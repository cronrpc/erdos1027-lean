"""Offline regression checks. These tests never contact or write to GitHub."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("publish", Path(__file__).with_name("publish.py"))
publish = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publish)


def result(args=(), stdout="", stderr="", code=0):
    return subprocess.CompletedProcess(args, code, stdout, stderr)


class PublicationChecks(unittest.TestCase):
    def test_plan_has_no_commands_or_writes(self):
        with patch.object(publish.sys, "argv", ["publish.py"]), \
             patch.object(publish, "run") as run, patch.object(publish, "save") as save, \
             contextlib.redirect_stdout(io.StringIO()):
            publish.main()
        run.assert_not_called()
        save.assert_not_called()

    def test_commands_pin_github_host(self):
        with patch.dict(os.environ, {"GH_HOST": "enterprise.invalid"}), \
             patch.object(publish.subprocess, "run", return_value=result()) as child, \
             contextlib.redirect_stdout(io.StringIO()):
            publish.run(["gh", "api", "user"])
        self.assertEqual(child.call_args.kwargs["env"]["GH_HOST"], "github.com")

    def test_extra_staged_file_blocks_commit(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            subprocess.run(["git", "init", "-q", path], check=True)
            (path / "proof.lean").write_text("-- proof\n")
            (path / "extra.txt").write_text("must not be uploaded\n")
            subprocess.run(["git", "add", "."], cwd=path, check=True)
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(RuntimeError, "extra.txt"):
                publish.ensure_staged_scope(path, ["proof.lean"])

    def test_commit_with_extra_tree_entry_is_rejected(self):
        with patch.object(publish, "run", return_value=result(stdout="proof.lean\0extra.txt\0")):
            with self.assertRaisesRegex(RuntimeError, "exactly match"):
                publish.ensure_proof_tree("a" * 40, ["proof.lean"])

    def test_existing_issue_uses_direct_lookup_and_is_reused(self):
        commit = "a" * 40
        repo = "https://github.com/test-user/erdos1027-lean"
        issue = {"title": publish.ISSUE_TITLE, "body": repo + " " + commit,
                 "html_url": "https://github.com/TheJustinSunPrize/awards/issues/123"}
        state = {"issue_create_pending": True}
        with patch.object(publish, "gh_json", return_value=[[issue]]) as query, \
             patch.object(publish, "run") as run, patch.object(publish, "save"):
            self.assertEqual(publish.create_issue(state, repo, commit, "test-user"), issue["html_url"])
        self.assertEqual(query.call_args.args[0][0], "api")
        self.assertIn("--paginate", query.call_args.args[0])
        run.assert_not_called()

    def test_uncertain_issue_creation_does_not_retry(self):
        with patch.object(publish, "gh_json", return_value=[[]]), \
             patch.object(publish, "run") as run:
            with self.assertRaisesRegex(RuntimeError, "uncertain outcome"):
                publish.create_issue({"issue_create_pending": True}, "https://github.com/a/b", "a" * 40, "a")
        run.assert_not_called()

    def test_different_commit_issue_is_not_duplicated(self):
        issue = {"title": publish.ISSUE_TITLE, "body": "an older proof", "html_url": "https://github.com/a/b/issues/1"}
        with patch.object(publish, "gh_json", return_value=[[issue]]), \
             patch.object(publish, "run") as run:
            with self.assertRaisesRegex(RuntimeError, "different proof version"):
                publish.create_issue({}, "https://github.com/a/b", "a" * 40, "a")
        run.assert_not_called()

    def test_proof_push_uses_saved_commit_not_head(self):
        commit = "a" * 40
        state = {"proof_repo": "test-user/erdos1027-lean", "proof_commit": commit}
        calls = []
        def fake_run(args, *unused, **kwargs):
            calls.append(args)
            if args[:2] == ["gh", "api"]:
                return result(stdout=json.dumps({"private": False, "owner": {"login": "test-user"}}))
            if args[:3] == ["git", "remote", "get-url"]:
                return result(stdout="https://github.com/test-user/erdos1027-lean.git\n")
            return result()
        with patch.object(publish, "run", side_effect=fake_run), \
             patch.object(publish, "ensure_proof_tree"), patch.object(publish, "save"):
            publish.publish_proof(state, ["proof.lean"], "test-user", 1, "erdos1027-lean")
        pushes = [args for args in calls if args[:2] == ["git", "push"]]
        self.assertEqual(pushes, [["git", "push", "origin", commit + ":refs/heads/main"]])


if __name__ == "__main__":
    unittest.main()
