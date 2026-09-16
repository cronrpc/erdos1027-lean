#!/usr/bin/env python3
"""Publish the prepared submission using the user's locally authenticated gh CLI.

Without --publish this only describes the plan. No token is read or requested.
The first successful run publishes a proof repository, nomination issue, and
candidate PR. Saved state supports resuming without force-pushing or deleting.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / ".submission-work"
STATE_FILE = ROOT / ".submission-state.json"
UPSTREAM = "TheJustinSunPrize/awards"
ISSUE_TITLE = "[Recipient] JSP-000854 / Erdos 1027: complete Lean formalization and eligibility review"
PR_TITLE = "JSP-000854: submit complete Lean formalization for candidate review"


def run(args, cwd=ROOT, *, check=True):
    args = [str(a) for a in args]
    print("+ " + subprocess.list2cmdline(args), flush=True)
    env = os.environ.copy()
    env["GH_HOST"] = "github.com"
    result = subprocess.run(args, cwd=cwd, env=env, text=True, encoding="utf-8",
                            errors="replace", stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    if result.returncode and check:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or
                           f"Command failed with exit code {result.returncode}")
    return result


def gh_json(args, cwd=ROOT):
    return json.loads(run(["gh", *args], cwd=cwd).stdout)


def save(state):
    tmp = STATE_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")
    tmp.replace(STATE_FILE)


def check_release():
    manifest = ROOT / "RELEASE_FILES.txt"
    if not manifest.is_file():
        raise RuntimeError("RELEASE_FILES.txt is missing. Use the complete prepared archive.")
    files = manifest.read_text(encoding="utf-8").splitlines()
    for name in files:
        p = Path(name)
        if not name or p.is_absolute() or ".." in p.parts or not (ROOT / p).is_file():
            raise RuntimeError(f"Invalid or missing release file: {name!r}")
    for line in (ROOT / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
        digest, name = line.split("  ", 1)
        if name not in files:
            raise RuntimeError(f"Checksum path is outside the release: {name}")
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest:
            raise RuntimeError(f"Prepared file changed: {name}. Review and rebuild the release before publishing.")
    return files


def configure_author(path, login, user_id):
    # Only this new checkout is configured; use the authenticated account's
    # public handle and GitHub's no-reply address, not a private email address.
    run(["git", "config", "user.name", login], path)
    run(["git", "config", "user.email", f"{user_id}+{login}@users.noreply.github.com"], path)


def ensure_staged_scope(path, allowed):
    staged = set(filter(None, run(["git", "diff", "--cached", "--name-only", "-z"], path).stdout.split("\0")))
    extra = staged - set(allowed)
    if extra:
        raise RuntimeError("Other files are already staged and will not be published: " + ", ".join(sorted(extra)))


def ensure_proof_tree(commit, files):
    tracked = set(filter(None, run(["git", "ls-tree", "-r", "--name-only", "-z", commit]).stdout.split("\0")))
    if tracked != set(files):
        raise RuntimeError("The proof commit tree does not exactly match the prepared release whitelist.")
    run(["git", "diff", "--exit-code", commit, "--", *files])


def publish_proof(state, files, login, user_id, repo_name):
    slug = f"{login}/{repo_name}"
    if state.get("proof_repo") not in (None, slug):
        raise RuntimeError("Saved state belongs to a different proof repository.")
    if not state.get("proof_commit"):
        if (ROOT / ".git").exists() and not (state.get("initialized") or state.get("initializing")):
            raise RuntimeError("This directory already has Git history. Extract the archive to a fresh directory.")
        if not state.get("initialized"):
            state.update(initializing=True, proof_repo=slug)
            save(state)
            if not (ROOT / ".git").exists():
                run(["git", "init", "-b", "main"])
            state.update(initialized=True, proof_repo=slug)
            save(state)
        configure_author(ROOT, login, user_id)
        # A whitelist prevents incidental local files from being published.
        run(["git", "add", "--", *files])
        ensure_staged_scope(ROOT, files)
        head = run(["git", "rev-parse", "--verify", "HEAD"], check=False)
        if head.returncode:
            run(["git", "commit", "-m", "Add complete Codex-assisted Lean formalization of Erdos 1027"])
        elif run(["git", "diff", "--cached", "--quiet"], check=False).returncode:
            raise RuntimeError("An initial commit already exists but prepared files changed. Review locally before retrying.")
        state["proof_commit"] = run(["git", "rev-parse", "HEAD"]).stdout.strip()
        save(state)
    ensure_proof_tree(state["proof_commit"], files)
    if not state.get("proof_pushed"):
        result = run(["gh", "api", f"repos/{slug}"], check=False)
        if result.returncode:
            if "404" not in result.stderr:
                raise RuntimeError(result.stderr.strip())
            run(["gh", "repo", "create", slug, "--public", "--description",
                 "Complete Lean formalization of Erdos 1027 / JSP-000854; submitted for review"])
        else:
            repo = json.loads(result.stdout)
            if repo.get("private") or repo.get("owner", {}).get("login", "").lower() != login.lower():
                raise RuntimeError("The target must be a public repository owned by the authenticated account.")
            remote = run(["git", "ls-remote", f"https://github.com/{slug}.git"]).stdout.strip()
            expected = state["proof_commit"]
            if remote and not any(line.split() == [expected, "refs/heads/main"] for line in remote.splitlines()):
                raise RuntimeError("The target repository already contains other work. Choose another --repo-name.")
        remote_url = f"https://github.com/{slug}.git"
        origin = run(["git", "remote", "get-url", "origin"], check=False)
        if origin.returncode:
            run(["git", "remote", "add", "origin", remote_url])
        elif origin.stdout.strip() != remote_url:
            raise RuntimeError("Unexpected origin remote; it will not be replaced.")
        run(["git", "push", "origin", f"{state['proof_commit']}:refs/heads/main"])
        state["proof_pushed"] = True
        save(state)
    return f"https://github.com/{slug}", state["proof_commit"]


def render_issue(repo, commit, login):
    text = (ROOT / "submission/ISSUE_BODY.md.in").read_text(encoding="utf-8")
    text = text.replace("{{PROOF_REPO}}", repo).replace("{{PROOF_COMMIT}}", commit)
    text = text.replace("RECIPIENT-JSP-000854-A", f"RECIPIENT-JSP-000854-{login.upper()}-A")
    if "{{" in text:
        raise RuntimeError("Unresolved issue placeholder.")
    out = WORK / "issue-body.md"
    out.write_text(text, encoding="utf-8")
    return out


def create_issue(state, repo, commit, login):
    if state.get("issue_url"):
        return state["issue_url"]
    pages = gh_json(["api", "--method", "GET", f"repos/{UPSTREAM}/issues",
                     "-f", f"creator={login}", "-f", "state=all", "-f", "per_page=100",
                     "--paginate", "--slurp"])
    existing = [item for page in pages for item in page]
    matches = [x for x in existing if "pull_request" not in x and x["title"] == ISSUE_TITLE]
    if matches:
        if len(matches) != 1 or commit not in matches[0].get("body", "") or repo not in matches[0].get("body", ""):
            raise RuntimeError("An existing nomination uses this title but a different proof version. Review it before creating another.")
        state["issue_url"] = matches[0]["html_url"]
    else:
        if state.get("issue_create_pending"):
            raise RuntimeError("A previous issue-creation attempt has an uncertain outcome. "
                               "Check GitHub before retrying; this script will not create a possible duplicate.")
        body = render_issue(repo, commit, login)
        state["issue_create_pending"] = True
        save(state)
        result = run(["gh", "issue", "create", "--repo", UPSTREAM,
                      "--title", ISSUE_TITLE, "--body-file", body], check=False)
        if result.returncode:
            raise RuntimeError("The proof repository is published, but issue creation failed. "
                               "No alternate posting route was attempted. " + result.stderr.strip() +
                               f"\nThe prepared issue is at {body}. Rerun after resolving access.")
        state["issue_url"] = result.stdout.strip().splitlines()[-1]
    save(state)
    return state["issue_url"]


def prepare_and_publish_pr(state, repo, commit, login, user_id, issue_url):
    if state.get("pr_url"):
        return state["pr_url"]
    checkout = WORK / "awards"
    if not checkout.exists():
        run(["git", "clone", f"https://github.com/{UPSTREAM}.git", checkout])
    configure_author(checkout, login, user_id)
    if not state.get("candidate_base"):
        if run(["git", "remote", "get-url", "origin"], checkout).stdout.strip() != f"https://github.com/{UPSTREAM}.git":
            raise RuntimeError("Unexpected candidate checkout origin.")
        state["candidate_base"] = run(["git", "rev-parse", "HEAD"], checkout).stdout.strip()
        save(state)
    if not state.get("candidate_branch"):
        state["candidate_branch"] = f"candidate/jsp-000854-{commit[:12]}"
        save(state)
    branch = state["candidate_branch"]
    if run(["git", "branch", "--show-current"], checkout).stdout.strip() != branch:
        exists = run(["git", "show-ref", "--verify", f"refs/heads/{branch}"], checkout, check=False)
        run(["git", "checkout", branch] if not exists.returncode else
            ["git", "checkout", "-b", branch, state["candidate_base"]], checkout)
    if not state.get("candidate_prepared"):
        generated = run([sys.executable, ROOT / "submission/prepare_candidate.py",
             "--awards-dir", checkout, "--proof-repo", repo, "--proof-commit", commit,
             "--submitter", login, "--issue-url", issue_url])
        prepared = json.loads(generated.stdout)
        stable_body = WORK / "pr-body.md"
        shutil.copyfile(prepared["pr_body_path"], stable_body)
        prepared["pr_body_path"] = str(stable_body)
        prepared["hashes"] = {name: hashlib.sha256((checkout / name).read_bytes()).hexdigest()
                              for name in prepared["relative_files"]}
        state["candidate_prepared"] = prepared
        save(state)
    prepared = state["candidate_prepared"]
    for name, digest in prepared["hashes"].items():
        if hashlib.sha256((checkout / name).read_bytes()).hexdigest() != digest:
            raise RuntimeError("Generated candidate file changed; review before publishing: " + name)
    env_dir = WORK / "validator-venv"
    python = env_dir / ("Scripts/python.exe" if os.name == "nt" else "bin/python")
    if not python.exists():
        run([sys.executable, "-m", "venv", env_dir])
    run([python, "-m", "pip", "install", "-r", checkout / "requirements.txt"])
    for command in ("validate", "links", "build", "check"):
        result = run([python, "scripts/manage.py", command], checkout)
        (WORK / f"records-{command}.log").write_text(result.stdout + result.stderr, encoding="utf-8")
    result = run([python, "-m", "unittest", "discover", "-s", "tests", "-v"], checkout)
    (WORK / "records-tests.log").write_text(result.stdout + result.stderr, encoding="utf-8")
    entry_id = prepared["entry_id"]
    candidate = f"candidates/verified-pending/{entry_id}"
    allowed = prepared["relative_files"] + prepared["generated_data_files"]
    run(["git", "add", "--", *allowed], checkout)
    ensure_staged_scope(checkout, allowed)
    if run(["git", "diff", "--cached", "--quiet"], checkout, check=False).returncode:
        run(["git", "commit", "-m", "Add JSP-000854 formalization candidate pending review"], checkout)
    changed = set(filter(None, run(["git", "diff", "--name-only", "-z",
                                    state["candidate_base"], "HEAD"], checkout).stdout.split("\0")))
    if changed - set(allowed):
        raise RuntimeError("The candidate branch contains unrelated changes; it will not be pushed.")
    fork_slug = f"{login}/awards"
    fork_check = run(["gh", "api", f"repos/{fork_slug}"], check=False)
    if fork_check.returncode:
        if "404" not in fork_check.stderr:
            raise RuntimeError(fork_check.stderr.strip())
        run(["gh", "repo", "fork", UPSTREAM, "--clone=false", "--remote=false"], checkout)
    else:
        fork = json.loads(fork_check.stdout)
        if not fork.get("fork") or fork.get("parent", {}).get("full_name", "").lower() != UPSTREAM.lower():
            raise RuntimeError(f"{fork_slug} exists but is not the expected awards fork.")
    run(["git", "push", f"https://github.com/{fork_slug}.git", f"HEAD:refs/heads/{branch}"], checkout)
    prs = gh_json(["api", "--method", "GET", f"repos/{UPSTREAM}/pulls",
                   "-f", f"head={login}:{branch}", "-f", "state=all",
                   "-f", "per_page=100"], checkout)
    if prs:
        if len(prs) != 1:
            raise RuntimeError("More than one PR matches the saved branch.")
        state["pr_url"] = prs[0]["html_url"]
    else:
        if state.get("pr_create_pending"):
            raise RuntimeError("A previous PR-creation attempt has an uncertain outcome. Check GitHub before retrying.")
        # prepare_candidate.py supplies a reviewable English PR body.
        pr_body = Path(prepared["pr_body_path"])
        if not pr_body.is_file():
            raise RuntimeError(f"Prepared PR body not found: {pr_body}")
        state["pr_create_pending"] = True
        save(state)
        state["pr_url"] = run(["gh", "pr", "create", "--repo", UPSTREAM,
                               "--head", f"{login}:{branch}", "--base", "main",
                               "--title", PR_TITLE, "--body-file", pr_body], checkout).stdout.strip().splitlines()[-1]
    save(state)
    return state["pr_url"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--publish", action="store_true", help="Create the public proof repository, nomination issue, and candidate PR.")
    parser.add_argument("--repo-name", default="erdos1027-lean", help="New public repository name under your authenticated personal account.")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,99}", args.repo_name):
        parser.error("Invalid repository name.")
    print("This publishes: a public proof repository, one English nomination issue,\n"
          "and one English candidate PR to TheJustinSunPrize/awards.\n"
          "It requests review; it does not reserve the problem or announce an award.\n")
    if not args.publish:
        print("No network calls or changes made. To proceed after reviewing the package:\n"
              "  gh auth login --hostname github.com --git-protocol https --web --scopes workflow\n"
              "  python submission/publish.py --publish\n")
        return
    files = check_release()
    for tool in ("git", "gh"):
        if not shutil.which(tool):
            raise RuntimeError(f"{tool} is not installed. See START_HERE.md.")
    run(["gh", "auth", "status", "--hostname", "github.com"])
    user = gh_json(["api", "user"])
    login, user_id = user["login"], user["id"]
    state = json.loads(STATE_FILE.read_text(encoding="utf-8")) if STATE_FILE.exists() else {}
    if state.get("login") not in (None, login):
        raise RuntimeError("Saved publication state belongs to another GitHub account.")
    state["login"] = login
    save(state)
    WORK.mkdir(exist_ok=True)
    run(["gh", "auth", "setup-git", "--hostname", "github.com"])
    repo, commit = publish_proof(state, files, login, user_id, args.repo_name)
    issue = create_issue(state, repo, commit, login)
    pr = prepare_and_publish_pr(state, repo, commit, login, user_id, issue)
    print(f"\nProof: {repo}/tree/{commit}\nIssue: {issue}\nPR: {pr}\n"
          "Publication completed. Organizer review and any hosted CI result remain separate.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError) as exc:
        print(f"Stopped: {exc}", file=sys.stderr)
        print("Completed steps are retained in .submission-state.json; no force-push or deletion was attempted.", file=sys.stderr)
        sys.exit(1)
