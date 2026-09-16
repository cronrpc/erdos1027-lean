# Publish the prepared English submission

The mathematical proof and the complete Lean theorem have been checked locally.
The English issue, candidate-record generator, and PR text are prepared.
**Nothing has been published to GitHub from this workspace.** A GitHub-hosted
CI run and organizer review have not occurred.

## What to do

Extract this archive into a fresh directory and open a terminal in the
`erdos1027` directory containing this file. You need Python 3.10 or later,
Git, and [GitHub CLI](https://cli.github.com/). Lean is not required on the
computer doing the upload; the supplied workflow checks it on GitHub.

If `gh` is not installed on Windows, install it using the official WinGet
package, then open a new terminal:

```powershell
winget install --id GitHub.cli --exact
```

Authenticate directly with GitHub in your browser, then publish:

```powershell
gh auth login --hostname github.com --git-protocol https --web --scopes workflow
python submission/publish.py --publish
```

The `workflow` scope permits pushing the included Actions workflow. The script
uses GitHub CLI's authentication and configures Git to use that credential
helper. It never asks you to paste a token into this project or a chat.
Use the GitHub account under which you intend to make the submission.

Running `python submission/publish.py` without `--publish` only prints the plan.

## What the publication command does

1. Checks the prepared release file hashes and obtains the authenticated account.
2. Creates the public repository `YOUR_ACCOUNT/erdos1027-lean`, commits only the
   release's listed files, and pushes the exact commit that later evidence links
   will reference. An existing empty public repository with this name is usable;
   a repository containing unrelated work is not overwritten.
3. Opens one English recipient-recommendation issue in
   `TheJustinSunPrize/awards`, using the exact proof commit, build logs,
   axiom audit, statement explanation, and attribution record.
4. Clones the current awards repository, generates an unsigned candidate, and
   runs its validation, link checks, JSON generation, consistency check, and
   tests in a separate Python virtual environment.
5. Creates or reuses your awards fork, pushes a new candidate branch, and opens
   one English PR linking the nomination issue.
6. Prints the proof, issue, and PR URLs. Send those URLs back for follow-up.

The source commit uses your authenticated GitHub handle and its public no-reply
address as Git author metadata. The award recipient remains an unconfirmed
`RECIPIENT-*` placeholder; the script does not assert a legal name or affiliation.

To use a different new proof repository name:

```powershell
python submission/publish.py --publish --repo-name erdos1027-lean-submission
```

Choose the name before the first publication attempt. This script is intended
for a fresh prepared archive, not for importing unrelated existing Git history.

## Prepared submission contents

- [English issue text](submission/ISSUE_BODY.md.in)
- [English PR text](submission/PR_BODY.md.in)
- [English proof](PROOF.md)
- [Statement correspondence](STATEMENT.md)
- [Prior work, contributor roles, and AI assistance](ATTRIBUTION.md)
- [Actual Lean verification status](LEAN-STATUS.md)
- [Recorded build](verification/lake-build.log) and [axiom audit](verification/axioms.log)

The issue identifies the work as Codex-assisted formalization under the
submitter's direction, retains Koishi Chan's prior mathematical solution credit,
and requests review and eligibility reassessment. It does not claim a new
solution of an open problem, first formalization, an exclusive reservation,
official acceptance, or payment.

## Why the candidate is unsigned

The awards repository's formal statement schema currently requires at least
two real curator signatories and published reviews of custom definitions.
The candidate therefore has status `under-verification`, while `decision`,
`verification.formal`, and `verification/record.yaml` remain null. The full
declarations and definitions are supplied as `verification/proposed-statement.md`.
Actual reviewers can later issue the official signed statement. No signature
or independent verification result is fabricated.

The candidate format was checked against awards commit
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`. The publication script validates again
against the checkout used for your actual PR. If upstream requirements have
changed, it stops before pushing the candidate branch.

## If a step stops

Keep the extracted folder. `.submission-state.json` records completed steps,
and `.submission-work/` holds the prepared bodies and validation outputs.
These local files are excluded from the proof release.

For an ordinary failure before a remote creation attempt, resolve the reported
problem and rerun the same command. The script reuses recorded results and checks
for an existing matching issue or PR. If a remote creation may have succeeded
but its outcome cannot be established, it stops instead of creating another
record. Share the error and any resulting URLs for recovery; do not repeatedly
delete the saved state and retry.

The script performs no force-push, deletion, PR merge, or change to repository
visibility. It does not bypass issue restrictions or authentication failures.

## Verification of the preparation

The Lean verification script passed locally with pinned dependency caches.
The candidate generator passed the upstream schema/link/data checks and all
22 upstream tests in an explicitly temporary fixture; no fixture was published.
Offline publisher checks cover fixed-host routing, exact-commit pushes, staged
file scope, existing-issue reuse, and ambiguous-creation handling. They do not
constitute an authenticated end-to-end GitHub publication test.

Official references:

- [Contribution rules](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md)
- [Candidate records](https://github.com/TheJustinSunPrize/awards/blob/main/docs/records.md)
- [GitHub CLI browser login](https://cli.github.com/manual/gh_auth_login)
- [GitHub CLI repository creation](https://cli.github.com/manual/gh_repo_create)
- [GitHub CLI issue creation](https://cli.github.com/manual/gh_issue_create)
- [GitHub CLI PR creation](https://cli.github.com/manual/gh_pr_create)
