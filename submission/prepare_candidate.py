#!/usr/bin/env python3
"""Prepare an unsigned JSP-000854 candidate without publishing anything.

Python 3.10+. Only the standard library is needed to generate the files. The
upstream awards requirements are needed for the separately reported checks.
The .yaml files contain JSON, a strict subset of the YAML accepted upstream.

The current awards statement schema requires two real curator signatories.
Without those attestations this generator writes a proposed-statement.md and
leaves formal evidence and its review record null; it never fabricates a
signed statement, review result, recipient identity, or announced decision.

This program checks URL syntax, not public accessibility or commit existence.
The caller must publish and verify the actual pinned proof source before
submitting these files. Synthetic fixtures belong in temporary test copies.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path
from urllib.parse import urlsplit


PROJECT_ROOT = Path(__file__).resolve().parents[1]
UPSTREAM_REPO = "https://github.com/TheJustinSunPrize/awards"
TESTED_AWARDS_COMMIT = "f4e7173d89dfe91022a185427d63452c8ffbf6ae"
PROBLEM_URL = "https://www.erdosproblems.com/1027"
EXISTING_PROOF_URL = "https://www.erdosproblems.com/forum/thread/1027"
CATALOG_PATH = "problems/catalog-0801-0900.md#JSP-000854"


def _login(value: str) -> str:
    if not re.fullmatch(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?", value):
        raise ValueError("submitter must be a GitHub login (1-39 letters, digits, or hyphens)")
    if "--" in value:
        raise ValueError("submitter must not contain consecutive hyphens")
    return value.lower()


def _proof_repository(value: str) -> str:
    parsed = urlsplit(value)
    if parsed.scheme != "https" or parsed.netloc.lower() != "github.com":
        raise ValueError("proof-repo must have the form https://github.com/OWNER/REPO")
    if parsed.query or parsed.fragment or any(ch.isspace() for ch in value):
        raise ValueError("proof-repo must not contain queries, fragments, or whitespace")
    parts = parsed.path.strip("/").split("/")
    if len(parts) != 2:
        raise ValueError("proof-repo must point to a repository, not a branch or file")
    owner, repository = parts
    _login(owner)
    if repository.endswith(".git"):
        repository = repository[:-4]
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", repository) or repository in (".", ".."):
        raise ValueError("invalid GitHub repository name")
    if owner == "OWNER" or repository == "REPO":
        raise ValueError("replace the example OWNER and REPO with the actual proof repository")
    return f"https://github.com/{owner}/{repository}"


def _https_url(value: str) -> str:
    parsed = urlsplit(value)
    if (parsed.scheme != "https" or not parsed.hostname or parsed.username
            or parsed.password or any(ch.isspace() for ch in value)):
        raise ValueError("issue-url must be an HTTPS URL without credentials or whitespace")
    return value


def _theorem_signature(path: Path, name: str) -> str:
    source = path.read_text(encoding="utf-8")
    found = re.search(rf"(?m)^theorem {re.escape(name)}\b", source)
    if not found:
        raise ValueError(f"missing theorem {name} in {path.name}")
    signature, separator, _ = source[found.start():].partition(":= by")
    if not separator:
        raise ValueError(f"cannot extract the declaration of {name}")
    return signature.rstrip()


def _definition(path: Path, name: str) -> str:
    source = path.read_text(encoding="utf-8")
    found = re.search(rf"(?m)^def {re.escape(name)}\b", source)
    if not found:
        raise ValueError(f"missing definition {name} in {path.name}")
    return source[found.start():].split("\n\n", 1)[0].rstrip()


def _project_metadata() -> dict:
    manifest = json.loads((PROJECT_ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = [package for package in manifest["packages"] if package["name"] == "mathlib"]
    if len(packages) != 1 or not re.fullmatch(r"[0-9a-f]{40}", packages[0]["rev"]):
        raise ValueError("the bundled project must pin one immutable mathlib commit")
    return {
        "toolchain": (PROJECT_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "mathlib_commit": packages[0]["rev"],
        "proper": _definition(PROJECT_ROOT / "Erdos1027Completion.lean", "Proper"),
        "splits": _definition(PROJECT_ROOT / "Erdos1027Subsets.lean", "Splits"),
        "coloring_theorem": _theorem_signature(PROJECT_ROOT / "Erdos1027Main.lean", "erdos_1027"),
        "subset_theorem": _theorem_signature(PROJECT_ROOT / "Erdos1027Main.lean", "erdos_1027_subsets"),
    }


def _candidate_files(entry_id: str, proof_repo: str, proof_commit: str,
                     submitter: str, issue_url: str | None) -> dict[str, str]:
    metadata = _project_metadata()
    source = f"{proof_repo}/tree/{proof_commit}"
    blob = f"{proof_repo}/blob/{proof_commit}"
    catalog = f"{UPSTREAM_REPO}/blob/{TESTED_AWARDS_COMMIT}/{CATALOG_PATH}"
    recipient = f"RECIPIENT-{entry_id.upper()}-A"
    issue_text = f"[Related issue]({issue_url})" if issue_url else "No related public issue has been supplied."
    award = {
        "id": entry_id,
        "batch": None,
        "problem": {
            "source": "erdosproblems.com",
            "number": 1027,
            "title_en": "Erdos problem 1027 / JSP-000854: a positive proportion of splitting subsets",
            "posed": {
                "year": 1964,
                "basis": "earliest-reference",
                "citation": (
                    "The prize catalogue records 'No later than 1964 (bibliographic evidence)': "
                    f"{catalog}. This is a bibliographic upper bound, not an asserted exact first-posed date."
                ),
            },
            "resolved": None,
        },
        "decision": None,
        "recipients": [{
            "id": recipient,
            "affiliation": "",
            "contribution_en": (
                "Proposed contribution: AI-assisted Lean 4 formalization of the complete "
                "Erdos 1027 counting theorem via random partial colorings. Contribution "
                "attribution and recipient identity await confirmation; no priority or award is asserted."
            ),
            "confirmation": None,
        }],
        "verification": {"peer_review": None, "formal": None, "independent_review": None},
        "conflicts": [],
        "status": "under-verification",
        "revocation": None,
    }
    citation = f"""# Candidate review: JSP-000854 / Erdos problem 1027

## English

This is an **under-verification candidate**, not an award or a completed independent verification record. The `verified-pending` pool is the repository's location convention; its name does not establish successful verification.

The proposed contribution is an AI-assisted Lean 4 formalization of the full positive-proportion theorem. For each real c > 0 there are delta > 0 and N, depending only on c, such that for every finite vertex type V, every natural n >= N, and every family F of n-element subsets of V with at most c * 2^n members, at least delta * 2^|V| subsets B of V have both A intersect B nonempty and A minus B nonempty for every A in F. No degree or intersection restriction is imposed. An equivalent Boolean-coloring theorem is included.

The original problem is [Erdos 1027]({PROBLEM_URL}); the corresponding prize entry is [JSP-000854]({catalog}). The existing mathematical solution by Koishi Chan is credited in the [public discussion]({EXISTING_PROOF_URL}). This candidate concerns formalization and does not claim to solve a previously unsolved problem. The reconstructed partial-coloring argument is not asserted to be novel, and formalization priority has not been established. The mathematical resolution year remains null pending an appropriate reviewed dated source; this does not dispute the catalogue's solved status.

The immutable proof source is [{proof_commit}]({source}). Review [the complete theorem declarations]({blob}/Erdos1027Main.lean), [the proof route]({blob}/PROOF.md), [dependency pins]({blob}/lake-manifest.json), and [the repository instructions]({blob}/README.md). The project specifies `{metadata['toolchain']}` and mathlib commit `{metadata['mathlib_commit']}`. These versions are reported exactly, without asserting that they satisfy any current minimum safe-version policy.

The bundled local [build log]({blob}/verification/lake-build.log) and [axiom-audit log]({blob}/verification/axioms.log) are submitter-provided evidence. They are not a completed independent review or evidence of two independent checker implementations. Reviewers must fetch the pinned source, reproduce the build, compare the theorem to the original question, and inspect the actual axiom dependencies.

The [unsigned proposed statement](verification/proposed-statement.md) records every quantifier and the relevant definitions. `verification.formal` and [the verification record](verification/record.yaml) are null. The current upstream schema requires at least two real curator signatories before an active `statement.yaml` can be supplied. No signatures, profile confirmations, independent checkers, sandbox guarantees, or organizer conclusions have been invented.

Submitter account: @{submitter}. This identifies the submitting account, not a confirmed recipient. The submitter is involved in this recommendation; the submission is not an independent endorsement. No additional professional relationship or conflict is asserted; further disclosures remain subject to review. {issue_text}
"""
    recipients = f"""# Candidate attribution

## English

`{recipient}` is the sole unconfirmed recipient placeholder. It does not identify a person or establish eligibility, a share of an award, or a payment claim. No recipient name, affiliation, confirmation, private contact information, or payment information is included.

The proposed contribution is an AI-assisted Lean 4 formalization and a finite-probability proof of the complete statement of Erdos problem 1027. Attribution is to be reviewed against [the immutable source]({source}) and its contribution history before any recipient identity is associated with this record.

The pre-existing mathematical solution is credited to Koishi Chan in the [original public discussion]({EXISTING_PROOF_URL}). That scholarly credit is not a nomination of the prior solver as a recipient of this submission. Neither the argument's novelty nor first-formalization priority is asserted.

The submitting account @{submitter} is not treated as a confirmed recipient. A recipient identity may replace the placeholder only after the confirmation and authorized public-profile requirements of this repository are met. Independent verification and attribution review remain pending.
"""
    statement = f"""# Unsigned proposed formal statement

## English

This is a **submitter-supplied, unsigned proposal for review**, not an issued `statement.yaml`. It records no public curator signatures or completed definition reviews. The declarations below are extracted from the source bundled with this generator; an independent reviewer must compare them to [the supplied immutable proof commit]({source}) and to [the original question]({PROBLEM_URL}). The generator validates URL syntax, not remote availability or agreement between its local tree and the supplied commit.

### Scope and quantifier order

For every real c > 0, there exist a real delta > 0 and a natural number N, depending only on c. For **every** finite vertex type V with decidable equality, every natural n >= N, and every finite family F of finite subsets of V, if all members of F have cardinality n and |F| <= c * 2^n, then the number of subsets B of V splitting every A in F is at least delta * 2^|V|. The order is: for every c, there exist delta and N, then for every V, n, and F. There is no regularity, degree, distinct-intersection, nonempty-family, or fixed-vertex-count hypothesis.

The family is a `Finset (Finset V)`, so duplicate edges are not counted multiple times. `Fintype V` supplies finite enumeration; `DecidableEq V` is the equality interface used by finite sets. `Nat.card` is the cardinality of the displayed subtype. Inequalities, delta, c, and the counting bound are in the reals, with the indicated natural-cardinality casts. Choosing V to be the finite union of the edges gives the original ground-set formulation; the theorem allows an arbitrary finite ambient V, including unused vertices.

### Custom definitions to be reviewed

These are exact local source transcriptions, with fully qualified names stated below. They are **not** marked as independently reviewed definitions.

`Erdos1027.Proper`, from [Erdos1027Completion.lean]({blob}/Erdos1027Completion.lean), means that every edge contains each of the two Boolean colors:

```lean
{metadata['proper']}
```

`Erdos1027Subsets.Splits`, from [Erdos1027Subsets.lean]({blob}/Erdos1027Subsets.lean), means that each edge meets both the selected set and its complement within the edge. In its source namespace the parameters have `{{V : Type*}} [Fintype V] [DecidableEq V]`:

```lean
{metadata['splits']}
```

The same source proves an equivalence of proper colorings and splitting subsets, with matching cardinalities. Independent statement comparison must review this correspondence as well as the top-level premises.

### Complete Boolean-coloring declaration

Fully qualified theorem: `Erdos1027Main.erdos_1027` in [Erdos1027Main.lean]({blob}/Erdos1027Main.lean).

```lean
{metadata['coloring_theorem']}
```

### Complete splitting-subset declaration

Fully qualified theorem: `Erdos1027Main.erdos_1027_subsets` in [Erdos1027Main.lean]({blob}/Erdos1027Main.lean).

```lean
{metadata['subset_theorem']}
```

### Pins and outstanding review

Proof repository: [{proof_repo}]({proof_repo}). Proof commit: `{proof_commit}`. Toolchain: `{metadata['toolchain']}`. Library: mathlib commit [`{metadata['mathlib_commit']}`](https://github.com/leanprover-community/mathlib4/tree/{metadata['mathlib_commit']}); transitive dependencies are pinned in [lake-manifest.json]({blob}/lake-manifest.json).

No claim is made that the toolchain or library meets any current minimum safe-version policy. No curator has signed this proposal, no independent verifier is named, no checker conclusion or isolated-build environment is attested, and no award decision or recipient confirmation is recorded. The current upstream [statement schema]({UPSTREAM_REPO}/blob/{TESTED_AWARDS_COMMIT}/data/schema/statement.schema.json) requires at least two signatories; the record guide also requires published reviews for custom definitions. Those requirements must be fulfilled by actual authorized reviewers, after which maintainers may issue an active `statement.yaml` and enable the structured formal reference. Until then `verification.formal` and `verification/record.yaml` remain null.
"""
    return {
        "award.yaml": json.dumps(award, ensure_ascii=False, indent=2) + "\n",
        "citation.md": citation,
        "recipients.md": recipients,
        "verification/record.yaml": "null\n",
        "verification/proposed-statement.md": statement,
    }


def build_candidate(awards_dir: Path, proof_repo: str, proof_commit: str,
                    submitter: str, issue_url: str | None = None) -> dict:
    """Write one new candidate; refuse overwrites and return publishing inputs.

    The caller runs the official commands returned in ``check_commands`` and
    includes the regenerated JSON in the eventual PR. This function neither
    contacts GitHub nor commits, pushes, creates issues, or opens a PR.
    """
    awards_dir = Path(awards_dir).expanduser().resolve(strict=True)
    proof_repo = _proof_repository(proof_repo)
    if not re.fullmatch(r"[0-9a-fA-F]{40}", proof_commit) or set(proof_commit) == {"0"}:
        raise ValueError("proof-commit must be a nonzero, full 40-hex-character Git commit")
    proof_commit = proof_commit.lower()
    login = _login(submitter)
    issue_url = _https_url(issue_url) if issue_url else None
    for required in ("scripts/manage.py", "data/schema/award.schema.json",
                     "data/schema/statement.schema.json", "docs/records.md"):
        if not (awards_dir / required).is_file():
            raise ValueError(f"not an awards checkout: missing {required}")
    pool = awards_dir / "candidates/verified-pending"
    if not pool.is_dir() or pool.is_symlink() or (awards_dir / "candidates").is_symlink():
        raise ValueError("awards checkout must have a real candidates/verified-pending directory")
    entry_id = f"jsp-000854-{login}"
    candidate_dir = pool / entry_id
    for managed in (awards_dir / "awards", awards_dir / "candidates"):
        if any(path.parent.name == entry_id for path in managed.rglob("award.yaml")):
            raise ValueError(f"entry {entry_id} already exists; never overwrite a published statement")
    if candidate_dir.exists() or candidate_dir.is_symlink():
        raise ValueError(f"refusing to overwrite {candidate_dir}")
    files = _candidate_files(entry_id, proof_repo, proof_commit, login, issue_url)
    template = Path(__file__).with_name("PR_BODY.md.in").read_text(encoding="utf-8")
    replacements = {
        "{{PROOF_REPO}}": proof_repo,
        "{{PROOF_COMMIT}}": proof_commit,
        "{{ISSUE_URL}}": f"[public issue]({issue_url})" if issue_url else "Not supplied; check for related issues before submitting.",
        "{{ENTRY_ID}}": entry_id,
    }
    for key, value in replacements.items():
        template = template.replace(key, value)
    if re.search(r"\{\{[A-Z_]+\}\}", template):
        raise ValueError("unexpanded PR body template placeholder")
    # Prepare all text before creating anything; mkdir and write mode 'x'
    # ensure that an existing record is never silently replaced.
    candidate_dir.mkdir()
    (candidate_dir / "verification").mkdir()
    for relative, content in files.items():
        with (candidate_dir / relative).open("x", encoding="utf-8", newline="\n") as stream:
            stream.write(content)
    draft_dir = Path(tempfile.mkdtemp(prefix=f"{entry_id}-pr-"))
    pr_body_path = draft_dir / "PR_BODY.md"
    pr_body_path.write_text(template, encoding="utf-8")
    relative_files = [(candidate_dir / relative).relative_to(awards_dir).as_posix() for relative in files]
    return {
        "entry_id": entry_id,
        "candidate_dir": str(candidate_dir),
        "pr_body_path": str(pr_body_path),
        "relative_files": sorted(relative_files),
        "generated_data_files": ["data/awards.json", "data/candidates.json"],
        "proof_source_url": f"{proof_repo}/tree/{proof_commit}",
        "unsigned_statement": True,
        "check_commands": [
            ["python", "scripts/manage.py", command] for command in ("validate", "links", "build", "check")
        ] + [["python", "-m", "unittest", "discover", "-s", "tests", "-v"]],
        "notice": "Unsigned candidate only; run official checks and review the actual pinned public source before submitting.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--awards-dir", required=True, type=Path)
    parser.add_argument("--proof-repo", required=True)
    parser.add_argument("--proof-commit", required=True)
    parser.add_argument("--submitter", required=True)
    parser.add_argument("--issue-url")
    args = parser.parse_args()
    try:
        result = build_candidate(args.awards_dir, args.proof_repo, args.proof_commit,
                                 args.submitter, args.issue_url)
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as error:
        print(f"prepare_candidate: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
