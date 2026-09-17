# JSP-000854 submission references

This proof repository has been published. Its existing official submissions are
[Issue #141](https://github.com/TheJustinSunPrize/awards/issues/141) and
[PR #142](https://github.com/TheJustinSunPrize/awards/pull/142).

The official September 17, 2026 format uses an award-claim issue for the applicant
and a catalog-only PR for the proof references. The proof repository, named
branch, fixed commit, final theorem, reproduction instructions and attribution
remain publicly available here. The official PR carries catalog text and links.

- [Reproduction and theorem summary](README.md)
- [Statement correspondence](STATEMENT.md)
- [Mathematical proof](PROOF.md)
- [Contribution record](ATTRIBUTION.md)
- [Recorded verification scope](LEAN-STATUS.md)

The original scripts and templates under `submission/` are historical publication
helpers for the earlier candidate-record format. Do not run them to create another
submission; update the existing issue and PR using the
[current official requirements](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md).

Run `bash scripts/verify.sh` to reproduce the Lean build and final axiom audit.
The published source, pinned dependencies and original verification logs are
preserved. Attribution and submission-format updates do not change the proof.
