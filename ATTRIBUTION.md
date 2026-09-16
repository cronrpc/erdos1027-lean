# Attribution and contribution record

This package concerns [Erdős problem 1027](https://www.erdosproblems.com/1027),
listed as
[JSP-000854](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000854).
It is a Lean formalization of a mathematical problem with a known solution.

## Existing mathematical work

Koishi Chan has a public mathematical solution and subsequent discussion
in the [problem's forum thread](https://www.erdosproblems.com/forum/thread/1027).
That prior solution must be acknowledged when describing this work.

The proof developed for this package uses random partial colourings,
finite union and first-moment estimates, compatible representative
choices, and a final colouring-count identity. The accompanying note
does not present itself as a transcription of Chan's proof. This
description of the route does not establish originality or priority:
we have not established that this argument, or an equivalent argument,
was previously unknown.

## Roles in this package

| Role | Recorded contribution |
|---|---|
| Known mathematical solution | Koishi Chan's public solution is prior work, cited above. |
| Submitter and coordinator | The requesting user initiated and directed this preparation. Their preferred public name and GitHub handle have not been confirmed and are not asserted in this package. |
| AI-assisted development | OpenAI Codex assisted with the mathematical reconstruction, Lean implementation, compilation fixes, documentation, and statement review. Multiple AI agents worked on bounded components and cross-checked interfaces and statements. |
| Formal verification | Lean 4.19.0 checked the proof terms using the pinned Mathlib v4.19.0 dependencies. Recorded build and axiom-audit output accompanies the package. |
| Independent human review | No independent human review of the complete argument or Lean implementation is recorded for this package. |

The eventual public submitter name and account should be supplied and
confirmed by the user before those identifiers are used in a GitHub
submission. No real name, affiliation, or contact detail is inferred here.

AI-agent cross-checks should be described as AI-assisted review, not as
independent human review or human peer review. Lean's kernel checks are
also distinct from a human assessment that the formal statement matches
the intended problem; [STATEMENT.md](STATEMENT.md) makes that
correspondence explicit for reviewers.

## Scope of the contribution claim

The contribution prepared here is a complete formal proof of the original
qualitative finite-set statement, together with a quantitative theorem
under explicit numerical threshold hypotheses. Its checked declarations
are `Erdos1027Main.erdos_1027` and
`Erdos1027Main.erdos_1027_subsets`; the latter directly counts splitting
subsets.

The package makes no claim of:

- discovering the first mathematical solution;
- establishing a new or original proof method;
- being the first complete Lean formalization;
- priority over work not found during the source search;
- acceptance, prize eligibility, or an entitlement to payment.

The mathematical problem's prior solution and the limited scope of any
search for existing formalizations must remain visible in a submission.
See [SOURCES.md](SOURCES.md) for the sources checked. Its search results
are not an exhaustive proof that no earlier formalization exists.

## Dependencies and verification record

The package uses [Lean](https://github.com/leanprover/lean4),
[Mathlib](https://github.com/leanprover-community/mathlib4), and their pinned
dependencies, whose work is essential to the formalization. Version pins
and reproducibility instructions are in [README.md](README.md).

The actual verification record reports only Lean's standard foundational
axioms `propext`, `Classical.choice`, and `Quot.sound` for the final results.
It contains no `sorryAx` or custom axiom assuming the desired solution.
This verification supports the formal proof claim; it does not establish
novelty, authorship priority, prize eligibility, or independent human
review.

The current sources do not import or rely on an external custom axiom
asserting the solution of Erdős 1027. The source audit records the external
material inspected and distinguishes assumed solutions from completed
formal proofs. Optional finite Python checks are supplementary and are
not premises of the Lean theorems.
