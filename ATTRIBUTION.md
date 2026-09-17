# Attribution and contribution record

## Mathematical result

Koishi Chan's published solution and subsequent discussion of
[Erdős problem 1027](https://www.erdosproblems.com/forum/thread/1027)
are the prior mathematical work for
[JSP-000854](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000854).
The prize contribution submitted by this project is Lean formalization.

## Formalization contributor

GitHub account: cronrpc

The formalization project was initiated, directed and integrated by cronrpc,
who is the applicant for its formalization contribution. The work comprises
the finite probability and counting development, complete theorem assembly,
statement correspondence, and reproducible build and axiom-audit package.
Development and internal checks used automated proof-development assistance
under the applicant's direction. This records a project contribution; it does
not describe every proof step as manually written or internal checks as
independent human review.

The proof route uses random partial colourings, finite union and first-moment
estimates, compatible representative choices, and a final colouring-count
identity. The mathematical exposition and its relation to the known solution
are described in [PROOF.md](PROOF.md) and [SOURCES.md](SOURCES.md).

Recipient placeholder: `RECIPIENT-JSP-000854-CRONRPC-A`.
Recipient confirmation remains with the prize maintainers.
The applicant's existing [claim](https://github.com/TheJustinSunPrize/awards/issues/141)
and [catalog correction](https://github.com/TheJustinSunPrize/awards/pull/142)
identify the same contribution.

## Scope and dependencies

The final declarations are `Erdos1027Main.erdos_1027` and
`Erdos1027Main.erdos_1027_subsets`. They prove the full qualitative statement;
the project also gives a quantitative estimate under explicit thresholds.
See [STATEMENT.md](STATEMENT.md) for the complete quantifiers and definitions.

The project uses Lean 4.19.0, Mathlib v4.19.0 and their pinned dependencies.
Their existing licenses and attributions remain applicable. Build instructions
are in [README.md](README.md), and the original verification records remain in
`verification/`. The audited final declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.
