# Erdős 1027 / JSP-000854 — complete Lean formalization

The full original qualitative statement is proved in Lean 4.19.0 with
Mathlib v4.19.0. Both final theorems compile and their transitive axiom
dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorryAx` or custom solution axiom.

This project makes no claim of first discovery, first formalization, or
prize eligibility. The original mathematical problem already has a public
proof by Koishi Chan; see `SOURCES.md`.

## Final result

For every real `c > 0`, there exist `delta > 0` and a natural threshold `N`
such that, for every finite vertex type `V`, every `n >= N`, and every
family `F` of at most `c * 2^n` sets of cardinality `n`, at least
`delta * 2^(card V)` subsets of `V` meet every member of `F` both inside
and outside the subset. No degree or intersection hypothesis is added.

- `Erdos1027Main.erdos_1027`: the red/blue colouring statement.
- `Erdos1027Main.erdos_1027_subsets`: the equivalent subset-count statement.
- `Erdos1027Main.count_lower_bound`: the quantitative bound
  `delta = 1 / (4 * 2^L)` under explicit numerical threshold hypotheses.

The witnesses `delta` and `N` are chosen before `V`, `n`, and `F`.
Taking `V` to be the union of the family gives the original formulation.

## Submission and attribution

Formalization contributor: cronrpc. See the
[contribution record](ATTRIBUTION.md) for the project role and prior mathematics.
The English proof is [PROOF.md](PROOF.md), with a clause-by-clause
[statement correspondence](STATEMENT.md).

The existing [award claim](https://github.com/TheJustinSunPrize/awards/issues/141)
and [catalog correction PR](https://github.com/TheJustinSunPrize/awards/pull/142)
are updated in place. See [START_HERE.md](START_HERE.md) for the current submission
format. Proof source and build artifacts remain in this independent repository.

## Reproduce

Install Lean with Elan, then run in this directory:

```sh
bash scripts/verify.sh
```

`lean-toolchain` pins Lean 4.19.0. The Lake configuration pins Mathlib to
commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0).
`lake-manifest.json` also locks Mathlib's transitive dependencies.
The verifier downloads dependencies and their compiled cache, builds the
project, and checks the final axiom reports. The GitHub Actions workflow
runs the same verifier and stores its actual logs.

## Files

| File | Purpose |
|---|---|
| `Erdos1027Probability.lean` | Finite product weights and exact event masses |
| `Erdos1027Completion.lean` | Compatible representatives and completion count |
| `Erdos1027Estimates.lean` | Real estimates and existence of numerical parameters |
| `Erdos1027Events.lean` | Union bound, Markov bound, three bad events |
| `Erdos1027Mixing.lean` | Uniform final colouring and weighted count |
| `Erdos1027Subsets.lean` | Bijection between proper colourings and splitting subsets |
| `Erdos1027Main.lean` | Complete theorem assembly |
| `Erdos1027Audit.lean` | Exact theorem types and transitive axiom audit |
| `PROOF.md` | English mathematical proof and explicit paper constants |
| `PROOF.zh.md` | Optional Chinese translation |
| `STATEMENT.md` | Clause-by-clause statement correspondence |
| `ATTRIBUTION.md` | Mathematical sources and formalization contributor roles |
| `LEAN-STATUS.md` | Verification scope and actual audit results |
| `verification/` | Recorded verification output |
| `CoreCompletion.lean` | Earlier standalone representative lemma; not needed by Main |
| `check_finite.py`, `finite-checks.json` | Optional exact finite sanity checks |

The paper's particular ceiling formulas and its decimal example are not
separate Lean corollaries. The complete qualitative original theorem and
the threshold-conditional quantitative bound are formally proved.
Python experiments are supplementary and are not used in the Lean proof.
