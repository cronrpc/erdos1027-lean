# Actual Lean verification status

Checked on 2026-09-16.

- Lean: 4.19.0, commit `6caaee842e94`.
- Mathlib: v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Every module on the complete theorem's dependency path compiled successfully.
- Both complete final theorems passed the transitive axiom audit.
- The complete Lake project built successfully (exit code 0).

The published sources are also checked as one Lake project using local
package overrides pointing to the pinned dependency cache. This changes
only dependency locations, not source code or theorem statements. The
release configuration and manifest use the standard pinned Git dependencies.
See `verification/lake-build.log` for the recorded build output.

## Scope

The finite probability space, exact one-edge and two-edge event masses,
union and Markov inequalities, completion count, real-number bounds,
uniform final-colouring identity, positive parameter existence, and
colouring/subset bijection are connected into the complete original theorem.

The statement quantifies over **every positive real c**. The proportion and
threshold depend only on c and are chosen before the arbitrary finite vertex
type, edge size, and family. There are no extra structural assumptions on
the family. Opposite-colour conflict bounds include the same-edge case.

`Erdos1027Main.erdos_1027_subsets` counts subsets `B` such that, for every
`A` in the family, both `A ∩ B` and `A \ B` are nonempty. Its statement is
printed, including all implicit parameters, in `verification/axioms.log`.

## Actual transitive axiom audit

```text
'Erdos1027Main.count_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1027Main.erdos_1027' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1027Main.erdos_1027_subsets' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard foundational axioms. There is no `sorryAx` and no
custom axiom assuming the original problem, a probability bound, or any
completion theorem. The final theorem types and definitions also received AI-assisted
cross-checks for correspondence to the original statement. No independent
human review or organizer certification is claimed.

## Explicit constants

The machine proof establishes the original qualitative existence theorem
and the quantitative conclusion `delta = 1 / (4 * 2^L)` whenever

- `0 < L`;
- `8*c*exp(log(8*(c+1))) <= L`;
- `2*log(8*(c+1)) <= n`;
- `16*c^2*log(8*(c+1))*exp(2*log(8*(c+1))) <= n`.

It proves that suitable natural-number parameters exist. The paper's exact
ceiling choices and its `c = 1` decimal example have not been packaged as
separate Lean corollaries. This does not leave any part of the original
qualitative question unproved.

The exact finite Python checks remain supplementary; no finite experiment
is used to justify a universal theorem.

## Submission verification script

`scripts/verify.sh` builds the project and checks the three final theorem
axiom reports, records the toolchain and source hashes, and fails on missing
reports or additional axioms. The script passed locally on 2026-09-16 using
the same pinned dependency caches. The included GitHub Actions workflow
has not yet run on GitHub; no hosted CI result is claimed in this package.
