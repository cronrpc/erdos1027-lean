# Source audit — 2026-09-16

## Original problem and existing mathematical proof

- Original problem: https://www.erdosproblems.com/1027
- Exact LaTeX statement: https://www.erdosproblems.com/latex/1027
- Koishi Chan's proof and subsequent correction:
  https://www.erdosproblems.com/forum/thread/1027
- Prize catalogue entry:
  https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000854

The exact statement quantifies over every fixed positive real c. Both delta
and the large-n threshold may depend on c, but not on the family or its
vertex count. No bounded-degree or limited-intersection hypothesis is present.

Chan's published argument uses a nonuniform Property B theorem and adaptive
random colouring. The accompanying proof note reconstructs a different
elementary partial-colouring argument. We have not established priority or
novelty for that argument.

## Existing Lean material checked

The downloaded teorth/erdosproblems metadata marks problem 1027 as proved,
but its formalization status as unformalized:
https://github.com/teorth/erdosproblems

The file at
https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos1027Problem.lean
assumes the complete result through `axiom erdos_1027_solution`. Consequently,
its later theorem is not evidence of a complete kernel-verified solution
without that additional assumption. The related OQ01 and OQ03 files address
restricted regimes, not the full all-fixed-c claim.

No complete formalization was found in the sources checked. This is a
limited search result, not an exhaustive guarantee of absence. External
Lean source files are not copied into this deliverable.

## Review and verification

The written proof received AI-assisted cross-checks, including the same-edge
conflict case, integer ceiling bounds, representative consistency, empty
family, and final uniform-colouring count. These AI-assisted reviews are fallible and are neither independent human
review nor a formal machine certificate.

The Python checks exhaust finite cases exactly. Actual Lean compilation and
axiom-audit output is recorded separately in `LEAN-STATUS.md`.
