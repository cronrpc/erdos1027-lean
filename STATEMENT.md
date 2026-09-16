# Statement correspondence: Erdős 1027 / JSP-000854

This document explains how the compiled theorem corresponds to the
[original problem](https://www.erdosproblems.com/1027). The final declarations
are in [Erdos1027Main.lean](Erdos1027Main.lean); the exact colouring-to-subset
equivalence is in [Erdos1027Subsets.lean](Erdos1027Subsets.lean).

## Mathematical statement

For every real number $c>0$, there exist a real number $\delta>0$ and a
natural number $N$ such that the following holds. For every finite vertex
set $V$, every natural number $n\ge N$, and every finite family
$\mathcal F$ of subsets of $V$, if

$$
\forall A\in\mathcal F,\quad |A|=n,
\qquad |\mathcal F|\le c\,2^n,
$$

then

$$
\left|\left\{B\subseteq V:
  \forall A\in\mathcal F,\;
  A\cap B\ne\varnothing\ \text{and}\ A\setminus B\ne\varnothing
\right\}\right|
\;\ge\;\delta\,2^{|V|}.
$$

The conclusion gives a positive proportion of all subsets, uniformly over
the family and its vertex count. It is stronger than the existence of one
splitting subset.

## Exact final Lean statement

The following is the declaration type of
`Erdos1027Main.erdos_1027_subsets`, omitting only its proof:

```lean
theorem erdos_1027_subsets (c : ℝ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (n : ℕ), N ≤ n → ∀ (F : Finset (Finset V)),
          (∀ A ∈ F, A.card = n) → (F.card : ℝ) ≤ c * 2 ^ n →
            δ * (2 : ℝ) ^ Fintype.card V ≤
              (Nat.card {B : Finset V // Erdos1027Subsets.Splits F B} : ℝ)
```

Here `Splits` is defined by

```lean
def Splits (F : Finset (Finset V)) (B : Finset V) : Prop :=
  ∀ A ∈ F, (A ∩ B).Nonempty ∧ (A \ B).Nonempty
```

The quantifiers are important: `δ` and `N` are chosen **before** `V`, `n`,
and `F`. Their construction invokes `parameters_exist c hc`, which has no
family or vertex-set argument. Thus both parameters depend only on `c`.

| Original notion | Lean representation | Correspondence |
|---|---|---|
| Arbitrary positive real constant | `c : ℝ`, `hc : 0 < c` | No restriction to small, rational, or integral `c` |
| Positive density depending only on `c` | `∃ δ : ℝ, 0 < δ` before the universal family quantifiers | Uniform positive proportion |
| Sufficiently large edge size | `∃ N : ℕ`, followed by `N ≤ n` | One threshold works for all finite ground sets and families |
| Finite ground set | `[Fintype V]` | Includes the empty ground set |
| Equality of vertices | `[DecidableEq V]` | An encoding requirement, available classically; not a structural hypothesis on the family |
| Finite family of finite sets | `F : Finset (Finset V)` | Edges are sets, and the family has no repeated members |
| Uniform edge size | `∀ A ∈ F, A.card = n` | Every member has exactly `n` elements |
| Bound on the number of members | `(F.card : ℝ) ≤ c * 2 ^ n` | The stated exponential bound, with the weak inequality included |
| A subset meeting every member in both colours | `Splits F B` | Both the intersection and the set difference are nonempty |
| Number of valid subsets | `Nat.card {B : Finset V // Splits F B}` | Counts distinct subsets satisfying the predicate |
| Total number of subsets | `2 ^ Fintype.card V` | The usual power-set size |

All types being counted are finite because `V` is finite. In particular,
the conclusion does not use the convention that `Nat.card` of an infinite
type is zero.

No bounded-degree, limited-intersection, disjointness, or prior
two-colourability assumption occurs in the final theorem. Conditions on
successful partial colourings are established inside the proof; they are
not additional assumptions on the input family.

## Taking the ground set to be the union

In the original formulation, put
$X=\bigcup_{A\in\mathcal F}A$. This union is finite. Take the finite type
`V` to represent `X`, and regard each member of the family as a finite
subset of this type. This reindexing preserves the size of every member,
the number of members, and the splitting condition. The displayed theorem
then has denominator $2^{|X|}$ and counts precisely the subsets of the
original union.

The exported theorem is stated for an arbitrary finite ground type, so
the ground set is not required to equal the union. If extra vertices are
present, each choice on those vertices is free: adding `t` unused vertices
multiplies both the number of splitting subsets and the total number of
subsets by $2^t$, leaving the proportion unchanged. For direct statement
comparison, simply use the union as the ground type.

This paragraph describes the representation of the original finite
problem. There is no separate exported wrapper that starts from a possibly
infinite ambient type and carries out the union-subtype reindexing in Lean.

## Empty families and counting conventions

The theorem does not assume `F.Nonempty`. If the family is empty, `Splits`
is vacuous and every subset of the finite ground type is counted. With
the ground type chosen as the union, the union is empty and the unique
empty subset is counted. The constructed density
`1 / (4 * 2^L)` is positive and at most one, so this case is consistent
with the same conclusion.

For a nonempty family, the construction chooses a positive threshold
`N`, so the admitted edge sizes are positive. No empty edge is silently
permitted in the large-`n` nonempty-family case.

The intermediate predicate is

```lean
def Proper (F : Finset (Finset V)) (u : V → Bool) : Prop :=
  ∀ A ∈ F, ∀ b : Bool, ∃ v ∈ A, u v = b
```

`properEquivSplits` proves a genuine equivalence between proper Boolean
colourings and splitting subsets. Its forward map sends a colouring to
the vertices coloured `true`; its inverse is the membership indicator of
the subset. Both inverse identities are proved. Consequently,
`proper_card_eq_splitting_card` gives an exact equality of the two counts.

There is **no factor of two** in this conversion. A subset specifies which
colour is `true`; the statement does not identify a subset with its
complement or count unordered bipartitions.

## Quantitative scope and the paper's ceiling choices

The compiled theorem `Erdos1027Main.count_lower_bound` proves the density
$1/(4\,2^L)$ under explicit numerical hypotheses. Set

$$
k=\log(8(c+1)).
$$

Its numerical assumptions are

$$
L\in\mathbb N,\quad 0<L,\quad 8c e^k\le L,\qquad
2k\le n,\qquad 16c^2 k e^{2k}\le n.
$$

Together with the uniformity and family-size assumptions, these imply

$$
\frac{1}{4\,2^L}\,2^{|V|}
\le \#\{\text{proper Boolean colourings of }V\}.
$$

The checked cardinality equivalence above converts this to the same
subset count. The final existence theorem obtains suitable natural
numbers using `exists_nat_gt`, and therefore does not assume the
existence of suitable parameters as an additional hypothesis.

The accompanying [mathematical note](PROOF.md) chooses the more specific
paper constants

$$
L=\lceil64c(c+1)\rceil,
\qquad
N=\left\lceil\max\{2k,1024c^2(c+1)^2k\}\right\rceil.
$$

These ceiling choices satisfy the displayed weak numerical inequalities
mathematically. However, the package does not include separate Lean
corollaries proving those exact ceiling formulas or the note's numerical
example for `c = 1`. In particular, it does not assert that the existential
witnesses selected by `exists_nat_gt` equal these ceilings; at an integral
boundary its strict inequality can select a larger parameter. The full
qualitative original theorem and the quantitative theorem with the
displayed hypotheses are the machine-checked claims.

## Verification and interpretation

The final theorem statements, complete dependency path, and transitive
axiom audit are recorded in [LEAN-STATUS.md](LEAN-STATUS.md) and
[verification/axioms.log](verification/axioms.log). The audit reports only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom
solution axiom.

Kernel checking establishes the formal declarations. The correspondence
explanation in this document remains a human-readable interpretation of
those declarations and is open to reviewer scrutiny. Attribution and
the role of AI assistance are recorded in [ATTRIBUTION.md](ATTRIBUTION.md).
