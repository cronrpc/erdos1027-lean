# Erdős Problem 1027 / JSP-000854: an elementary probabilistic proof

Prepared on 2026-09-16.

**Verification scope.** The full qualitative theorem, with all the quantifiers
of the original problem, has been formalized and successfully compiled with
Lean 4.19.0 and Mathlib v4.19.0. The final subset-counting theorem is
`Erdos1027Main.erdos_1027_subsets`; an equivalent two-colouring theorem is also
included. Its transitive axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx` or custom solution axiom. The formalization
also proves a quantitative bound under explicit numerical threshold
hypotheses. The particular ceiling formulas and numerical example below have
not been packaged as separate Lean corollaries.

See the [statement](STATEMENT.md), [Lean verification status](LEAN-STATUS.md),
and [source and attribution audit](SOURCES.md).

**Attribution.** The original problem already has a published mathematical
proof by Koishi Chan. This note presents an elementary argument using random
partial colouring, a union bound, Markov's inequality, and exponential
estimates. We make no claim of a first mathematical solution, a first
formalization, priority for this argument, or prize eligibility.

## 1. The problem and an explicit bound

Fix a real number \(c>0\). Let \(\mathcal F\) be a finite family of sets,
each with exactly \(n\) elements, satisfying

\[
m:=|\mathcal F|\le c2^n,
\qquad X:=\bigcup_{A\in\mathcal F}A.
\]

A subset \(B\subseteq X\) is **proper** if, for every
\(A\in\mathcal F\),

\[
A\cap B\ne\varnothing,
\qquad A\setminus B\ne\varnothing.
\]

Equivalently, colour the elements of \(B\) red and the remaining elements
blue. Every member of \(\mathcal F\) must contain both colours.
The problem asks whether, for every fixed \(c>0\), there are constants
\(\delta(c)>0\) and \(N(c)\) such that, whenever \(n\ge N(c)\), at least
\(\delta(c)2^{|X|}\) subsets of \(X\) are proper. Both constants must be
independent of \(n\), \(X\), and \(\mathcal F\).

We prove the following explicit version. Set

\[
k=\log(8(c+1)),
\qquad L=\left\lceil64c(c+1)\right\rceil,
\]

\[
N(c)=\left\lceil
\max\{2k,\ 1024c^2(c+1)^2k\}
\right\rceil,
\qquad \delta(c)=2^{-L-2},
\]

where \(\log\) denotes the natural logarithm. Then, for every integer
\(n\ge N(c)\),

\[
\boxed{
\#\{B\subseteq X:B\text{ is proper}\}
\ \ge\ 2^{-L-2}\,2^{|X|}.
}
\]

These constants are deliberately conservative; no optimality is asserted.
If \(\mathcal F=\varnothing\), then \(X=\varnothing\) and the unique
subset is proper, so the conclusion holds immediately.

## 2. Random partial colouring

Put

\[
p=\frac{k}{n},
\qquad b=\frac{1-p}{2},
\qquad a=\frac{1+p}{2}.
\]

The condition \(n\ge2k>0\) ensures \(0<p\le1/2\).
Independently assign each element of \(X\) one of three states:

| State | Probability | Interpretation |
|---|---:|---|
| Fixed red | \(b\) | Remains red in every completion |
| Fixed blue | \(b\) | Remains blue in every completion |
| Grey | \(p\) | Receives a fair, independent red or blue colour later |

If a member \(A\) contains no fixed red element, it has a **red demand**.
If it contains no fixed blue element, it has a **blue demand**.
Let \(M\) be the total number of demands of both kinds. An all-grey member
has two demands and must be counted twice.

We will show that, with probability at least \(1/4\), the partial colouring
can be completed properly by prescribing the colours of at most \(L\)
grey elements.

## 3. Irreparable demands

A red demand with no grey element means that its entire member has already
been fixed blue. Such a demand cannot be repaired. The analogous obstruction
for a blue demand is an entirely fixed-red member.

Let \(E_0\) be the event that some member is entirely fixed red or entirely
fixed blue. By the union bound,

\[
\begin{aligned}
\Pr(E_0)
&\le 2mb^n\\
&\le 2c(1-p)^n\\
&\le 2ce^{-np}\\
&=2ce^{-k}
=\frac{c}{4(c+1)}
<\frac14.
\end{aligned}
\]

Thus, outside \(E_0\), every demand has at least one grey element available
to satisfy it.

## 4. Too many demands

For a fixed member, the probability of having no fixed red element is
\((b+p)^n=a^n\). The same holds for a blue demand. Linearity of expectation
therefore gives

\[
\begin{aligned}
\mathbb E[M]
&=2ma^n\\
&\le2c(1+p)^n\\
&\le2ce^{np}\\
&=2ce^k
=16c(c+1).
\end{aligned}
\]

No independence between demands on different members is needed.
Because \(L\ge64c(c+1)>0\), Markov's inequality yields

\[
\Pr(M\ge L)
\le\frac{\mathbb E[M]}{L}
\le\frac14.
\]

The bad event in this step is \(M\ge L\); its complement is \(M<L\).

## 5. Conflicting demands

Consider an ordered pair \((A,B)\) of members with nonempty intersection.
Write \(\ell=|A\cap B|\), so \(1\le\ell\le n\).
If \(A\) has a red demand and \(B\) has a blue demand, every element of
their intersection must be grey: it can be neither fixed red nor fixed blue.
Each of the remaining \(2(n-\ell)\) elements must avoid just one fixed
colour. Independence of the element states gives the exact probability

\[
\Pr(A\text{ has a red demand and }B\text{ has a blue demand})
=p^\ell a^{2(n-\ell)}.
\]

Since

\[
a^2-p=\frac{(1-p)^2}{4}\ge0,
\]

we have

\[
\begin{aligned}
p^\ell a^{2(n-\ell)}
&=p\,p^{\ell-1}a^{2(n-\ell)}\\
&\le p\,a^{2(\ell-1)}a^{2(n-\ell)}\\
&=p\,a^{2n-2}.
\end{aligned}
\]

Let \(E_\times\) be the event that some intersecting ordered pair has a red
demand on its first member and a blue demand on its second member.
**The pairs \(A=B\) are included.** In particular, every all-grey member
causes this conflict event. Omitting these pairs would invalidate the later
consistency argument.

There are at most \(m^2\) ordered pairs. Using the union bound and
\(a\ge1/2\), we obtain

\[
\begin{aligned}
\Pr(E_\times)
&\le m^2p\,a^{2n-2}\\
&\le4m^2p\,a^{2n}\\
&\le4c^2p(1+p)^{2n}\\
&\le4c^2\frac{k}{n}e^{2k}\\
&=\frac{256c^2(c+1)^2k}{n}\\
&\le\frac14.
\end{aligned}
\]

The last inequality follows from
\(n\ge1024c^2(c+1)^2k\). No independence between the ordered-pair events
is assumed or needed.

## 6. Many completions of a good partial colouring

Call a partial colouring **good** if it lies in

\[
E_0^c\cap\{M<L\}\cap E_\times^c.
\]

The three estimates above imply

\[
\begin{aligned}
\Pr(\text{good})
&\ge1-\Pr(E_0)-\Pr(M\ge L)-\Pr(E_\times)\\
&\ge\frac14.
\end{aligned}
\]

Fix a good partial colouring. For each red demand, choose one grey element
of the corresponding member and prescribe that its final colour be red.
For each blue demand, choose a grey element and prescribe blue.
The absence of \(E_0\) guarantees that every such choice is possible.

These prescriptions are consistent. If one element were prescribed both
red and blue, it would belong to the intersection of a member with a red
demand and a member with a blue demand. This would imply \(E_\times\),
contrary to goodness. Demands for the same colour may use the same
representative without causing a conflict.

Let \(r\) be the number of distinct grey elements whose colours have been
prescribed. Then

\[
r\le M<L,
\qquad\text{and hence }r\le L.
\]

Every assignment of colours to the remaining grey elements now gives a
proper colouring. A fixed colour already present in a member remains
present, and each initially missing colour is supplied by its chosen
representative.

Consequently, when all grey elements receive independent fair colours, the
probability of satisfying the prescriptions is

\[
2^{-r}\ge2^{-L}.
\]

This is a lower bound on the proportion of proper completions, rather than
merely an existence argument. If there are \(g\) grey elements, at least
\(2^{g-r}\) of their \(2^g\) completions are proper.

## 7. Returning to uniform subset counting

Consider the full random procedure: first choose the independent three-state
partial colouring, then independently give each grey element a fair red or
blue colour.

For any individual element, the probability of ending red is

\[
\frac{1-p}{2}+p\cdot\frac12=\frac12,
\]

and the probability of ending blue is also \(1/2\). The random choices for
distinct elements are independent. Thus the final colouring is uniform
among all \(2^{|X|}\) red-blue colourings of \(X\).

For each good partial colouring, the conditional probability of a proper
completion is at least \(2^{-L}\). Therefore

\[
\begin{aligned}
\Pr(\text{final colouring is proper})
&\ge\Pr(\text{good partial colouring})\,2^{-L}\\
&\ge2^{-L-2}.
\end{aligned}
\]

Identifying a colouring with its red subset \(B\), the number of proper
subsets is at least \(2^{-L-2}2^{|X|}\). All the parameters \(L\), \(N\),
and \(\delta\) depend only on \(c\), as required. This proves the theorem.

## 8. A numerical example and the formalization boundary

For \(c=1\), these formulas give

\[
L=128,
\qquad N=\lceil4096\log16\rceil=11357,
\qquad \delta=2^{-130}\approx7.35\times10^{-40}.
\]

The lower bound is extremely small, but it is positive and does not decrease
with the number of vertices or the edge size. It answers the qualitative
question. It is neither a prediction of the actual fraction of proper
colourings nor a claim of an optimal threshold.

The Lean theorem proves the quantitative bound
\(\delta=1/(4\cdot2^L)\) under the numerical hypotheses

\[
L>0,
\qquad 8ce^k\le L,
\qquad 2k\le n,
\qquad 16c^2ke^{2k}\le n,
\]

and proves that suitable natural-number parameters exist. Since
\(e^k=8(c+1)\), the ceiling formulas in Section 1 satisfy these hypotheses
by ordinary arithmetic. That particular ceiling specialization, and the
decimal approximation in the example, have not been stated as separate
Lean corollaries. The full qualitative theorem does not depend on such a
specialization and is already verified.

The accompanying exact finite checks exercise representative selection,
intersection conflicts, and completion-counting identities. They are
supplementary checks; finite experiments do not establish the universal
theorem.

## 9. Sources and formal results

- [Original problem](https://www.erdosproblems.com/1027) and
  [LaTeX statement](https://www.erdosproblems.com/latex/1027).
- [Koishi Chan's proof and subsequent discussion](https://www.erdosproblems.com/forum/thread/1027).
  The published approach uses a nonuniform Property B theorem and adaptive
  random colouring. This note does not reproduce that approach.
- [JSP-000854 catalogue entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000854).
- The checked [teorth/erdosproblems](https://github.com/teorth/erdosproblems)
  metadata records the problem as mathematically proved and unformalized.
  This describes the material checked, not an exhaustive assessment of all
  existing formalizations.
- The checked
  [LeanGenius problem file](https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos1027Problem.lean)
  assumes the complete conclusion through `axiom erdos_1027_solution`.
  Its downstream theorem therefore does not, by itself, establish the
  conclusion without that assumption. This project neither imports that
  axiom nor copies that project's source code.

In the accompanying formalization,
`Erdos1027Main.erdos_1027_subsets` first chooses a positive proportion
\(\delta\) and a natural-number threshold \(N\) for an arbitrary real
\(c>0\). It then proves the subset-counting bound for every finite vertex
type, every \(n\ge N\), and every family meeting the uniform-size and
cardinality hypotheses. No degree bound or intersection restriction is
added. The finite probability calculation, bad-event estimates, completion
count, uniform-colouring identity, and conversion from colourings to subsets
are all connected in that theorem.

Reproduction instructions and the recorded axiom audit are in
[README.md](README.md), [LEAN-STATUS.md](LEAN-STATUS.md), and
[verification/axioms.log](verification/axioms.log). Attribution and the limits
of the source search are documented in [SOURCES.md](SOURCES.md).
