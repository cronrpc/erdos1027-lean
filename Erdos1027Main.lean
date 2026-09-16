import Erdos1027Probability
import Erdos1027Completion
import Erdos1027Estimates
import Erdos1027Events
import Erdos1027Mixing
import Erdos1027Subsets

/-! End-to-end assembly of the finite-colouring argument for Erdos 1027. -/

noncomputable section
open Classical
open scoped BigOperators

namespace Erdos1027Main

open Erdos1027Probability Erdos1027Events Erdos1027Estimates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If no edge has already become monochromatic, every outstanding colour
request has a blank vertex that can supply the missing colour. -/
theorem gray_of_no_monochromatic (F : Finset (Finset V)) (f : V → Option Bool)
    (h0 : ¬ badEmpty F f) (b : Bool) (A : Finset V)
    (hreq : A ∈ Erdos1027.requests F f b) :
    ∃ v ∈ A, f v = none := by
  have ha : A ∈ F ∧ ∀ v ∈ A, f v ≠ some b := by
    exact (Erdos1027.mem_requests F f b A).mp hreq
  apply Classical.byContradiction
  intro hgray
  have hnone : ∀ v ∈ A, f v ≠ none := by
    intro v hv hn
    exact hgray ⟨v, hv, hn⟩
  apply h0
  refine ⟨A, ha.1, !b, ?_⟩
  intro v hv
  have hnot := ha.2 v hv
  have hng := hnone v hv
  cases hfv : f v with
  | none => exact False.elim (hng hfv)
  | some z => cases b <;> cases z <;> simp_all

/-- Avoiding the cross event makes opposite outstanding edges disjoint.
Self-pairs are included in `badCross`, so all-blank edges are also excluded. -/
theorem disjoint_of_no_cross (F : Finset (Finset V)) (f : V → Option Bool)
    (hx : ¬ badCross F f) :
    ∀ A ∈ Erdos1027.requests F f true,
      ∀ B ∈ Erdos1027.requests F f false, Disjoint A B := by
  intro A hA B hB
  have ha : A ∈ F ∧ ∀ v ∈ A, f v ≠ some true := by
    exact (Erdos1027.mem_requests F f true A).mp hA
  have hb : B ∈ F ∧ ∀ v ∈ B, f v ≠ some false := by
    exact (Erdos1027.mem_requests F f false B).mp hB
  apply Finset.disjoint_left.mpr
  intro v hvA hvB
  exact hx ⟨A, ha.1, B, hb.1,
    ⟨⟨v, Finset.mem_inter.mpr ⟨hvA, hvB⟩⟩, ha.2, hb.2⟩⟩

/-- Quantitative counting bound from the explicit numerical thresholds. -/
theorem count_lower_bound (c : ℝ) (hc : 0 < c) (n L : ℕ)
    (hL : 0 < L) (hBudget : 8 * c * Real.exp (k c) ≤ (L : ℝ))
    (hn1 : 2 * k c ≤ (n : ℝ))
    (hn2 : 16 * c ^ 2 * k c * Real.exp (2 * k c) ≤ (n : ℝ))
    (F : Finset (Finset V)) (hUniform : ∀ A ∈ F, A.card = n)
    (hEdges : (F.card : ℝ) ≤ c * 2 ^ n) :
    density L * (2 : ℝ) ^ Fintype.card V ≤
      (Nat.card {g : V → Bool // Erdos1027.Proper F g} : ℝ) := by
  let p : ℝ := k c / (n : ℝ)
  obtain ⟨hp0, hpHalf⟩ := sampling_parameter_bounds c (n : ℝ) hc hn1
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hpNonneg : 0 ≤ p := hp0.le
  have hLreal : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  let E₁ : (V → Option Bool) → Prop :=
    fun f => (L : ℝ) ≤ (requirements F f : ℝ)
  let Successful : (V → Option Bool) → Prop :=
    fun f => ¬ badEmpty F f ∧ ¬ E₁ f ∧ ¬ badCross F f
  have hEmpty : mass p (badEmpty F) ≤ (1 : ℝ) / 4 := by
    exact (mass_badEmpty_le hpNonneg hp1 F n hUniform).trans
      (sampled_empty_bound c (F.card : ℝ) n hc hEdges hn1).le
  have hMoment : expectation p (fun f => (requirements F f : ℝ)) ≤
      2 * c * Real.exp (k c) := by
    rw [expectation_requirements p F n hUniform]
    exact sampled_moment_bound c (F.card : ℝ) n hc hEdges hn1
  have hMarkov : mass p E₁ ≤ (1 : ℝ) / 4 := by
    have htail := mass_markov hpNonneg hp1 hLreal
      (fun f => (requirements F f : ℝ)) (fun _ => Nat.cast_nonneg _)
    apply htail.trans
    apply (div_le_iff₀ hLreal).2
    nlinarith [hMoment, hBudget]
  have hCross : mass p (badCross F) ≤ (1 : ℝ) / 4 := by
    exact (mass_badCross_le hpNonneg hp1 F n hUniform).trans
      (sampled_cross_bound c (F.card : ℝ) n hc (Nat.cast_nonneg _)
        hEdges hn1 hn2)
  have hSuccess : (1 : ℝ) / 4 ≤ mass p Successful :=
    mass_avoid_three hpNonneg hp1 (badEmpty F) E₁ (badCross F)
      hEmpty hMarkov hCross
  have hseed (f : V → Option Bool) (hf : Successful f) :
      (2 : ℝ) ^ Fintype.card V ≤
        (Nat.card {u : V → Bool //
          Erdos1027.Proper F (Erdos1027Mixing.complete f u)} : ℝ) * 2 ^ L := by
    have hM : requirements F f ≤ L := by
      have hlt : (requirements F f : ℝ) < (L : ℝ) := lt_of_not_ge hf.2.1
      exact le_of_lt (Nat.cast_lt.mp hlt)
    have hcount := Erdos1027.good_partial_seed_count F f L
      (gray_of_no_monochromatic F f hf.1)
      (disjoint_of_no_cross F f hf.2.2) hM
    exact_mod_cast hcount
  exact Erdos1027Mixing.density_count_lower_bound hpNonneg hp1
    (Erdos1027.Proper F) Successful L hSuccess hseed

/-- The complete original qualitative claim, uniformly over the finite vertex
type: the positive proportion and large-edge-size threshold depend only on c.
Every edge has both colours; no degree or intersection assumption is added. -/
theorem erdos_1027 (c : ℝ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (n : ℕ), N ≤ n → ∀ (F : Finset (Finset V)),
          (∀ A ∈ F, A.card = n) → (F.card : ℝ) ≤ c * 2 ^ n →
            δ * (2 : ℝ) ^ Fintype.card V ≤
              (Nat.card {g : V → Bool // Erdos1027.Proper F g} : ℝ) := by
  obtain ⟨N, L, hNpos, hLpos, hδ, hBudget, hN1, hN2, _⟩ :=
    parameters_exist c hc
  refine ⟨density L, hδ, N, ?_⟩
  intro V _ _ n hn F hUniform hEdges
  have hcast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  exact count_lower_bound c hc n L hLpos hBudget
    (hN1.trans hcast) (hN2.trans hcast) F hUniform hEdges

/-- The same full result stated directly as a count of subsets splitting
every member of the family, matching the original problem formulation. -/
theorem erdos_1027_subsets (c : ℝ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (n : ℕ), N ≤ n → ∀ (F : Finset (Finset V)),
          (∀ A ∈ F, A.card = n) → (F.card : ℝ) ≤ c * 2 ^ n →
            δ * (2 : ℝ) ^ Fintype.card V ≤
              (Nat.card {B : Finset V // Erdos1027Subsets.Splits F B} : ℝ) := by
  obtain ⟨δ, hδ, N, hMain⟩ := erdos_1027 c hc
  refine ⟨δ, hδ, N, ?_⟩
  intro V _ _ n hn F hUniform hEdges
  simpa only [Erdos1027Subsets.proper_card_eq_splitting_card] using
    hMain V n hn F hUniform hEdges

end Erdos1027Main

#print axioms Erdos1027Main.erdos_1027
#print axioms Erdos1027Main.erdos_1027_subsets
