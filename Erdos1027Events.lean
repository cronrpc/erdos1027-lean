import Erdos1027Probability
import Erdos1027Completion
import Erdos1027Estimates
import Lean.Elab.Tactic.Omega

/-! Finite union, first-moment and conflict estimates for partial colourings. -/
namespace Erdos1027Events

open scoped BigOperators
open Erdos1027Probability

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma mass_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E G : (V → Option Bool) → Prop} (h : ∀ f, E f → G f) :
    mass p E ≤ mass p G := by
  classical
  apply Finset.sum_le_sum
  intro f _
  by_cases he : E f
  · simp only [he, h f he, if_true]
    exact le_rfl
  · simp only [he, if_false]
    split_ifs
    · exact prodWeight_nonneg hp0 hp1 f
    · exact le_rfl

lemma mass_compl (p : ℝ) (E : (V → Option Bool) → Prop) :
    mass p (fun f => ¬ E f) = 1 - mass p E := by
  classical
  have hsum : mass p (fun f => ¬ E f) + mass p E = 1 := by
    rw [← mass_univ (V := V) p]
    unfold mass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f _
    by_cases he : E f <;> simp [he]
  linarith

lemma mass_union_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E G : (V → Option Bool) → Prop) :
    mass p (fun f => E f ∨ G f) ≤ mass p E + mass p G := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro f _
  have hw := prodWeight_nonneg hp0 hp1 f
  by_cases he : E f <;> by_cases hg : G f <;> simp [he, hg] <;> linarith

lemma mass_exists_finset_le {I : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset I) (E : I → (V → Option Bool) → Prop) :
    mass p (fun f => ∃ i ∈ s, E i f) ≤ ∑ i ∈ s, mass p (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mass]
  | @insert i s hi ih =>
    have he : mass p (fun f => ∃ j ∈ insert i s, E j f) =
        mass p (fun f => E i f ∨ ∃ j ∈ s, E j f) := by
      apply mass_congr
      intro f
      simp only [Finset.mem_insert, exists_eq_or_imp]
    rw [he, Finset.sum_insert hi]
    exact (mass_union_le hp0 hp1 _ _).trans (add_le_add_left ih _)

noncomputable def expectation (p : ℝ) (X : (V → Option Bool) → ℝ) : ℝ :=
  ∑ f, prodWeight p f * X f

lemma mass_markov {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ht : 0 < t) (X : (V → Option Bool) → ℝ) (hX : ∀ f, 0 ≤ X f) :
    mass p (fun f => t ≤ X f) ≤ expectation p X / t := by
  classical
  apply (le_div_iff₀ ht).2
  unfold mass expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro f _
  have hw := prodWeight_nonneg hp0 hp1 f
  by_cases hx : t ≤ X f
  · simp only [hx, if_true]
    exact mul_le_mul_of_nonneg_left hx hw
  · simp only [hx, if_false, zero_mul]
    exact mul_nonneg hw (hX f)

lemma expectation_add (p : ℝ) (X Y : (V → Option Bool) → ℝ) :
    expectation p (fun f => X f + Y f) = expectation p X + expectation p Y := by
  classical
  simp only [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_count {I : Type*} (p : ℝ) (s : Finset I)
    (E : I → (V → Option Bool) → Prop) :
    expectation p (fun f => ((s.filter (fun i => E i f)).card : ℝ)) =
      ∑ i ∈ s, mass p (E i) := by
  classical
  simp only [expectation, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter, Nat.cast_ite, Nat.cast_zero, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  rfl

/-- Number of still-missing colour requirements after a partial colouring. -/
noncomputable def requirements (F : Finset (Finset V)) (f : V → Option Bool) : ℕ :=
  (Erdos1027.requests F f true).card + (Erdos1027.requests F f false).card

/-- An edge fully painted a single colour cannot subsequently be repaired. -/
def badEmpty (F : Finset (Finset V)) (f : V → Option Bool) : Prop :=
  ∃ A ∈ F, ∃ b : Bool, ∀ v ∈ A, f v = some b

/-- Opposite requests conflict only if their underlying edges overlap. -/
def badCross (F : Finset (Finset V)) (f : V → Option Bool) : Prop :=
  ∃ A ∈ F, ∃ B ∈ F, (A ∩ B).Nonempty ∧
    (∀ v ∈ A, f v ≠ some true) ∧ (∀ v ∈ B, f v ≠ some false)

lemma mass_badEmpty_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : Finset (Finset V)) (n : ℕ) (hFn : ∀ A ∈ F, A.card = n) :
    mass p (badEmpty F) ≤ 2 * (F.card : ℝ) * ((1-p)/2)^n := by
  classical
  have hfirst := mass_exists_finset_le hp0 hp1 F
    (fun A f => ∃ b : Bool, ∀ v ∈ A, f v = some b)
  refine hfirst.trans ?_
  calc
    (∑ A ∈ F, mass p (fun f => ∃ b : Bool, ∀ v ∈ A, f v = some b)) ≤
        ∑ A ∈ F, (2 * ((1-p)/2)^n) := by
      apply Finset.sum_le_sum
      intro A hA
      have hb := mass_exists_finset_le hp0 hp1 (Finset.univ : Finset Bool)
        (fun b f => ∀ v ∈ A, f v = some b)
      simpa only [Finset.mem_univ, true_and, mass_fixed, hFn A hA,
        Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
        Nat.cast_ofNat] using hb
    _ = 2 * (F.card : ℝ) * ((1-p)/2)^n := by simp; ring

lemma expectation_requirements (p : ℝ) (F : Finset (Finset V))
    (n : ℕ) (hFn : ∀ A ∈ F, A.card = n) :
    expectation p (fun f => (requirements F f : ℝ)) =
      2 * (F.card : ℝ) * ((1+p)/2)^n := by
  classical
  simp only [requirements, Nat.cast_add]
  rw [expectation_add]
  have hreq (b : Bool) :
      expectation p (fun f => ((Erdos1027.requests F f b).card : ℝ)) =
      ∑ A ∈ F, mass p (fun f => ∀ v ∈ A, f v ≠ some b) := by
    convert expectation_count p F (fun A f => ∀ v ∈ A, f v ≠ some b) using 1
    congr 1
    funext f
    congr 1
    congr 1
    ext A
    simp only [Erdos1027.mem_requests, Finset.mem_filter]
  rw [hreq true, hreq false]
  have hs (b : Bool) :
      (∑ A ∈ F, mass p (fun f => ∀ v ∈ A, f v ≠ some b)) =
        (F.card : ℝ) * ((1+p)/2)^n := by
    calc
      (∑ A ∈ F, mass p (fun f => ∀ v ∈ A, f v ≠ some b)) =
          ∑ A ∈ F, ((1+p)/2)^n := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [mass_missing, hFn A hA]
      _ = (F.card : ℝ) * ((1+p)/2)^n := by simp
  rw [hs true, hs false]
  ring

lemma mass_avoid_three {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E₀ E₁ E₂ : (V → Option Bool) → Prop)
    (h₀ : mass p E₀ ≤ 1/4) (h₁ : mass p E₁ ≤ 1/4)
    (h₂ : mass p E₂ ≤ 1/4) :
    1/4 ≤ mass p (fun f => ¬ E₀ f ∧ ¬ E₁ f ∧ ¬ E₂ f) := by
  have he : mass p (fun f => ¬ E₀ f ∧ ¬ E₁ f ∧ ¬ E₂ f) =
      mass p (fun f => ¬ (E₀ f ∨ E₁ f ∨ E₂ f)) := by
    apply mass_congr
    intro f
    simp only [not_or]
  rw [he, mass_compl]
  have hU := mass_union_le hp0 hp1 E₀ (fun f => E₁ f ∨ E₂ f)
  have hV := mass_union_le hp0 hp1 E₁ E₂
  linarith

lemma mass_badCross_pair_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Finset V) (n : ℕ) (hA : A.card = n) (hB : B.card = n) :
    mass p (fun f => (A ∩ B).Nonempty ∧
        (∀ v ∈ A, f v ≠ some true) ∧ (∀ v ∈ B, f v ≠ some false)) ≤
      p * ((1+p)/2)^(2*n-2) := by
  classical
  by_cases hne : (A ∩ B).Nonempty
  · have he : mass p (fun f => (A ∩ B).Nonempty ∧
        (∀ v ∈ A, f v ≠ some true) ∧ (∀ v ∈ B, f v ≠ some false)) =
        mass p (fun f => (∀ v ∈ A, f v ≠ some true) ∧
          (∀ v ∈ B, f v ≠ some false)) := by
      apply mass_congr
      intro f
      simp only [hne, true_and]
    rw [he, mass_missing_pair]
    have hcA := Finset.card_sdiff_add_card_inter A B
    have hcB := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm B A] at hcB
    have hExp : (A \ B).card + (B \ A).card = 2*(n-(A∩B).card) := by omega
    rw [hExp]
    apply Erdos1027Estimates.pair_overlap_bound p n (A∩B).card hp0 hp1
    · exact Finset.card_pos.mpr hne
    · exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hA
  · simp only [hne, false_and, mass, if_false, Finset.sum_const_zero]
    exact mul_nonneg hp0 (pow_nonneg (by linarith) _)

lemma mass_badCross_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : Finset (Finset V)) (n : ℕ) (hFn : ∀ A ∈ F, A.card = n) :
    mass p (badCross F) ≤
      (F.card : ℝ)^2 * (p * ((1+p)/2)^(2*n-2)) := by
  classical
  refine (mass_exists_finset_le hp0 hp1 F (fun A f => ∃ B ∈ F,
    (A ∩ B).Nonempty ∧ (∀ v ∈ A, f v ≠ some true) ∧
      (∀ v ∈ B, f v ≠ some false))).trans ?_
  calc
    (∑ A ∈ F, mass p (fun f => ∃ B ∈ F, (A ∩ B).Nonempty ∧
        (∀ v ∈ A, f v ≠ some true) ∧ (∀ v ∈ B, f v ≠ some false))) ≤
      ∑ A ∈ F, ∑ B ∈ F, (p * ((1+p)/2)^(2*n-2)) := by
      apply Finset.sum_le_sum
      intro A hA
      refine (mass_exists_finset_le hp0 hp1 F _).trans ?_
      apply Finset.sum_le_sum
      intro B hB
      exact mass_badCross_pair_le hp0 hp1 A B n (hFn A hA) (hFn B hB)
    _ = (F.card : ℝ)^2 * (p * ((1+p)/2)^(2*n-2)) := by simp; ring

end Erdos1027Events

#print axioms Erdos1027Events.mass_badEmpty_le
#print axioms Erdos1027Events.expectation_requirements
#print axioms Erdos1027Events.mass_badCross_le
#print axioms Erdos1027Events.mass_avoid_three
