import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Elementary finite product probability for random partial Boolean colourings. -/
noncomputable section

namespace Erdos1027Probability

open scoped BigOperators
open Classical

/-- A coordinate is blank with weight `p` and each colour with weight `(1-p)/2`. -/
def weight (p : ℝ) : Option Bool → ℝ
  | none => p
  | some _ => (1 - p) / 2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Product weight of a partial colouring. -/
def prodWeight (p : ℝ) (f : V → Option Bool) : ℝ := ∏ v, weight p (f v)

/-- Finite mass of an arbitrary event. -/
noncomputable def mass (p : ℝ) (E : (V → Option Bool) → Prop) : ℝ := by
  classical
  exact ∑ f, if E f then prodWeight p f else 0

lemma weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Option Bool) :
    0 ≤ weight p x := by
  cases x with
  | none => exact hp0
  | some b => exact div_nonneg (sub_nonneg.mpr hp1) (by norm_num)

lemma prodWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : V → Option Bool) : 0 ≤ prodWeight p f := by
  exact Finset.prod_nonneg fun v _ => weight_nonneg hp0 hp1 (f v)

lemma mass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : (V → Option Bool) → Prop) : 0 ≤ mass p E := by
  classical
  unfold mass
  exact Finset.sum_nonneg fun f _ => by
    split_ifs
    · exact prodWeight_nonneg hp0 hp1 f
    · exact le_rfl

lemma sum_weight (p : ℝ) : ∑ x : Option Bool, weight p x = 1 := by
  simp only [Fintype.sum_option, Fintype.sum_bool, weight]
  ring

/-- Sum-product interchange gives coordinate independence without any measure theory. -/
lemma mass_coordinate (p : ℝ) (R : V → Option Bool → Prop) :
    mass p (fun f => ∀ v, R v (f v)) =
      ∏ v, ∑ x : Option Bool, if R v x then weight p x else 0 := by
  classical
  unfold mass prodWeight
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [Fintype.prod_ite_zero]
  split_ifs <;> rfl

lemma mass_univ (p : ℝ) : mass (V := V) p (fun _ => True) = 1 := by
  classical
  have h := mass_coordinate (V := V) p (fun _ _ => True)
  simpa only [implies_true, if_true, sum_weight, Finset.prod_const_one] using h

lemma mass_congr (p : ℝ) {E F : (V → Option Bool) → Prop}
    (h : ∀ f, E f ↔ F f) : mass p E = mass p F := by
  classical
  unfold mass
  apply Finset.sum_congr rfl
  intro f _
  simp only [h f]

lemma sum_weight_fixed (p : ℝ) (b : Bool) :
    (∑ x : Option Bool, if x = some b then weight p x else 0) = (1-p)/2 := by
  cases b <;> simp [Fintype.sum_option, Fintype.sum_bool, weight]

lemma sum_weight_missing (p : ℝ) (b : Bool) :
    (∑ x : Option Bool, if x ≠ some b then weight p x else 0) = (1+p)/2 := by
  cases b <;> simp [Fintype.sum_option, Fintype.sum_bool, weight] <;> ring

lemma sum_weight_missing_both (p : ℝ) :
    (∑ x : Option Bool, if x ≠ some true ∧ x ≠ some false then weight p x else 0) = p := by
  simp [Fintype.sum_option, Fintype.sum_bool, weight]

/-- Probability that every coordinate in `A` has the fixed colour `b`. -/
lemma mass_fixed (p : ℝ) (A : Finset V) (b : Bool) :
    mass p (fun f => ∀ v ∈ A, f v = some b) = ((1-p)/2)^A.card := by
  classical
  rw [mass_coordinate p (fun v x => v ∈ A → x = some b)]
  calc
    _ =
        ∏ v, if v ∈ A then (1-p)/2 else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ A
      · simp only [hv, true_implies, if_true, sum_weight_fixed]
      · simp only [hv, false_implies, if_true, if_false, sum_weight]
    _ = ((1-p)/2)^A.card := by rw [Fintype.prod_ite_mem]; simp only [Finset.prod_const]

/-- Probability that a given colour is absent from `A`. -/
lemma mass_missing (p : ℝ) (A : Finset V) (b : Bool) :
    mass p (fun f => ∀ v ∈ A, f v ≠ some b) = ((1+p)/2)^A.card := by
  classical
  rw [mass_coordinate p (fun v x => v ∈ A → x ≠ some b)]
  calc
    _ =
        ∏ v, if v ∈ A then (1+p)/2 else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ A
      · simp only [hv, true_implies, if_true, sum_weight_missing]
      · simp only [hv, false_implies, if_true, if_false, sum_weight]
    _ = ((1+p)/2)^A.card := by rw [Fintype.prod_ite_mem]; simp only [Finset.prod_const]

/-- Opposite-colour absence on two sets forces blanks on their intersection. -/
lemma mass_missing_pair (p : ℝ) (A B : Finset V) :
    mass p (fun f => (∀ v ∈ A, f v ≠ some true) ∧ (∀ v ∈ B, f v ≠ some false)) =
      p^(A ∩ B).card * ((1+p)/2)^((A \ B).card + (B \ A).card) := by
  classical
  have hevent : mass p
      (fun f => (∀ v ∈ A, f v ≠ some true) ∧ (∀ v ∈ B, f v ≠ some false)) =
      mass p (fun f => ∀ v, (v ∈ A → f v ≠ some true) ∧
        (v ∈ B → f v ≠ some false)) := by
    apply mass_congr
    intro f
    constructor
    · intro h v
      exact ⟨h.1 v, h.2 v⟩
    · intro h
      exact ⟨fun v => (h v).1, fun v => (h v).2⟩
  rw [hevent, mass_coordinate p (fun v x =>
    (v ∈ A → x ≠ some true) ∧ (v ∈ B → x ≠ some false))]
  calc
    _ =
        ∏ v, (if v ∈ A ∩ B then p else 1) *
          (if v ∈ A \ B then (1+p)/2 else 1) *
          (if v ∈ B \ A then (1+p)/2 else 1) := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases ha : v ∈ A <;> by_cases hb : v ∈ B <;>
        simp [ha, hb, sum_weight_missing, sum_weight_missing_both, sum_weight, weight] <;> ring
    _ = p^(A ∩ B).card * ((1+p)/2)^((A \ B).card + (B \ A).card) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rw [Fintype.prod_ite_mem, Fintype.prod_ite_mem, Fintype.prod_ite_mem]
      simp only [Finset.prod_const, pow_add]
      ring

end Erdos1027Probability
