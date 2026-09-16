import Erdos1027Probability
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Completing partial colourings preserves the uniform distribution

All identities below are finite real sums.  In particular, they avoid a measure
or probability-monad model and expose the exact counting bridge used by the
Erdős 1027 proof.
-/

open scoped BigOperators
open Classical

namespace Erdos1027Mixing

open Erdos1027Probability

noncomputable section

/-- Complete a partial colouring using one seed bit at each vertex. -/
def complete {V : Type*} (f : V → Option Bool) (u : V → Bool) : V → Bool :=
  fun v => (f v).getD (u v)

/-- Cardinality of a finite predicate, expressed as a real sum of indicators. -/
theorem nat_card_eq_sum_indicator {A : Type*} [Fintype A] (P : A → Prop) :
    (Nat.card {a : A // P a} : ℝ) = ∑ a, if P a then (1 : ℝ) else 0 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Factor the mass of partial colourings producing a prescribed final colouring. -/
theorem complete_coordinate_mass (p : ℝ) (u g : V → Bool) :
    mass p (fun f => complete f u = g) =
      ∏ v, ∑ x : Option Bool, if x.getD (u v) = g v then weight p x else 0 := by
  have h := mass_coordinate p (fun v (x : Option Bool) => x.getD (u v) = g v)
  have hevent : mass p (fun f => complete f u = g) =
      mass p (fun f => ∀ v, (f v).getD (u v) = g v) :=
    mass_congr p (fun _ => funext_iff)
  refine hevent.trans (h.trans ?_)
  apply Finset.prod_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

/-- Summing the output mass over all seed colourings gives one for each output. -/
theorem sum_complete_mass (p : ℝ) (g : V → Bool) :
    (∑ u : V → Bool, mass p (fun f => complete f u = g)) = 1 := by
  simp_rw [complete_coordinate_mass]
  rw [← Fintype.prod_sum (fun v (b : Bool) =>
    ∑ x : Option Bool, if x.getD b = g v then weight p x else 0)]
  calc
    (∏ v, ∑ b : Bool, ∑ x : Option Bool,
      if x.getD b = g v then weight p x else 0) = ∏ _v : V, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro v _
      cases g v <;> simp [Fintype.sum_bool, Fintype.sum_option, weight] <;> ring
    _ = 1 := Finset.prod_const_one

/-- The finite kernel obtained by composing partial colours and seeds is uniform. -/
theorem completion_kernel (p : ℝ) (g : V → Bool) :
    (∑ f : V → Option Bool, ∑ u : V → Bool,
      if complete f u = g then prodWeight p f else 0) = 1 := by
  rw [Finset.sum_comm]
  have h := sum_complete_mass p g
  unfold mass at h
  refine Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro f _
  split_ifs <;> rfl

/-- Uniform mixing, expressed for an arbitrary real test function. -/
theorem weighted_completion_sum (p : ℝ) (H : (V → Bool) → ℝ) :
    (∑ f : V → Option Bool, prodWeight p f * ∑ u : V → Bool, H (complete f u)) =
      ∑ g : V → Bool, H g := by
  have hpoint (f : V → Option Bool) (u : V → Bool) :
      prodWeight p f * H (complete f u) =
        ∑ g : V → Bool, (if complete f u = g then prodWeight p f else 0) * H g := by
    simp only [ite_mul, zero_mul]
    simp
  calc
    (∑ f : V → Option Bool, prodWeight p f * ∑ u : V → Bool, H (complete f u)) =
        ∑ f : V → Option Bool, ∑ u : V → Bool, ∑ g : V → Bool,
          (if complete f u = g then prodWeight p f else 0) * H g := by
      simp_rw [Finset.mul_sum, hpoint]
    _ = ∑ f : V → Option Bool, ∑ g : V → Bool, ∑ u : V → Bool,
          (if complete f u = g then prodWeight p f else 0) * H g := by
      apply Finset.sum_congr rfl
      intro f _
      exact Finset.sum_comm
    _ = ∑ g : V → Bool, ∑ f : V → Option Bool, ∑ u : V → Bool,
          (if complete f u = g then prodWeight p f else 0) * H g := Finset.sum_comm
    _ = ∑ g : V → Bool, (∑ f : V → Option Bool, ∑ u : V → Bool,
          if complete f u = g then prodWeight p f else 0) * H g := by
      simp_rw [Finset.sum_mul]
    _ = ∑ g : V → Bool, H g := by simp_rw [completion_kernel, one_mul]

/-- The exact bridge from weighted good seeds to the number of good colourings. -/
theorem weighted_completion_count (p : ℝ) (Good : (V → Bool) → Prop) :
    (∑ f : V → Option Bool, prodWeight p f *
      (Nat.card {u : V → Bool // Good (complete f u)} : ℝ)) =
        (Nat.card {g : V → Bool // Good g} : ℝ) := by
  simpa only [nat_card_eq_sum_indicator] using
    weighted_completion_sum p (fun g => if Good g then 1 else 0)

/-- A lower bound on seed counts on an event transfers to a global colour count. -/
theorem good_count_lower_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Good : (V → Bool) → Prop) (Successful : (V → Option Bool) → Prop)
    (L : ℕ)
    (hseed : ∀ f, Successful f →
      (2 : ℝ) ^ Fintype.card V ≤
        (Nat.card {u : V → Bool // Good (complete f u)} : ℝ) * 2 ^ L) :
    mass p Successful * (2 : ℝ) ^ Fintype.card V ≤
      (Nat.card {g : V → Bool // Good g} : ℝ) * 2 ^ L := by
  calc
    mass p Successful * (2 : ℝ) ^ Fintype.card V =
        ∑ f : V → Option Bool,
          if Successful f then prodWeight p f * (2 : ℝ) ^ Fintype.card V else 0 := by
      simp only [mass, Finset.sum_mul, ite_mul, zero_mul]
    _ ≤ ∑ f : V → Option Bool, prodWeight p f *
        ((Nat.card {u : V → Bool // Good (complete f u)} : ℝ) * 2 ^ L) := by
      apply Finset.sum_le_sum
      intro f _
      by_cases hf : Successful f
      · simp only [hf, if_pos]
        exact mul_le_mul_of_nonneg_left (hseed f hf) (prodWeight_nonneg hp0 hp1 f)
      · simp only [hf, if_neg]
        exact mul_nonneg (prodWeight_nonneg hp0 hp1 f)
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))
    _ = (Nat.card {g : V → Bool // Good g} : ℝ) * 2 ^ L := by
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, weighted_completion_count]


/-- A successful partial-colouring mass of one quarter gives an explicit
positive proportion, without divisions or truncated natural subtraction. -/
theorem good_count_quarter {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Good : (V → Bool) → Prop) (Successful : (V → Option Bool) → Prop)
    (L : ℕ) (hquarter : (1 : ℝ) / 4 ≤ mass p Successful)
    (hseed : ∀ f, Successful f →
      (2 : ℝ) ^ Fintype.card V ≤
        (Nat.card {u : V → Bool // Good (complete f u)} : ℝ) * 2 ^ L) :
    (2 : ℝ) ^ Fintype.card V ≤
      (Nat.card {g : V → Bool // Good g} : ℝ) * 2 ^ (L + 2) := by
  have hbound := good_count_lower_bound hp0 hp1 Good Successful L hseed
  have hquarterbound : (1 / 4 : ℝ) * 2 ^ Fintype.card V ≤
      (Nat.card {g : V → Bool // Good g} : ℝ) * 2 ^ L :=
    (mul_le_mul_of_nonneg_right hquarter (pow_nonneg (by norm_num) _)).trans hbound
  calc
    (2 : ℝ) ^ Fintype.card V = 4 * ((1 / 4 : ℝ) * 2 ^ Fintype.card V) := by ring
    _ ≤ 4 * ((Nat.card {g : V → Bool // Good g} : ℝ) * 2 ^ L) :=
      mul_le_mul_of_nonneg_left hquarterbound (by norm_num)
    _ = (Nat.card {g : V → Bool // Good g} : ℝ) * 2 ^ (L + 2) := by
      rw [pow_add]
      ring


/-- The density formulation used in the final Erdős statement. -/
theorem density_count_lower_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Good : (V → Bool) → Prop) (Successful : (V → Option Bool) → Prop)
    (L : ℕ) (hquarter : (1 : ℝ) / 4 ≤ mass p Successful)
    (hseed : ∀ f, Successful f →
      (2 : ℝ) ^ Fintype.card V ≤
        (Nat.card {u : V → Bool // Good (complete f u)} : ℝ) * 2 ^ L) :
    (1 / (4 * (2 : ℝ) ^ L)) * 2 ^ Fintype.card V ≤
      (Nat.card {g : V → Bool // Good g} : ℝ) := by
  have hbound := good_count_quarter hp0 hp1 Good Successful L hquarter hseed
  have hden : (0 : ℝ) < 4 * 2 ^ L :=
    mul_pos (by norm_num) (pow_pos (by norm_num) _)
  calc
    (1 / (4 * (2 : ℝ) ^ L)) * 2 ^ Fintype.card V =
        2 ^ Fintype.card V / (4 * 2 ^ L) := by ring
    _ ≤ (Nat.card {g : V → Bool // Good g} : ℝ) := by
      apply (div_le_iff₀ hden).2
      convert hbound using 1 <;> simp only [pow_add] <;> ring

end
end Erdos1027Mixing
