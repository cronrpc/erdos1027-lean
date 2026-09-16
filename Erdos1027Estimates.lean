import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Local algebraic estimates for an Erdos 1027 proof attempt

STATUS: VERIFIED with Lean 4.19.0 and mathlib v4.19.0.
All declarations in this file have been checked by Lean; no `sorry` or
custom axioms are used. See the axiom reports at the end of this file.

This file does NOT formalize Erdos 1027 itself, a probability space, or
the required combinatorial probability estimates.  Its intended scope is
the real algebra used after those estimates have been established.

All powers with a natural-number exponent are ordinary natural powers.
-/

namespace Erdos1027Estimates

/-- The elementary exponential upper bound for a positive binomial factor. -/
theorem positive_binomial_bound (p : ℝ) (n : ℕ) (hp : 0 ≤ p) :
    (1 + p) ^ n ≤ Real.exp ((n : ℝ) * p) := by
  have hbase : 1 + p ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) hbase n

/-- The elementary exponential upper bound for an empty-edge factor. -/
theorem negative_binomial_bound (p : ℝ) (n : ℕ) (hp : p ≤ 1) :
    (1 - p) ^ n ≤ Real.exp (-(n : ℝ) * p) := by
  have hbase : 1 - p ≤ Real.exp (-p) := by
    linarith [Real.add_one_le_exp (-p)]
  calc
    (1 - p) ^ n ≤ Real.exp (-p) ^ n :=
      pow_le_pow_left₀ (by linarith) hbase n
    _ = Real.exp (-(n : ℝ) * p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Algebra for the first-moment bound, assuming at most `c * 2^n` edges.
The probabilistic interpretation must be established separately. -/
theorem first_moment_factor_bound (c m p : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (hp : 0 ≤ p) (hm : m ≤ c * 2 ^ n) :
    m * ((1 + p) / 2) ^ n ≤ c * Real.exp ((n : ℝ) * p) := by
  have ha : 0 ≤ (1 + p) / 2 := by positivity
  have hcancel : (2 : ℝ) * ((1 + p) / 2) = 1 + p := by ring
  calc
    m * ((1 + p) / 2) ^ n ≤ (c * 2 ^ n) * ((1 + p) / 2) ^ n :=
      mul_le_mul_of_nonneg_right hm (pow_nonneg ha n)
    _ = c * (1 + p) ^ n := by rw [mul_assoc, ← mul_pow, hcancel]
    _ ≤ c * Real.exp ((n : ℝ) * p) :=
      mul_le_mul_of_nonneg_left (positive_binomial_bound p n hp) hc

/-- Algebra for the empty-color error, under the same edge-count bound. -/
theorem empty_factor_bound (c m p : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (hp : p ≤ 1) (hm : m ≤ c * 2 ^ n) :
    2 * m * ((1 - p) / 2) ^ n ≤ 2 * c * Real.exp (-(n : ℝ) * p) := by
  have ha : 0 ≤ (1 - p) / 2 := by linarith
  have hcancel : (2 : ℝ) * ((1 - p) / 2) = 1 - p := by ring
  have hscaled : 2 * m ≤ (2 * c) * 2 ^ n := by nlinarith [hm]
  calc
    2 * m * ((1 - p) / 2) ^ n ≤ ((2 * c) * 2 ^ n) * ((1 - p) / 2) ^ n :=
      mul_le_mul_of_nonneg_right hscaled (pow_nonneg ha n)
    _ = (2 * c) * (1 - p) ^ n := by rw [mul_assoc, ← mul_pow, hcancel]
    _ ≤ 2 * c * Real.exp (-(n : ℝ) * p) :=
      mul_le_mul_of_nonneg_left (negative_binomial_bound p n hp) (by positivity)

/-- The one-vertex overlap comparison used in the pair-conflict estimate. -/
theorem p_le_square_average (p : ℝ) : p ≤ ((1 + p) / 2) ^ 2 := by
  nlinarith [sq_nonneg (p - 1)]

/-- A nonempty overlap of size `ell` contributes no more than the
one-vertex-overlap bound. This is an algebraic statement, not a claim
about the probability of any particular event. -/
theorem pair_overlap_bound (p : ℝ) (n ell : ℕ)
    (hp : 0 ≤ p) (_hp1 : p ≤ 1) (h1 : 1 ≤ ell) (hn : ell ≤ n) :
    p ^ ell * ((1 + p) / 2) ^ (2 * (n - ell)) ≤
      p * ((1 + p) / 2) ^ (2 * n - 2) := by
  let a : ℝ := (1 + p) / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpa : p ≤ a ^ 2 := p_le_square_average p
  have hpow : p ^ (ell - 1) ≤ (a ^ 2) ^ (ell - 1) :=
    pow_le_pow_left₀ hp hpa _
  have hsplit : p ^ ell = p * p ^ (ell - 1) := by
    calc
      p ^ ell = p ^ ((ell - 1) + 1) := by congr 1; omega
      _ = p * p ^ (ell - 1) := by rw [pow_succ]; ring
  have hexp : 2 * (ell - 1) + 2 * (n - ell) = 2 * n - 2 := by omega
  change p ^ ell * a ^ (2 * (n - ell)) ≤ p * a ^ (2 * n - 2)
  calc
    p ^ ell * a ^ (2 * (n - ell)) =
        p * (p ^ (ell - 1) * a ^ (2 * (n - ell))) := by rw [hsplit]; ring
    _ ≤ p * ((a ^ 2) ^ (ell - 1) * a ^ (2 * (n - ell))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (pow_nonneg ha _)) hp
    _ = p * a ^ (2 * n - 2) := by rw [← pow_mul, ← pow_add, hexp]

/-- Summing the uniform overlap bound over at most `m^2` ordered pairs
has the required exponential upper bound. Only the algebra is asserted here. -/
theorem cross_factor_bound (c m p : ℝ) (n : ℕ)
    (hm0 : 0 ≤ m) (hp : 0 ≤ p) (hn : 1 ≤ n)
    (hm : m ≤ c * 2 ^ n) :
    m ^ 2 * (p * ((1 + p) / 2) ^ (2 * n - 2)) ≤
      4 * c ^ 2 * p * Real.exp (2 * (n : ℝ) * p) := by
  let d : ℕ := 2 * n - 2
  let a : ℝ := (1 + p) / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hm2 : m ^ 2 ≤ c ^ 2 * (2 : ℝ) ^ (2 * n) := by
    calc
      m ^ 2 ≤ (c * 2 ^ n) ^ 2 := pow_le_pow_left₀ hm0 hm 2
      _ = c ^ 2 * (2 : ℝ) ^ (2 * n) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm n 2]
  have hde : 2 * n = d + 2 := by dsimp [d]; omega
  have htwo : (2 : ℝ) ^ (2 * n) = 4 * 2 ^ d := by
    rw [hde, pow_add]
    norm_num
    ring
  have hcancel : (2 : ℝ) * a = 1 + p := by dsimp [a]; ring
  have hpoly : (1 + p) ^ d ≤ Real.exp (2 * (n : ℝ) * p) := by
    calc
      (1 + p) ^ d ≤ (1 + p) ^ (2 * n) :=
        pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
      _ ≤ Real.exp (2 * (n : ℝ) * p) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          positive_binomial_bound p (2 * n) hp
  change m ^ 2 * (p * a ^ d) ≤ 4 * c ^ 2 * p * Real.exp (2 * (n : ℝ) * p)
  calc
    m ^ 2 * (p * a ^ d) ≤ (c ^ 2 * (2 : ℝ) ^ (2 * n)) * (p * a ^ d) :=
      mul_le_mul_of_nonneg_right hm2 (mul_nonneg hp (pow_nonneg ha _))
    _ = 4 * c ^ 2 * p * ((2 : ℝ) ^ d * a ^ d) := by rw [htwo]; ring
    _ = 4 * c ^ 2 * p * (1 + p) ^ d := by rw [← mul_pow, hcancel]
    _ ≤ 4 * c ^ 2 * p * Real.exp (2 * (n : ℝ) * p) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)

/-- The explicit choice of the auxiliary parameter. -/
noncomputable def k (c : ℝ) : ℝ := Real.log (8 * (c + 1))

theorem k_pos (c : ℝ) (hc : 0 < c) : 0 < k c := by
  apply Real.log_pos
  linarith

theorem exp_k (c : ℝ) (hc : 0 < c) : Real.exp (k c) = 8 * (c + 1) := by
  apply Real.exp_log
  positivity

/-- The first error term is strictly below one quarter. -/
theorem empty_error_lt_quarter (c : ℝ) (hc : 0 < c) :
    2 * c * Real.exp (-k c) < (1 : ℝ) / 4 := by
  rw [Real.exp_neg, exp_k c hc]
  have hden : 0 < 8 * (c + 1) := by positivity
  change (2 * c) / (8 * (c + 1)) < (1 : ℝ) / 4
  apply (div_lt_iff₀ hden).2
  linarith

/-- If the expectation is at most `2 c exp(k)`, Markov's bound at the
threshold `8 c exp(k)` is at most one quarter. This only verifies the
ratio; Markov's inequality is not formalized in this file. -/
theorem markov_ratio (c : ℝ) (hc : 0 < c) :
    (2 * c * Real.exp (k c)) / (8 * c * Real.exp (k c)) = (1 : ℝ) / 4 := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have he0 : Real.exp (k c) ≠ 0 := ne_of_gt (Real.exp_pos _)
  field_simp [hc0, he0]
  ring

/-- The size threshold guarantees a valid partial-coloring probability. -/
theorem sampling_parameter_bounds (c n : ℝ) (hc : 0 < c)
    (hn : 2 * k c ≤ n) :
    0 < k c / n ∧ k c / n ≤ (1 : ℝ) / 2 := by
  have hk := k_pos c hc
  have hn0 : 0 < n := by linarith
  constructor
  · exact div_pos hk hn0
  · apply (div_le_iff₀ hn0).2
    linarith

/-- The second size threshold controls the total pair-conflict estimate. -/
theorem conflict_error_le_quarter (c n : ℝ) (hc : 0 < c)
    (hn1 : 2 * k c ≤ n)
    (hn2 : 16 * c ^ 2 * k c * Real.exp (2 * k c) ≤ n) :
    (4 * c ^ 2 * Real.exp (2 * k c) * k c) / n ≤ (1 : ℝ) / 4 := by
  have hk := k_pos c hc
  have hn0 : 0 < n := by linarith
  apply (div_le_iff₀ hn0).2
  nlinarith [hn2]

/-- The empty-edge numeric estimate with the actual sampling parameter. -/
theorem sampled_empty_bound (c m : ℝ) (n : ℕ) (hc : 0 < c)
    (hm : m ≤ c * 2 ^ n) (hn : 2 * k c ≤ (n : ℝ)) :
    2 * m * ((1 - k c / (n : ℝ)) / 2) ^ n < (1 : ℝ) / 4 := by
  obtain ⟨hp0, hp1⟩ := sampling_parameter_bounds c (n : ℝ) hc hn
  have hk := k_pos c hc
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith : 0 < (n : ℝ))
  have hneg : -(n : ℝ) * (k c / (n : ℝ)) = -k c := by field_simp [hn0]; ring
  have hbound := empty_factor_bound c m (k c / (n : ℝ)) n hc.le
    (by linarith : k c / (n : ℝ) ≤ 1) hm
  rw [hneg] at hbound
  exact hbound.trans_lt (empty_error_lt_quarter c hc)

/-- The first-moment numeric estimate with the actual sampling parameter. -/
theorem sampled_moment_bound (c m : ℝ) (n : ℕ) (hc : 0 < c)
    (hm : m ≤ c * 2 ^ n) (hn : 2 * k c ≤ (n : ℝ)) :
    2 * m * ((1 + k c / (n : ℝ)) / 2) ^ n ≤ 2 * c * Real.exp (k c) := by
  obtain ⟨hp0, hp1⟩ := sampling_parameter_bounds c (n : ℝ) hc hn
  have hk := k_pos c hc
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith : 0 < (n : ℝ))
  have hmul : (n : ℝ) * (k c / (n : ℝ)) = k c := by field_simp [hn0]
  have hbound := first_moment_factor_bound c m (k c / (n : ℝ)) n hc.le hp0.le hm
  rw [hmul] at hbound
  nlinarith [hbound]

/-- The total cross-conflict numeric estimate with the actual parameter. -/
theorem sampled_cross_bound (c m : ℝ) (n : ℕ) (hc : 0 < c)
    (hm0 : 0 ≤ m) (hm : m ≤ c * 2 ^ n)
    (hn1 : 2 * k c ≤ (n : ℝ))
    (hn2 : 16 * c ^ 2 * k c * Real.exp (2 * k c) ≤ (n : ℝ)) :
    m ^ 2 * ((k c / (n : ℝ)) * ((1 + k c / (n : ℝ)) / 2) ^ (2 * n - 2)) ≤
      (1 : ℝ) / 4 := by
  obtain ⟨hp0, hp1⟩ := sampling_parameter_bounds c (n : ℝ) hc hn1
  have hk := k_pos c hc
  have hnpos : 0 < (n : ℝ) := by linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hnn : 1 ≤ n := Nat.cast_pos.mp hnpos
  have hmul : 2 * (n : ℝ) * (k c / (n : ℝ)) = 2 * k c := by field_simp [hn0]; ring
  have hbound := cross_factor_bound c m (k c / (n : ℝ)) n hm0 hp0.le hnn hm
  rw [hmul] at hbound
  have hfactor : 4 * c ^ 2 * (k c / (n : ℝ)) * Real.exp (2 * k c) =
      (4 * c ^ 2 * Real.exp (2 * k c) * k c) / (n : ℝ) := by ring
  rw [hfactor] at hbound
  exact hbound.trans (conflict_error_le_quarter c (n : ℝ) hc hn1 hn2)

/-- The three numeric error estimates sum to strictly less than `3/4`. -/
theorem total_error_lt_three_quarters (c n : ℝ) (hc : 0 < c)
    (hn1 : 2 * k c ≤ n)
    (hn2 : 16 * c ^ 2 * k c * Real.exp (2 * k c) ≤ n) :
    2 * c * Real.exp (-k c) +
      (2 * c * Real.exp (k c)) / (8 * c * Real.exp (k c)) +
      (4 * c ^ 2 * Real.exp (2 * k c) * k c) / n < (3 : ℝ) / 4 := by
  rw [markov_ratio c hc]
  have hempty := empty_error_lt_quarter c hc
  have hconflict := conflict_error_le_quarter c n hc hn1 hn2
  linarith

/-- Abstract final arithmetic after a union bound has been proved.
`hcover` must be obtained from the actual probability space separately. -/
theorem good_mass_gt_quarter (good bad₁ bad₂ bad₃ : ℝ)
    (hcover : 1 ≤ good + bad₁ + bad₂ + bad₃)
    (hbad : bad₁ + bad₂ + bad₃ < (3 : ℝ) / 4) :
    (1 : ℝ) / 4 < good := by
  linarith

/-- A positive lower-density constant determined only by the constraint budget. -/
noncomputable def density (L : ℕ) : ℝ := 1 / (4 * 2 ^ L)

theorem density_pos (L : ℕ) : 0 < density L := by
  unfold density
  positivity

theorem density_mul_pow (L : ℕ) : density L * (2 : ℝ) ^ L = (1 : ℝ) / 4 := by
  unfold density
  have hpow : (2 : ℝ) ^ L ≠ 0 := ne_of_gt (by positivity)
  field_simp [hpow]
  ring

/-- The large-`n` parameter choice, with an integer constraint budget `L`.
This lemma proves parameter existence directly; it does not assume a
coloring theorem or any probabilistic existence conclusion. -/
theorem parameters_exist (c : ℝ) (hc : 0 < c) :
    ∃ N L : ℕ,
      0 < N ∧ 0 < L ∧ 0 < density L ∧
      8 * c * Real.exp (k c) ≤ (L : ℝ) ∧
      2 * k c ≤ (N : ℝ) ∧
      16 * c ^ 2 * k c * Real.exp (2 * k c) ≤ (N : ℝ) ∧
      ∀ n : ℕ, N ≤ n →
        0 < k c / (n : ℝ) ∧ k c / (n : ℝ) ≤ (1 : ℝ) / 2 ∧
        2 * c * Real.exp (-k c) < (1 : ℝ) / 4 ∧
        (2 * c * Real.exp (k c)) / (L : ℝ) ≤ (1 : ℝ) / 4 ∧
        (4 * c ^ 2 * Real.exp (2 * k c) * k c) / (n : ℝ) ≤ (1 : ℝ) / 4 := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (2 * k c) (16 * c ^ 2 * k c * Real.exp (2 * k c)))
  obtain ⟨L, hL⟩ := exists_nat_gt (8 * c * Real.exp (k c))
  have hk := k_pos c hc
  have hN1 : 2 * k c ≤ (N : ℝ) := (le_max_left _ _).trans hN.le
  have hN2 : 16 * c ^ 2 * k c * Real.exp (2 * k c) ≤ (N : ℝ) :=
    (le_max_right _ _).trans hN.le
  have hNpos : 0 < (N : ℝ) := by linarith
  have hLpos : 0 < (L : ℝ) := by
    have hpos : 0 < 8 * c * Real.exp (k c) := by positivity
    exact hpos.trans hL
  refine ⟨N, L, Nat.cast_pos.mp hNpos, Nat.cast_pos.mp hLpos,
    density_pos L, hL.le, hN1, hN2, ?_⟩
  intro n hn
  have hnn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hn1 : 2 * k c ≤ (n : ℝ) := hN1.trans hnn
  have hn2 : 16 * c ^ 2 * k c * Real.exp (2 * k c) ≤ (n : ℝ) := hN2.trans hnn
  obtain ⟨hp0, hp1⟩ := sampling_parameter_bounds c (n : ℝ) hc hn1
  refine ⟨hp0, hp1, empty_error_lt_quarter c hc, ?_,
    conflict_error_le_quarter c (n : ℝ) hc hn1 hn2⟩
  apply (div_le_iff₀ hLpos).2
  linarith [hL.le]

end Erdos1027Estimates

#print axioms Erdos1027Estimates.pair_overlap_bound
#print axioms Erdos1027Estimates.total_error_lt_three_quarters
#print axioms Erdos1027Estimates.good_mass_gt_quarter
#print axioms Erdos1027Estimates.cross_factor_bound
#print axioms Erdos1027Estimates.parameters_exist
