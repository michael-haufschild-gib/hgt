import GaloisForLFunctions.RHTower.FiniteEulerLocalQuartet

/-!
# Finite reflected Euler local ratios

The ordinary finite-place ratio is the quotient of a reflected Euler factor
by its original factor.  This file records its exact Euler-power formula,
reflection inverse law, and the fixed-point identity at `s = 1/2`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-- The reflected ratio of one finite zeta Euler factor. -/
def finiteEulerLocalRatio (p : Nat.Primes) (s : ℂ) : ℂ :=
  finiteEulerLocalFactor p (1 - s) / finiteEulerLocalFactor p s

/-- The finite local ratio has the classical Euler-power expression. -/
theorem finiteEulerLocalRatio_eq_cpow (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalRatio p s =
      (1 - ((p : ℕ) : ℂ) ^ (s - 1)) / (1 - ((p : ℕ) : ℂ) ^ (-s)) := by
  unfold finiteEulerLocalRatio
  rw [finiteEulerLocalFactor_eq_one_sub_natCast_cpow p (1 - s),
    finiteEulerLocalFactor_eq_one_sub_natCast_cpow p s]
  congr 3
  ring

/-- Reflection sends a local ratio to its multiplicative inverse. -/
theorem finiteEulerLocalRatio_reflection (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalRatio p (1 - s) = (finiteEulerLocalRatio p s)⁻¹ := by
  unfold finiteEulerLocalRatio
  rw [sub_sub_cancel]
  exact (inv_div _ _).symm

/-- At the unique reflection fixed point, every finite local ratio is one. -/
theorem finiteEulerLocalRatio_half (p : Nat.Primes) :
    finiteEulerLocalRatio p (1 / 2) = 1 := by
  unfold finiteEulerLocalRatio
  have hline : (1 - (1 / 2 : ℂ) : ℂ) = 1 / 2 := by norm_num
  rw [hline, div_self]
  convert finiteEulerLocalFactor_criticalLine_ne_zero p 0 using 1
  norm_num

/-- At the left endpoint the finite local ratio is zero. -/
theorem finiteEulerLocalRatio_zero (p : Nat.Primes) :
    finiteEulerLocalRatio p 0 = 0 := by
  simp [finiteEulerLocalRatio, finiteEulerLocalFactor]

/-- At the right endpoint the finite local ratio is zero. -/
theorem finiteEulerLocalRatio_one (p : Nat.Primes) :
    finiteEulerLocalRatio p 1 = 0 := by
  simp [finiteEulerLocalRatio, finiteEulerLocalFactor]

/-- The constant unit family is not summable on the prime index type. -/
theorem not_summable_constant_one_on_primes :
    ¬ Summable (fun _ : Nat.Primes => (1 : ℝ)) := by
  intro h
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (0 : ℝ)) := by
    simpa using h
  rw [Nat.Primes.summable_rpow] at hpow
  norm_num at hpow

/-- The finite local ratios do not approach one absolutely at the left endpoint. -/
theorem not_summable_norm_finiteEulerLocalRatio_sub_one_zero :
    ¬ Summable (fun p : Nat.Primes => ‖finiteEulerLocalRatio p 0 - 1‖) := by
  simpa [finiteEulerLocalRatio_zero] using not_summable_constant_one_on_primes

/-- The finite local ratios do not approach one absolutely at the right endpoint. -/
theorem not_summable_norm_finiteEulerLocalRatio_sub_one_one :
    ¬ Summable (fun p : Nat.Primes => ‖finiteEulerLocalRatio p 1 - 1‖) := by
  simpa [finiteEulerLocalRatio_one] using not_summable_constant_one_on_primes

/-- At the off-line point `s = 1/4`, the local-ratio deviation has an exact
positive two-power expression. -/
theorem finiteEulerLocalRatio_quarter_sub_one (p : Nat.Primes) :
    finiteEulerLocalRatio p (1 / 4) - 1 =
      (((p : ℝ) ^ (-(1 / 4 : ℝ)) + (p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  let a : ℂ := ((p : ℕ) : ℂ) ^ (-(1 / 4 : ℂ))
  have ha_ne_one : a ≠ 1 := by
    intro ha
    have hanorm : ‖a‖ < 1 := by
      dsimp [a]
      rw [Complex.norm_natCast_cpow_of_pos p.property.pos]
      norm_num
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by norm_num)
    have : ‖a‖ = 1 := by rw [ha, norm_one]
    exact (ne_of_lt hanorm) this
  have ha3 : ((p : ℕ) : ℂ) ^ (-(3 / 4 : ℂ)) = a ^ 3 := by
    dsimp [a]
    rw [show (-(3 / 4 : ℂ)) = (3 : ℂ) * (-(1 / 4 : ℂ)) by ring]
    exact Complex.cpow_nat_mul _ 3 _
  have ha : ((p : ℕ) : ℂ) ^ (-(1 / 4 : ℂ)) = a := rfl
  have hratio : finiteEulerLocalRatio p (1 / 4) = 1 + a + a ^ 2 := by
    rw [finiteEulerLocalRatio_eq_cpow]
    norm_num
    rw [ha3, ha]
    field_simp
    ring
  rw [hratio]
  have ha_real : a = (((p : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) := by
    dsimp [a]
    rw [show ((p : ℕ) : ℂ) = ((p : ℝ) : ℂ) by norm_cast]
    rw [show (-(1 / 4 : ℂ)) = (-(1 / 4 : ℝ) : ℂ) by norm_num]
    rw [← ofReal_neg]
    exact (Complex.ofReal_cpow (show 0 ≤ (p : ℝ) by positivity) (-(1 / 4 : ℝ))).symm
  rw [ha_real]
  push_cast
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
  have hsq : ((p : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 = (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 4 : ℝ))) 2,
      ← Real.rpow_mul hp_nonneg]
    congr 1
    ring
  norm_cast
  rw [hsq]
  ring

/-- The exact quarter-point deviation dominates its leading prime power. -/
theorem finiteEulerLocalRatio_quarter_norm_lower (p : Nat.Primes) :
    (p : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ‖finiteEulerLocalRatio p (1 / 4) - 1‖ := by
  rw [finiteEulerLocalRatio_quarter_sub_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  · exact le_add_of_nonneg_right (by positivity)
  · positivity

/-- The finite local ratios do not approach one absolutely at the off-line
point `s = 1/4`. -/
theorem not_summable_norm_finiteEulerLocalRatio_sub_one_quarter :
    ¬ Summable (fun p : Nat.Primes => ‖finiteEulerLocalRatio p (1 / 4) - 1‖) := by
  intro h
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 / 4 : ℝ))) :=
    Summable.of_nonneg_of_le (fun p => by positivity)
      finiteEulerLocalRatio_quarter_norm_lower h
  rw [Nat.Primes.summable_rpow] at hpow
  norm_num at hpow

/-- Reflection gives the exact complementary off-line deviation at `s = 3/4`. -/
theorem finiteEulerLocalRatio_threeQuarter_sub_one (p : Nat.Primes) :
    finiteEulerLocalRatio p (3 / 4) - 1 =
      -((((p : ℝ) ^ (-(1 / 4 : ℝ)) + (p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) /
        (1 + (((p : ℝ) ^ (-(1 / 4 : ℝ)) + (p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) := by
  let q : ℂ :=
    (((p : ℝ) ^ (-(1 / 4 : ℝ)) + (p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  have hquarter : finiteEulerLocalRatio p (1 / 4) = 1 + q := by
    calc
      finiteEulerLocalRatio p (1 / 4) =
          (finiteEulerLocalRatio p (1 / 4) - 1) + 1 := by ring
      _ = q + 1 := by rw [finiteEulerLocalRatio_quarter_sub_one]
      _ = 1 + q := by ring
  have hreflection : finiteEulerLocalRatio p (3 / 4) =
      (finiteEulerLocalRatio p (1 / 4))⁻¹ := by
    convert finiteEulerLocalRatio_reflection p (1 / 4) using 1
    norm_num
  have hden : 1 + q ≠ 0 := by
    have hpos : (0 : ℝ) < 1 +
        (p : ℝ) ^ (-(1 / 4 : ℝ)) + (p : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    intro h
    have hre : (1 + q).re = 0 := by rw [h]; simp
    norm_num [q] at hre
    nlinarith [hre]
  rw [hreflection, hquarter]
  dsimp [q] at hden ⊢
  field_simp
  ring

/-- The reflected `3/4` deviation still dominates a fixed multiple of the
same non-summable prime power. -/
theorem finiteEulerLocalRatio_threeQuarter_norm_lower (p : Nat.Primes) :
    (1 / 3 : ℝ) * (p : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      ‖finiteEulerLocalRatio p (3 / 4) - 1‖ := by
  let q : ℝ := (p : ℝ) ^ (-(1 / 4 : ℝ))
  let r : ℝ := q + (p : ℝ) ^ (-(1 / 2 : ℝ))
  have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
  have hqle : q ≤ 1 := by
    dsimp [q]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast p.property.one_lt.le) (by norm_num)
  have hsq : q ^ 2 = (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    dsimp [q]
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 4 : ℝ))) 2,
      ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hr : r = q + q ^ 2 := by
    dsimp [r]
    rw [hsq]
  have hrnonneg : 0 ≤ r := by rw [hr]; positivity
  have hdenpos : 0 < 1 + r := by linarith
  have hnorm : ‖finiteEulerLocalRatio p (3 / 4) - 1‖ = r / (1 + r) := by
    rw [finiteEulerLocalRatio_threeQuarter_sub_one]
    change ‖-((r : ℂ) / (1 + (r : ℂ)))‖ = r / (1 + r)
    rw [norm_neg, norm_div]
    rw [show 1 + (r : ℂ) = ((1 + r : ℝ) : ℂ) by push_cast; ring]
    change ‖(r : ℂ)‖ / ‖((1 + r : ℝ) : ℂ)‖ = r / (1 + r)
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hrnonneg, Real.norm_eq_abs, abs_of_nonneg hdenpos.le]
  rw [hnorm]
  apply (le_div_iff₀ hdenpos).2
  have hq2nonneg : 0 ≤ q ^ 2 := sq_nonneg q
  have hqcube : q ^ 3 ≤ q ^ 2 := by
    calc
      q ^ 3 = q ^ 2 * q := by ring
      _ ≤ q ^ 2 * 1 := mul_le_mul_of_nonneg_left hqle hq2nonneg
      _ = q ^ 2 := by ring
  rw [hr]
  nlinarith

/-- The finite local ratios do not approach one absolutely at the reflected
off-line point `s = 3/4`. -/
theorem not_summable_norm_finiteEulerLocalRatio_sub_one_threeQuarter :
    ¬ Summable (fun p : Nat.Primes => ‖finiteEulerLocalRatio p (3 / 4) - 1‖) := by
  intro h
  have hscaled : Summable (fun p : Nat.Primes =>
      (1 / 3 : ℝ) * (p : ℝ) ^ (-(1 / 4 : ℝ))) :=
    Summable.of_nonneg_of_le (fun p => by positivity)
      finiteEulerLocalRatio_threeQuarter_norm_lower h
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 / 4 : ℝ))) := by
    rw [← summable_mul_left_iff (by norm_num : (1 / 3 : ℝ) ≠ 0)]
    exact hscaled
  rw [Nat.Primes.summable_rpow] at hpow
  norm_num at hpow

end GaloisForLFunctions.RHTower

end
