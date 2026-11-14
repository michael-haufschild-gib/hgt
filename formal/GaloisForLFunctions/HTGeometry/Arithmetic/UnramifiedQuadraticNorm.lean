import GaloisForLFunctions.HTGeometry.RationalTameData
import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationParity
import GaloisForLFunctions.HTGeometry.Arithmetic.SquareDenominator

/-!
# Quadratic norm tests for simultaneous local integrality

If a rational unit has nonsquare residue at a prime, its binary norm form
has no cancellation even when the two coordinates have equal valuation.
The norm valuation is twice the smaller coordinate valuation. A single
square-denominator condition therefore tests both coordinates at once.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

variable {p : ℕ} [Fact p.Prime]

/-- A unit square cannot cancel a unit with nonsquare residue. -/
theorem isPadicUnit_sq_sub_of_nonsquare_residue {β u : ℚ}
    (hβ : IsPadicUnit p β) (hns : ¬ IsSquare (ratRes p β))
    (hu : IsPadicUnit p u) : IsPadicUnit p (u ^ 2 - β) := by
  let s : ℚ := (u * u) * β⁻¹
  have hs : IsPadicUnit p s := (hu.mul hu).mul hβ.inv
  have hres : ratRes p s ≠ 1 := by
    intro h
    rw [ratRes_mul (hu.mul hu) hβ.inv, ratRes_mul hu hu, ratRes_inv hβ] at h
    have heq := congrArg (fun x : ZMod p => x * ratRes p β) h
    have hsq : ratRes p u * ratRes p u = ratRes p β := by
      simpa only [mul_assoc, inv_mul_cancel₀ hβ.ratRes_ne_zero, mul_one, one_mul] using heq
    exact hns ⟨ratRes p u, hsq.symm⟩
  have hone : IsPadicUnit p (1 - s) := isPadicUnit_of_ratRes_ne_zero (by
    rw [ratRes_one_sub hs.2]
    exact sub_ne_zero.mpr hres.symm)
  have hneg : IsPadicUnit p (-β) := (padicValRat_eq_zero_iff (neg_ne_zero.mpr hβ.ne_zero)).mp (by
    rw [padicValRat.neg]
    exact (padicValRat_eq_zero_iff hβ.ne_zero).mpr hβ)
  have heq : u ^ 2 - β = -β * (1 - s) := by
    dsimp only [s]
    field_simp [hβ.ne_zero]
    ring
  rw [heq]
  exact hneg.mul hone

/-- The unramified binary norm has exactly twice the smaller coordinate
valuation. The nonzero-coordinate restriction avoids the total convention
`padicValRat p 0 = 0`. -/
theorem quadraticNorm_val {β a b : ℚ}
    (hβ : IsPadicUnit p β) (hns : ¬ IsSquare (ratRes p β))
    (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 2 - β * b ^ 2 ≠ 0 ∧
      padicValRat p (a ^ 2 - β * b ^ 2) =
        2 * min (padicValRat p a) (padicValRat p b) := by
  have hβval := (padicValRat_eq_zero_iff hβ.ne_zero).mpr hβ
  by_cases heq : padicValRat p a = padicValRat p b
  · have hu : IsPadicUnit p (a / b) := (padicValRat_eq_zero_iff (div_ne_zero ha hb)).mp (by
      rw [padicValRat.div ha hb, heq, sub_self])
    have hnorm := isPadicUnit_sq_sub_of_nonsquare_residue hβ hns hu
    have hfactor : a ^ 2 - β * b ^ 2 = b ^ 2 * ((a / b) ^ 2 - β) := by
      field_simp
    rw [hfactor]
    refine ⟨mul_ne_zero (pow_ne_zero 2 hb) hnorm.ne_zero, ?_⟩
    rw [padicValRat.mul (pow_ne_zero 2 hb) hnorm.ne_zero, padicValRat.pow,
      (padicValRat_eq_zero_iff hnorm.ne_zero).mpr hnorm, add_zero, heq, min_self]
    rfl
  · have hvals : padicValRat p (a ^ 2) ≠ padicValRat p (β * b ^ 2) := by
      rw [padicValRat.pow, padicValRat.mul hβ.ne_zero (pow_ne_zero 2 hb),
        hβval, zero_add, padicValRat.pow]
      exact fun h => heq (by omega)
    refine ⟨sub_ne_zero_of_val_ne hvals, ?_⟩
    rw [val_sub_eq_min (pow_ne_zero 2 ha) (mul_ne_zero hβ.ne_zero (pow_ne_zero 2 hb)) hvals,
      padicValRat.pow, padicValRat.mul hβ.ne_zero (pow_ne_zero 2 hb), hβval,
      zero_add, padicValRat.pow]
    norm_cast
    omega

/-- Nonsquare residue makes the rational norm form anisotropic. -/
theorem quadraticNorm_eq_zero_iff {β : ℚ}
    (hβ : IsPadicUnit p β) (hns : ¬ IsSquare (ratRes p β)) (a b : ℚ) :
    a ^ 2 - β * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  by_cases ha : a = 0
  · simp [ha, hβ.ne_zero]
  by_cases hb : b = 0
  · simp [hb, ha]
  exact iff_of_false (quadraticNorm_val hβ hns ha hb).1 (fun h => ha h.1)

/-- The norm is integral exactly when both coordinates are integral. -/
theorem quadraticNorm_integral_iff {β : ℚ}
    (hβ : IsPadicUnit p β) (hns : ¬ IsSquare (ratRes p β)) (a b : ℚ) :
    0 ≤ padicValRat p (a ^ 2 - β * b ^ 2) ↔
      0 ≤ padicValRat p a ∧ 0 ≤ padicValRat p b := by
  have hβval := (padicValRat_eq_zero_iff hβ.ne_zero).mpr hβ
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [ha, hb]
    rw [ha, zero_pow (by omega : 2 ≠ 0), zero_sub, padicValRat.neg,
      padicValRat.mul hβ.ne_zero (pow_ne_zero 2 hb), hβval, zero_add, padicValRat.pow,
      padicValRat.zero]
    norm_cast
    omega
  by_cases hb : b = 0
  · rw [hb, zero_pow (by omega : 2 ≠ 0), mul_zero, sub_zero,
      padicValRat.pow, padicValRat.zero]
    norm_cast
    omega
  rw [(quadraticNorm_val hβ hns ha hb).2]
  omega

/-- One square-denominator predicate tests two local integrality conditions. -/
theorem squareDenominator_quadraticNorm_iff {β : ℚ}
    (hβ : IsPadicUnit p β) (hns : ¬ IsSquare (ratRes p β)) (a b : ℚ) :
    SquareDenominator ((p : ℚ) * (a ^ 2 - β * b ^ 2) ^ 2) ↔
      0 ≤ padicValRat p a ∧ 0 ≤ padicValRat p b := by
  rw [squareDenominator_prime_mul_sq_iff, quadraticNorm_integral_iff hβ hns]

private theorem scaled_integral_iff (a : ℚ) (k : ℕ) :
    0 ≤ padicValRat p (a / (p : ℚ) ^ k) ↔
      a = 0 ∨ (k : ℤ) ≤ padicValRat p a := by
  by_cases ha : a = 0
  · simp [ha]
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicValRat.div ha (pow_ne_zero k hp), padicValRat.pow,
    padicValRat.self (Fact.out : p.Prime).one_lt, mul_one, or_iff_right ha]
  omega

/-- The same single predicate tests any common precision. Zero coordinates
satisfy every precision, as required by divisibility. -/
theorem squareDenominator_quadraticNorm_precision_iff {β : ℚ}
    (hβ : IsPadicUnit p β) (hns : ¬ IsSquare (ratRes p β)) (a b : ℚ) (k : ℕ) :
    SquareDenominator ((p : ℚ) * ((a ^ 2 - β * b ^ 2) / (p : ℚ) ^ (2 * k)) ^ 2) ↔
      (a = 0 ∨ (k : ℤ) ≤ padicValRat p a) ∧
        (b = 0 ∨ (k : ℤ) ≤ padicValRat p b) := by
  have hscale : (a ^ 2 - β * b ^ 2) / (p : ℚ) ^ (2 * k) =
      (a / (p : ℚ) ^ k) ^ 2 - β * (b / (p : ℚ) ^ k) ^ 2 := by
    rw [mul_comm 2 k, pow_mul, div_pow, div_pow]
    ring
  rw [hscale, squareDenominator_quadraticNorm_iff hβ hns,
    scaled_integral_iff, scaled_integral_iff]

#print axioms quadraticNorm_val
#print axioms quadraticNorm_eq_zero_iff
#print axioms squareDenominator_quadraticNorm_iff
#print axioms squareDenominator_quadraticNorm_precision_iff

end GaloisForLFunctions.HTGeometry.Arithmetic
