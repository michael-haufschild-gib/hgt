import GaloisForLFunctions.RHTower.EisensteinHeckeSecondMoment

/-!
# Hecke operators are two shifts on the resonant cutoff family

At a resonance the constant term has one Weyl power. The two branches of `T_p`
therefore change its cutoff to `pY` and `Y/p`. Multiplication by `Y^u` absorbs
the coefficients, giving the sum of two translations in logarithmic height.
-/

open Complex UpperHalfPlane
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- The exact Hecke action on the entire cutoff family of a resonant state. -/
theorem hecke_cutoff_shifts {p : ℕ} (hp : p.Prime) {u : ℂ} (hAu : msA u = 0)
    (Y : ℝ) (z : ℍ) :
    heckeTruncated p u Y z =
      (p : ℂ) ^ u * truncatedLineModel u (Y * p) z +
        (p : ℂ) ^ (-u) * truncatedLineModel u (Y / p) z := by
  have hupper := weyl_scalar_identity hp.pos u false
  rw [weylExponent_false, sqrt_inv_mul_cpow_half_sub hp.pos] at hupper
  have hupper' : (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (p : ℂ) *
      ((p : ℂ) ^ ((1 : ℂ) / 2 - u))⁻¹ = (p : ℂ) ^ u := by
    linear_combination hupper
  rw [heckeTruncated_eq hp]
  unfold heckeRemainder weylRemainderTerm truncatedLineModel
  rw [constantCoefficient_false, constantCoefficient_true, hAu, weylExponent_false,
    sqrt_inv_mul_cpow_half_sub hp.pos, hupper', cuspConstantPart_eq_msAB, hAu]
  simp only [zero_mul, add_zero]
  split_ifs <;> ring

/-- Complex normalization makes each Hecke action a coefficient-free pair of height shifts. -/
theorem normalized_hecke_cutoff_shifts {p : ℕ} (hp : p.Prime) {u : ℂ}
    (hAu : msA u = 0) {Y : ℝ} (hY : 0 < Y) (z : ℍ) :
    (Y : ℂ) ^ u * heckeTruncated p u Y z =
      ((Y * p : ℝ) : ℂ) ^ u * truncatedLineModel u (Y * p) z +
        ((Y / p : ℝ) : ℂ) ^ u * truncatedLineModel u (Y / p) z := by
  rw [hecke_cutoff_shifts hp hAu]
  have hm := natCast_mul_ofReal_cpow p hY.le u
  have hd := ofReal_div_natCast_cpow_eisensteinHeckeMaassSelberg p hY.le u
  push_cast
  rw [mul_comm (Y : ℂ) (p : ℂ), hm, hd, Complex.cpow_neg]
  ring

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
