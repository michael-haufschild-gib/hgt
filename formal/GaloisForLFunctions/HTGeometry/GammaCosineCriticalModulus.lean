import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The zeta functional-equation factor has modulus one on the critical line

The factor `χ(s) = 2 (2π)^{s−1} Γ(1−s) cos(π(1−s)/2)` in `ζ(s) = χ(s) ζ(1−s)` has unit modulus on
`Re s = 1/2`.  With `a = 1 − s = 1/2 − iy`: `|Γ(a)|² = Γ(a)Γ(1−a) = π/sin(πa) = π/cosh(πy)` by the
reflection formula and conjugation symmetry, `|cos(πa/2)|² = (cos(π/2) + cosh(πy))/2 = cosh(πy)/2` by the
product-to-sum identity, and `|(2π)^{−a}| = (2π)^{−1/2}`; the product is `4 · (2π)^{−1} · π/cosh · cosh/2 = 1`.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- `|Γ(1/2 − iy)|² = π / cosh(πy)`. -/
theorem normSq_Gamma_half_sub_mul_I (y : ℝ) :
    Complex.normSq (Complex.Gamma ((1 / 2 : ℂ) - (y : ℂ) * I)) = Real.pi / Real.cosh (Real.pi * y) := by
  set a : ℂ := (1 / 2 : ℂ) - (y : ℂ) * I with ha
  have hconj : (starRingEnd ℂ) a = 1 - a := by
    apply Complex.ext
    · simp [ha]; norm_num
    · simp [ha]
  have hsin : Complex.sin ((Real.pi : ℂ) * a) = (Real.cosh (Real.pi * y) : ℂ) := by
    rw [show (Real.pi : ℂ) * a = (Real.pi : ℂ) / 2 - ((Real.pi * y : ℝ) : ℂ) * I by
        rw [ha]; push_cast; ring,
      Complex.sin_pi_div_two_sub, Complex.cos_mul_I, Complex.ofReal_cosh]
  have hcosh : (0 : ℝ) < Real.cosh (Real.pi * y) := Real.cosh_pos _
  have hkey : ((Complex.normSq (Complex.Gamma a) : ℝ) : ℂ)
      = ((Real.pi / Real.cosh (Real.pi * y) : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, ← Complex.Gamma_conj, hconj, Complex.Gamma_mul_Gamma_one_sub, hsin]
    push_cast
    rfl
  exact_mod_cast hkey

/-- `|cos(π(1/2 − iy)/2)|² = cosh(πy) / 2`. -/
theorem normSq_cos_pi_mul_half_sub_mul_I_div_two (y : ℝ) :
    Complex.normSq (Complex.cos ((Real.pi : ℂ) * ((1 / 2 : ℂ) - (y : ℂ) * I) / 2))
      = Real.cosh (Real.pi * y) / 2 := by
  set w : ℂ := (Real.pi : ℂ) * ((1 / 2 : ℂ) - (y : ℂ) * I) / 2 with hw
  have hw' : w = ((Real.pi / 4 : ℝ) : ℂ) - ((Real.pi * y / 2 : ℝ) : ℂ) * I := by
    rw [hw]; push_cast; ring
  have hconjw : (starRingEnd ℂ) w = (Real.pi : ℂ) / 2 - w := by
    rw [hw', map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  -- product-to-sum: `cos w · cos w̄ = (cos(w + w̄) + cos(w − w̄))/2`
  have hprod : Complex.cos w * Complex.cos ((starRingEnd ℂ) w)
      = (Complex.cos (w + (starRingEnd ℂ) w) + Complex.cos (w - (starRingEnd ℂ) w)) / 2 := by
    rw [Complex.cos_add, Complex.cos_sub]; ring
  have hsum : w + (starRingEnd ℂ) w = (Real.pi : ℂ) / 2 := by rw [hconjw]; ring
  have hdiff : w - (starRingEnd ℂ) w = -(((Real.pi * y : ℝ) : ℂ) * I) := by
    rw [hconjw, hw]; push_cast; ring
  have hkey : ((Complex.normSq (Complex.cos w) : ℝ) : ℂ)
      = ((Real.cosh (Real.pi * y) / 2 : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, ← Complex.cos_conj, hprod, hsum, hdiff, Complex.cos_pi_div_two,
      Complex.cos_neg, Complex.cos_mul_I]
    push_cast
    ring
  exact_mod_cast hkey

/-- **Unit modulus of the zeta functional factor on the critical line.**
`‖2 (2π)^{−(1/2 − iy)} Γ(1/2 − iy) cos(π(1/2 − iy)/2)‖ = 1`. -/
theorem norm_zetaFunctionalFactor_critical (y : ℝ) :
    ‖(2 : ℂ) * ((2 * Real.pi : ℝ) : ℂ) ^ (-((1 / 2 : ℂ) - (y : ℂ) * I)) *
        Complex.Gamma ((1 / 2 : ℂ) - (y : ℂ) * I) *
        Complex.cos ((Real.pi : ℂ) * ((1 / 2 : ℂ) - (y : ℂ) * I) / 2)‖ = 1 := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcosh : (0 : ℝ) < Real.cosh (Real.pi * y) := Real.cosh_pos _
  have hpow : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-((1 / 2 : ℂ) - (y : ℂ) * I))‖
      = (2 * Real.pi) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h2π]
    congr 1; simp
  have hsq : ‖(2 : ℂ) * ((2 * Real.pi : ℝ) : ℂ) ^ (-((1 / 2 : ℂ) - (y : ℂ) * I)) *
        Complex.Gamma ((1 / 2 : ℂ) - (y : ℂ) * I) *
        Complex.cos ((Real.pi : ℂ) * ((1 / 2 : ℂ) - (y : ℂ) * I) / 2)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul,
      normSq_Gamma_half_sub_mul_I, normSq_cos_pi_mul_half_sub_mul_I_div_two,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hpow]
    have hp : ((2 * Real.pi) ^ (-(1 / 2 : ℝ))) ^ 2 = (2 * Real.pi)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2π.le,
        show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    rw [hp]
    simp only [Complex.norm_ofNat]
    field_simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp hsq

end GaloisForLFunctions.HTGeometry
