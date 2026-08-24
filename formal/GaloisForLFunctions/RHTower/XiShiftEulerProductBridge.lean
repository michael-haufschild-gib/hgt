import GaloisForLFunctions.RHTower.XiShiftEulerRegionIndex
import GaloisForLFunctions.RHTower.XiRealAxisGrowth
import GaloisForLFunctions.HTGeometry.ShiftedEulerLogChord

/-!
# Exact prime--archimedean factorization of the shifted-Xi quotient

On the literal Euler sampling half-plane, both shifted zeta arguments have
real part greater than one.  The completed-Xi quotient therefore factors
into an explicit polynomial--Gamma quotient and the exponential of an
absolutely convergent shifted Euler-log Dirichlet series.
-/

open Complex Set LSeries
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Polynomial--Gamma factor in the completed Xi function. -/
def eulerXiArchimedeanFactor (s : ℂ) : ℂ :=
  s * (s - 1) / 2 * Complex.Gammaℝ s

/-- Explicit archimedean quotient at the two shifted Euler arguments. -/
def eulerXiArchimedeanQuotient (omega : ℝ) (z : ℂ) : ℂ :=
  eulerXiArchimedeanFactor (1 / 2 - (omega : ℂ) - z * I) /
    eulerXiArchimedeanFactor (1 / 2 + (omega : ℂ) - z * I)

/-- Completed Xi is its explicit polynomial--Gamma factor times zeta on
`Re s > 1`. -/
theorem xi_eq_eulerXiArchimedeanFactor_mul_zeta_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    xi s = eulerXiArchimedeanFactor s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [xi_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_eq_Gammaℝ_mul (by linarith)]
  unfold eulerXiArchimedeanFactor
  ring

/-- The polynomial--Gamma factor has no zero on `Re s > 1`. -/
theorem eulerXiArchimedeanFactor_ne_zero
    {s : ℂ} (hs : 1 < s.re) : eulerXiArchimedeanFactor s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := sub_eq_zero.mp h
    rw [this] at hs
    norm_num at hs
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero hs0 hs1) (by norm_num))
    (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))

/-- Exact polynomial--Gamma times zeta-ratio factorization of the literal
shifted-Xi quotient throughout the Euler region. -/
theorem eulerXiShiftTheta_eq_archimedean_mul_zeta_ratio
    {omega : ℝ} (homega : 0 < omega)
    {z : ℂ} (hz : z ∈ xiShiftEulerUpperSet omega) :
    eulerXiShiftTheta omega z = eulerXiArchimedeanQuotient omega z *
      (riemannZeta (1 / 2 - (omega : ℂ) - z * I) /
        riemannZeta (1 / 2 + (omega : ℂ) - z * I)) := by
  have hm : 1 < (1 / 2 - (omega : ℂ) - z * I).re := by
    change 1 / 2 + omega < z.im at hz
    simp only [Complex.sub_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_num
    linarith
  have hp : 1 < (1 / 2 + (omega : ℂ) - z * I).re := by
    change 1 / 2 + omega < z.im at hz
    simp only [Complex.sub_re, Complex.add_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_num
    linarith
  rw [eulerXiShiftTheta_eq_suzukiCanonicalTheta,
    suzukiCanonicalTheta,
    xi_eq_eulerXiArchimedeanFactor_mul_zeta_of_one_lt_re hm,
    xi_eq_eulerXiArchimedeanFactor_mul_zeta_of_one_lt_re hp,
    eulerXiArchimedeanQuotient]
  field_simp [eulerXiArchimedeanFactor_ne_zero hp,
    riemannZeta_ne_zero_of_one_lt_re hp]

/-- The shifted Euler-log coefficient series is absolutely convergent at
every Euler-region sampling node. -/
theorem eulerXiShiftedEulerLogIncrement_summable
    {omega : ℝ} (homega : 0 < omega)
    {z : ℂ} (hz : z ∈ xiShiftEulerUpperSet omega) :
    LSeriesSummable (shiftedEulerLogIncrementCoeff (omega : ℂ))
      (1 / 2 - z * I) := by
  have hm : 1 < ((1 / 2 - z * I) - (omega : ℂ)).re := by
    change 1 / 2 + omega < z.im at hz
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    norm_num
    linarith
  have hp : 1 < ((1 / 2 - z * I) + (omega : ℂ)).re := by
    change 1 / 2 + omega < z.im at hz
    simp only [Complex.sub_re, Complex.add_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re]
    norm_num
    linarith
  rw [shiftedEulerLogIncrementCoeff]
  exact ((LSeriesSummable_powerTwist _ _ _).mpr
    (canonicalEulerLogZeta_summable hm)).sub
      ((LSeriesSummable_powerTwist _ _ _).mpr (by
        simpa only [sub_neg_eq_add] using
          canonicalEulerLogZeta_summable hp))

/-- Branch-free exact prime--archimedean formula: the shifted-Xi quotient is
the explicit archimedean quotient times the exponential of its absolutely
convergent shifted Euler-log series. -/
theorem eulerXiShiftTheta_eq_archimedean_mul_exp_eulerLog
    {omega : ℝ} (homega : 0 < omega)
    {z : ℂ} (hz : z ∈ xiShiftEulerUpperSet omega) :
    eulerXiShiftTheta omega z = eulerXiArchimedeanQuotient omega z *
      Complex.exp (LSeries (shiftedEulerLogIncrementCoeff (omega : ℂ))
        (1 / 2 - z * I)) := by
  have hm : 1 < ((1 / 2 - z * I) - (omega : ℂ)).re := by
    change 1 / 2 + omega < z.im at hz
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    norm_num
    linarith
  have hp : 1 < ((1 / 2 - z * I) + (omega : ℂ)).re := by
    change 1 / 2 + omega < z.im at hz
    simp only [Complex.sub_re, Complex.add_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re]
    norm_num
    linarith
  rw [eulerXiShiftTheta_eq_archimedean_mul_zeta_ratio homega hz]
  rw [exp_LSeries_shiftedEulerLogIncrementCoeff_eq_zeta_ratio hm hp]
  ring_nf

end
end RHTower
