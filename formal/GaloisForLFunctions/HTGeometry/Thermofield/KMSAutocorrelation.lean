import GaloisForLFunctions.HTGeometry.IntervalIntegralHolderSwap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# KMS kernels and their integrated squared correlations

The KMS kernel at spectral gap `2x` is `cosh (x(1-2u)) / cosh x`.
The autocorrelation argument of Manai--Warzel, arXiv:2608.23177,
admits the stronger bound `q(1+q)/2`: the estimate `|sinh x| ≥ |x|`
retains a factor of one half in the quadratic term. Cauchy--Schwarz
transfers the scalar estimate to distinct spectral gaps.
-/

noncomputable section
open MeasureTheory intervalIntegral
namespace GaloisForLFunctions.HTGeometry.Thermofield

/-- The normalized imaginary-time KMS kernel at spectral gap `2x`. -/
def kmsKernel (x u : ℝ) : ℝ := Real.cosh (x * (1-2*u)) / Real.cosh x

/-- The integrated KMS kernel, with its continuous value at zero gap. -/
def kmsMean (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / (x * Real.cosh x)

theorem continuous_kmsKernel (x : ℝ) : Continuous (kmsKernel x) := by
  unfold kmsKernel
  fun_prop

theorem kmsKernel_pos (x u : ℝ) : 0 < kmsKernel x u :=
  div_pos (Real.cosh_pos _) (Real.cosh_pos _)

private theorem integral_cosh_affine_mul (x : ℝ) :
    x * (∫ u in (0:ℝ)..1, Real.cosh (x * (1-2*u))) = Real.sinh x := by
  have hd (u : ℝ) : HasDerivAt (fun v => -Real.sinh (x * (1-2*v)) / 2)
      (x * Real.cosh (x * (1-2*u))) u := by
    convert (((((hasDerivAt_const u (1:ℝ)).sub
      ((hasDerivAt_id u).const_mul 2)).const_mul x).sinh).neg.div_const 2) using 1 <;> ring
  have hi : IntervalIntegrable (fun u => x * Real.cosh (x * (1-2*u))) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
  rw [integral_const_mul] at h
  simp only [mul_zero, sub_zero, mul_one, show (1:ℝ)-2*1 = -1 by ring,
    mul_neg_one, Real.sinh_neg, neg_neg] at h
  linarith only [h]

/-- The susceptibility of a single KMS spectral gap. -/
theorem integral_kmsKernel (x : ℝ) :
    (∫ u in (0:ℝ)..1, kmsKernel x u) = kmsMean x := by
  by_cases hx : x = 0
  · subst x
    simp [kmsKernel, kmsMean]
  · rw [kmsMean, if_neg hx, kmsKernel, integral_div]
    have h := integral_cosh_affine_mul x
    apply (eq_div_iff (mul_ne_zero hx (Real.cosh_pos x).ne')).mpr
    field_simp [(Real.cosh_pos x).ne']
    nlinarith only [h]

theorem kmsMean_nonneg (x : ℝ) : 0 ≤ kmsMean x := by
  rw [← integral_kmsKernel]
  exact integral_nonneg zero_le_one (fun u _ => (kmsKernel_pos x u).le)

/-- Exact single-gap square integral. -/
theorem integral_kmsKernel_sq (x : ℝ) :
    (∫ u in (0:ℝ)..1, kmsKernel x u ^ 2) =
      kmsMean x / 2 + 1 / (2 * Real.cosh x ^ 2) := by
  by_cases hx : x = 0
  · subst x
    norm_num [kmsKernel, kmsMean]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hpoint (u : ℝ) : kmsKernel x u ^ 2 =
      (Real.cosh ((2*x) * (1-2*u)) + 1) / (2 * Real.cosh x ^ 2) := by
    have h := Real.cosh_two_mul (x * (1-2*u))
    have h' := Real.cosh_sq_sub_sinh_sq (x * (1-2*u))
    rw [show 2 * (x * (1-2*u)) = (2*x)*(1-2*u) by ring] at h
    dsimp [kmsKernel]
    field_simp
    nlinarith only [h, h']
  simp_rw [hpoint]
  rw [integral_div, integral_add
    ((by fun_prop : Continuous (fun u : ℝ => Real.cosh ((2*x)*(1-2*u)))).intervalIntegrable _ _)
    intervalIntegrable_const, integral_const]
  have h := integral_cosh_affine_mul (2*x)
  rw [Real.sinh_two_mul] at h
  rw [kmsMean, if_neg hx]
  simp only [sub_zero, smul_eq_mul, one_mul]
  field_simp
  nlinarith only [h]

/-- The endpoint attenuation is bounded by the square of the susceptibility. -/
theorem kms_sech_sq_le_mean_sq (x : ℝ) :
    1 / Real.cosh x ^ 2 ≤ kmsMean x ^ 2 := by
  by_cases hx : x = 0
  · subst x
    norm_num [kmsMean]
  have hs : x^2 ≤ Real.sinh x ^ 2 := by
    rw [sq_le_sq, Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg x)
  rw [kmsMean, if_neg hx, div_pow, mul_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos (Real.cosh_pos x))
    (mul_pos (sq_pos_of_ne_zero hx) (sq_pos_of_pos (Real.cosh_pos x)))).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg (Real.cosh x))]

/-- The sharp quadratic coefficient furnished by the single-gap calculation. -/
theorem integral_kmsKernel_sq_le (x : ℝ) :
    (∫ u in (0:ℝ)..1, kmsKernel x u ^ 2) ≤
      kmsMean x / 2 + kmsMean x ^ 2 / 2 := by
  rw [integral_kmsKernel_sq]
  have h := kms_sech_sq_le_mean_sq x
  have he : 1 / (2 * Real.cosh x ^ 2) = (1 / Real.cosh x ^ 2) / 2 := by ring
  rw [he]
  linarith only [h]

/-- Mixed KMS correlations retain the improved quadratic coefficient. -/
theorem integral_kmsKernel_mul_le (x y : ℝ) :
    (∫ u in (0:ℝ)..1, kmsKernel x u * kmsKernel y u) ≤
      (kmsMean x + kmsMean y) / 4 + kmsMean x * kmsMean y / 2 := by
  have hcs := sq_intervalIntegral_mul_le zero_le_one
    (continuous_kmsKernel x) (continuous_kmsKernel y)
  have hx := integral_kmsKernel_sq_le x
  have hy := integral_kmsKernel_sq_le y
  have hprod := mul_le_mul hx hy
    (integral_nonneg zero_le_one (fun u _ => sq_nonneg (kmsKernel y u)))
    (by have := kmsMean_nonneg x; positivity)
  have hupper : 0 ≤ (kmsMean x + kmsMean y) / 4 + kmsMean x * kmsMean y / 2 := by
    have := kmsMean_nonneg x
    have := kmsMean_nonneg y
    positivity
  have hid : ((kmsMean x + kmsMean y) / 4 + kmsMean x * kmsMean y / 2)^2 -
      (kmsMean x / 2 + kmsMean x^2 / 2) *
        (kmsMean y / 2 + kmsMean y^2 / 2) = (kmsMean x-kmsMean y)^2 / 16 := by ring
  have hsquare : (∫ u in (0:ℝ)..1, kmsKernel x u * kmsKernel y u)^2 ≤
      ((kmsMean x + kmsMean y) / 4 + kmsMean x * kmsMean y / 2)^2 := by
    nlinarith only [hcs, hprod, hid, sq_nonneg (kmsMean x-kmsMean y)]
  exact (sq_le_sq₀
    (integral_nonneg zero_le_one (fun u _ =>
      mul_nonneg (kmsKernel_pos x u).le (kmsKernel_pos y u).le)) hupper).mp hsquare

end GaloisForLFunctions.HTGeometry.Thermofield
