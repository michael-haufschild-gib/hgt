import GaloisForLFunctions.RHTower.SelbergMaassFourierModes
import GaloisForLFunctions.RHTower.DeningerFourierBridge

/-!
# Physical mass and quarter-energy Parseval identities for Maass slices

The literal normalized Maass coefficient agrees with Mathlib's interval Fourier coefficient.
Continuity supplies square integrability on every finite horizontal period. Parseval therefore
identifies actual slice mass with squared coefficient mass. One integration by parts and the
actual height derivative identify the horizontal and vertical derivative energies as well.

Adding these convergent identities yields the physical horizontal quarter-energy integral as
its literal modal series. This is a fixed-positive-height identity; no interchange with an
infinite height integral, quotient-core cancellation, or Selberg conclusion is assumed.
-/

open MeasureTheory Set Filter UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassParseval
open SelbergMaassMean SelbergMaassFourier
open _root_.RHTower
noncomputable section

private theorem slice_memLp (w : ℝ) {F : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    MemLp (fun x : ℝ => F (point x y)) 2 (volume.restrict (Ioc 0 w)) := by
  have hc := slice_continuous hf hy
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := w)).exists_bound_of_continuousOn hc.continuousOn
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) w)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  apply MemLp.of_bound hc.aestronglyMeasurable.restrict M
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hM x ⟨hx.1.le, hx.2⟩

private theorem slice_normSq_intervalIntegrable (w : ℝ) {F : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    IntervalIntegrable (fun x : ℝ => Complex.normSq (F (point x y))) volume 0 w := by
  exact (Complex.continuous_normSq.comp (slice_continuous hf hy)).intervalIntegrable (0 : ℝ) w

/-- The literal normalized interval coefficient agrees with Mathlib's Fourier coefficient. -/
theorem coefficient_eq_fourierCoeffOn (w : ℝ) (hw : 0 < w) (F : ℂ → ℂ) (y : ℝ) (n : ℤ) :
    coefficient w n F y = fourierCoeffOn hw (fun x : ℝ => F (point x y)) n := by
  unfold coefficient deningerFourierCoeff
  rw [fourierCoeffOn_eq_integral, sub_zero]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [deningerFourierKernel_eq_fourier, smul_eq_mul]

/-- Physical slice mass is the sum of squared literal coefficient norms. -/
theorem coefficient_mass_hasSum (w : ℝ) (hw : 0 < w) {F : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => Complex.normSq (coefficient w n F y))
      (w⁻¹ * ∫ x in (0 : ℝ)..w, Complex.normSq (F (point x y))) := by
  have h := hasSum_sq_fourierCoeffOn hw (slice_memLp w hf hy)
  simpa only [← coefficient_eq_fourierCoeffOn w hw F y, Complex.normSq_eq_norm_sq,
    sub_zero, smul_eq_mul] using h

/-- One actual horizontal derivative multiplies the coefficient by its signed imaginary frequency. -/
theorem coefficient_horizontal (w : ℝ) (hw : 0 < w) (n : ℤ) {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    (hp : ∀ x, F (point (x + w) y) = F (point x y)) :
    coefficient w n (directional 1 F) y =
      ((signedFrequency w n : ℝ) : ℂ) * Complex.I * coefficient w n F y := by
  have hd := directional_contDiffOn hf (m := 0) (by simp) (1 : ℂ)
  have hper : F (point w y) = F (point 0 y) := by simpa only [zero_add] using hp 0
  have h := deningerFourierCoeff_deriv hw.ne' (slice_horizontal hf hy)
    (slice_continuous hd.continuousOn hy) hper n
  have hr : (2 * Real.pi * Complex.I * n) / (w : ℂ) =
      ((signedFrequency w n : ℝ) : ℂ) * Complex.I := by
    unfold signedFrequency
    push_cast
    ring
  rw [hr] at h
  exact h

/-- Parseval for the actual Maass slice mass, with the exact period normalization. -/
theorem maass_mass_hasSum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => Complex.normSq (maassCoefficient N f n y))
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
        Complex.normSq ((f.1.1 ∘ ofComplex) (point x y))) :=
  coefficient_mass_hasSum (N + 1 : ℕ) (by positivity) f.2.2.1.1.continuousOn hy

/-- Parseval for the actual horizontal derivative energy. -/
theorem maass_horizontal_hasSum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => signedFrequency (N + 1 : ℕ) n ^ (2 : ℕ) *
      Complex.normSq (maassCoefficient N f n y))
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
        Complex.normSq (directional 1 (f.1.1 ∘ ofComplex) (point x y))) := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hd := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hs := coefficient_mass_hasSum (N + 1 : ℕ) (by positivity) hd.continuousOn hy
  apply hs.congr_fun
  intro n
  rw [coefficient_horizontal (N + 1 : ℕ) (by positivity) n
    (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy (fun x => maass_periodic N f x hy)]
  simp [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I, maassCoefficient, F, pow_two]

/-- Parseval for the actual height derivative energy. -/
theorem maass_vertical_hasSum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => Complex.normSq (deriv (maassCoefficient N f n) y))
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
        Complex.normSq (directional Complex.I (f.1.1 ∘ ofComplex) (point x y))) := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hd := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  have hs := coefficient_mass_hasSum (N + 1 : ℕ) (by positivity) hd.continuousOn hy
  apply hs.congr_fun
  intro n
  change Complex.normSq (deriv (coefficient (N + 1 : ℕ) n F) y) = _
  rw [(coefficient_hasDerivAt (N + 1 : ℕ) (by positivity) n
    (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy).deriv]

/-- The actual horizontal integral of Dirichlet energy minus quarter hyperbolic mass. -/
def quarterSlice (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(N + 1 : ℕ),
    Complex.normSq (directional 1 (f.1.1 ∘ ofComplex) (point x y)) +
    Complex.normSq (directional Complex.I (f.1.1 ∘ ofComplex) (point x y)) -
    (1 / (4 * y ^ (2 : ℕ))) * Complex.normSq ((f.1.1 ∘ ofComplex) (point x y))

/-- The corresponding literal modal energy at a fixed positive height. -/
def modalQuarter (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (y : ℝ) (n : ℤ) : ℝ :=
  Complex.normSq (deriv (maassCoefficient N f n) y) +
    (signedFrequency (N + 1 : ℕ) n ^ (2 : ℕ) - 1 / (4 * y ^ (2 : ℕ))) * Complex.normSq (maassCoefficient N f n y)

/-- The modal quarter-energy series converges to the normalized physical slice energy. -/
theorem maass_quarter_hasSum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasSum (modalQuarter N f y) (((N + 1 : ℕ) : ℝ)⁻¹ * quarterSlice N f y) := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hd1 := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdI := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  have hi1 := slice_normSq_intervalIntegrable (N + 1 : ℕ) hd1.continuousOn hy
  have hiI := slice_normSq_intervalIntegrable (N + 1 : ℕ) hdI.continuousOn hy
  have hi0 := slice_normSq_intervalIntegrable (N + 1 : ℕ) hf.continuousOn hy
  have hs := ((maass_horizontal_hasSum N f hy).add (maass_vertical_hasSum N f hy)).sub
    ((maass_mass_hasSum N f hy).mul_left (1 / (4 * y ^ (2 : ℕ))))
  have he :
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
        Complex.normSq (directional 1 F (point x y))) +
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
        Complex.normSq (directional Complex.I F (point x y))) -
      (1 / (4 * y ^ (2 : ℕ))) * (((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
        Complex.normSq (F (point x y))) =
      (((N + 1 : ℕ) : ℝ)⁻¹ * quarterSlice N f y) := by
    unfold quarterSlice
    change _ = ((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
      Complex.normSq (directional 1 F (point x y)) +
      Complex.normSq (directional Complex.I F (point x y)) -
      (1 / (4 * y ^ (2 : ℕ))) * Complex.normSq (F (point x y))
    rw [intervalIntegral.integral_sub (hi1.add hiI) (hi0.const_mul _),
      intervalIntegral.integral_add hi1 hiI, intervalIntegral.integral_const_mul]
    ring
  change HasSum _ (_ + _ - _) at hs
  rw [he] at hs
  apply hs.congr_fun
  intro n
  unfold modalQuarter
  ring

/-- The actual physical quarter-energy slice equals its literal modal sum times the period. -/
theorem maass_quarter_energy_identity (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    quarterSlice N f y = (N + 1 : ℕ) * ∑' n : ℤ, modalQuarter N f y n := by
  rw [(maass_quarter_hasSum N f hy).tsum_eq]
  field_simp

end
end GaloisForLFunctions.RHTower.SelbergMaassParseval
