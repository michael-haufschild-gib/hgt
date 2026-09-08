import GaloisForLFunctions.RHTower.SelbergMaassCuspDecay

/-!
# Finite physical Maass tail energy and exact infinite-height Green balance

The actual flux derivative dominates a positive multiple of mass above the
explicit frequency cutoff and is integrable there. This proves integrability of
physical mass; division by height squared gives hyperbolic mass integrability.
Local source regularity extends the tail statements to every positive height.

The source PDE now gives integrable gradient and quarter-energy slices. The
terminal flux is proved to vanish, so the infinite-height identities retain only
the actual lower flux and the literal hyperbolic mass integral. No assumed decay
rate, discarded boundary term, or height/Fourier interchange is used.

The quotient-core estimate and the global Selberg quarter bound remain unproved.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassTailEnergy
open SelbergMaassMean SelbergMaassFlux SelbergMaassCuspDecay SelbergMaassParseval
noncomputable section

private theorem mass_continuousOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ContinuousOn (mass N f) (Ioi 0) := by
  intro y hy
  exact (mass_hasDerivAt N f hy).continuousAt.continuousWithinAt

private theorem hyperbolicMass_continuousOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ContinuousOn (fun y => mass N f y / y ^ 2) (Ioi 0) :=
  (mass_continuousOn N f).div (continuous_id.pow 2).continuousOn
    (fun _ hy => (sq_pos_of_pos hy).ne')

/-- Actual C² chart regularity makes physical derivative energy continuous at positive heights. -/
theorem gradientEnergy_continuousOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ContinuousOn (gradientEnergy N f) (Ioi 0) := by
  have hf := f.2.2.1.1
  have hd1 := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdI := directional_contDiffOn hf (m := 1) le_rfl Complex.I
  intro y hy
  exact (((pairing_hasDerivAt (N + 1 : ℕ) hd1 hd1 hy).continuousAt.add
    (pairing_hasDerivAt (N + 1 : ℕ) hdI hdI hy).continuousAt).const_mul
      ((N + 1 : ℕ) : ℝ)⁻¹).continuousWithinAt

private theorem flux_deriv_continuousOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ContinuousOn (deriv (flux N f)) (Ioi 0) := by
  apply ((gradientEnergy_continuousOn N f).sub
    ((hyperbolicMass_continuousOn N f).const_mul lam)).congr
  intro y hy
  rw [(flux_hasDerivAt N f hy).deriv]
  simp only [Pi.sub_apply]
  ring

private theorem extend_integrable_tail {g : ℝ → ℝ} (hc : ContinuousOn g (Ioi 0))
    {a Y : ℝ} (hY : 0 < Y) (hi : IntegrableOn g (Ioi a)) :
    IntegrableOn g (Ioi Y) := by
  by_cases haY : a ≤ Y
  · exact hi.mono_set (Ioi_subset_Ioi haY)
  · have hYa : Y ≤ a := (lt_of_not_ge haY).le
    rw [← Ioc_union_Ioi_eq_Ioi hYa]
    apply IntegrableOn.union ?_ hi
    apply IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    exact hc.mono (fun y hy => hY.trans_le hy.1)

private theorem mass_cutoff_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    IntegrableOn (mass N f) (Ioi (cutoff N)) := by
  have hi := (flux_deriv_integrable N lam f).const_mul (2 / rate N ^ 2)
  apply hi.mono' (((mass_continuousOn N f).mono
    (Ioi_subset_Ioi (cutoff_pos N).le)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mass_nonneg N f ((cutoff_pos N).trans hy))]
  calc
    mass N f y = (2 / rate N ^ 2) * (rate N ^ 2 / 2 * mass N f y) := by
      field_simp [(rate_pos N).ne']
    _ ≤ (2 / rate N ^ 2) * deriv (flux N f) y :=
      mul_le_mul_of_nonneg_left (flux_deriv_lower N lam f hy.le) (by positivity)

/-- Actual exceptional Maass mass is integrable above every positive height. -/
theorem mass_tail_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) : IntegrableOn (mass N f) (Ioi Y) :=
  extend_integrable_tail (mass_continuousOn N f) hY (mass_cutoff_integrable N lam f)

/-- Actual hyperbolic cusp mass is finite above every positive height. -/
theorem hyperbolicMass_tail_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) : IntegrableOn (fun y => mass N f y / y ^ 2) (Ioi Y) := by
  have hi := (mass_tail_integrable N lam f hY).const_mul (1 / Y ^ 2)
  apply hi.mono' (((hyperbolicMass_continuousOn N f).mono
    (Ioi_subset_Ioi hY.le)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hmass := mass_nonneg N f (hY.trans hy)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hmass (sq_nonneg _))]
  calc
    mass N f y / y ^ 2 ≤ mass N f y / Y ^ 2 := by
      apply div_le_div_of_nonneg_left hmass (sq_pos_of_pos hY)
      have hYy : Y ≤ y := hy.le
      nlinarith [sq_nonneg (y - Y), mul_nonneg hY.le (sub_nonneg.mpr hYy)]
    _ = (1 / Y ^ 2) * mass N f y := by ring

/-- The actual flux derivative is integrable above every positive height. -/
theorem flux_deriv_tail_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) : IntegrableOn (deriv (flux N f)) (Ioi Y) :=
  extend_integrable_tail (flux_deriv_continuousOn N f) hY (flux_deriv_integrable N lam f)

/-- Infinite-height fundamental theorem with the actual terminal flux proved to vanish. -/
theorem flux_tail_integral (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) :
    ∫ y in Ioi Y, deriv (flux N f) y = -flux N f Y := by
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => (flux_hasDerivAt N f (hY.trans_le hy)).differentiableAt.hasDerivAt)
    (flux_deriv_tail_integrable N lam f hY) (flux_decay N lam f)

/-- Both actual physical derivative energies have finite combined tail integral. -/
theorem gradientEnergy_tail_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) : IntegrableOn (gradientEnergy N f) (Ioi Y) := by
  apply ((flux_deriv_tail_integrable N lam f hY).add
    ((hyperbolicMass_tail_integrable N lam f hY).const_mul (lam : ℝ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [Pi.add_apply]
  rw [(flux_hasDerivAt N f (hY.trans hy)).deriv]
  ring

/-- The signed actual physical quarter-energy slice is integrable on the infinite cusp. -/
theorem quarterSlice_tail_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) : IntegrableOn (quarterSlice N f) (Ioi Y) := by
  apply (((flux_deriv_tail_integrable N lam f hY).add
    ((hyperbolicMass_tail_integrable N lam f hY).const_mul ((lam : ℝ) - 1 / 4))).const_mul
      ((N + 1 : ℕ) : ℝ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have h := quarterSlice_eq_flux_deriv N f (hY.trans hy)
  have he : deriv (flux N f) y + ((lam : ℝ) - 1 / 4) * (mass N f y / y ^ 2) =
      ((N + 1 : ℕ) : ℝ)⁻¹ * quarterSlice N f y := by
    rw [h]
    ring
  change ((N + 1 : ℕ) : ℝ) * _ = _
  simp only [Pi.add_apply]
  rw [he]
  field_simp

/-- Exact physical tail energy equals lower outgoing flux plus spectral hyperbolic mass. -/
theorem gradientEnergy_tail_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) :
    ∫ y in Ioi Y, gradientEnergy N f y =
      -flux N f Y + (lam : ℝ) * ∫ y in Ioi Y, mass N f y / y ^ 2 := by
  have he : ∀ᵐ y ∂volume.restrict (Ioi Y), gradientEnergy N f y =
      deriv (flux N f) y + (lam : ℝ) * (mass N f y / y ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [(flux_hasDerivAt N f (hY.trans hy)).deriv]
    ring
  rw [integral_congr_ae he, integral_add (flux_deriv_tail_integrable N lam f hY)
    ((hyperbolicMass_tail_integrable N lam f hY).const_mul (lam : ℝ)),
    integral_const_mul, flux_tail_integral N lam f hY]

/-- Exact physical quarter-energy tail balance, with no unproved terminal boundary value. -/
theorem quarterSlice_tail_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) :
    ((N + 1 : ℕ) : ℝ)⁻¹ * ∫ y in Ioi Y, quarterSlice N f y =
      -flux N f Y + ((lam : ℝ) - 1 / 4) * ∫ y in Ioi Y, mass N f y / y ^ 2 := by
  have he : ∀ᵐ y ∂volume.restrict (Ioi Y),
      ((N + 1 : ℕ) : ℝ)⁻¹ * quarterSlice N f y =
      deriv (flux N f) y + ((lam : ℝ) - 1 / 4) * (mass N f y / y ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [quarterSlice_eq_flux_deriv N f (hY.trans hy)]
    ring
  rw [← integral_const_mul, integral_congr_ae he,
    integral_add (flux_deriv_tail_integrable N lam f hY)
      ((hyperbolicMass_tail_integrable N lam f hY).const_mul ((lam : ℝ) - 1 / 4)),
    integral_const_mul, flux_tail_integral N lam f hY]

end
end GaloisForLFunctions.RHTower.SelbergMaassTailEnergy
