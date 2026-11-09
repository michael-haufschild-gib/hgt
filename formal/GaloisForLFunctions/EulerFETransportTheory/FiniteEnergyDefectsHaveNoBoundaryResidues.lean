import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsObeyTheTentIdentity
import GaloisForLFunctions.ExactEventTheory.IntegrableDefectsVanishInTheUnitGap

/-!
# Finite-energy defects carry no radial boundary residue

The half-line Laplace bound is uniform in height and grows only as the inverse
square root of the distance to the boundary. Multiplication by that distance
therefore removes every radial residue.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower.HamburgerStability
open GaloisForLFunctions.ExactEventTheory GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Uniform square-root control at every height of the actual defect transform. -/
theorem norm_mul_finiteEnergy_defectLaplace_le {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    ‖(ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I)‖ ≤
      rayL2Norm (defectMellinSource (hg.toLp g)) * Real.sqrt (2 * ε) / 2 := by
  let z : ℂ := (ε : ℂ) + (y : ℂ) * I
  have hz : 0 < z.re := by simpa only [z, Complex.add_re, Complex.ofReal_re,
    Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero] using hε
  have hb : ‖defectLaplace g z‖ ≤
      rayL2Norm (defectMellinSource (hg.toLp g)) / Real.sqrt (2 * ε) := by
    rw [← defectLaplace_congr_ae hg.coeFn_toLp z,
      defectLaplace_eq_laplaceRay (hg.toLp g) hz]
    simpa only [z, Complex.add_re, Complex.ofReal_re,
      Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero] using
      norm_laplaceRay_le (Lp.memLp (defectMellinSource (hg.toLp g))) hz
  have hr : ε / Real.sqrt (2 * ε) = Real.sqrt (2 * ε) / 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * ε by positivity)
    apply (div_eq_div_iff (Real.sqrt_pos.mpr (by positivity)).ne' two_ne_zero).mpr
    nlinarith only [hs]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  calc
    ε * ‖defectLaplace g z‖ ≤
        ε * (rayL2Norm (defectMellinSource (hg.toLp g)) / Real.sqrt (2 * ε)) :=
      mul_le_mul_of_nonneg_left hb hε.le
    _ = rayL2Norm (defectMellinSource (hg.toLp g)) * (ε / Real.sqrt (2 * ε)) := by ring
    _ = _ := by rw [hr]; ring

/-- No finite-energy defect changes any radial residue on the imaginary axis. -/
theorem tendsto_mul_finiteEnergy_defectLaplace {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (y : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm'
    (a := fun ε : ℝ => rayL2Norm (defectMellinSource (hg.toLp g)) *
      Real.sqrt (2 * ε) / 2)
  · exact eventually_nhdsWithin_of_forall fun ε hε =>
      norm_mul_finiteEnergy_defectLaplace_le hg hε y
  · have hc : Continuous (fun ε : ℝ => rayL2Norm (defectMellinSource (hg.toLp g)) *
        Real.sqrt (2 * ε) / 2) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

/-- Reality of the measure forces reality of the pole, because the defect has no radial residue. -/
theorem measure_pole_real_of_finiteEnergy_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    (β.re : ℂ) = β := by
  have hreal (ε : ℝ) : (measureSeries ν (ε : ℂ)).im = 0 ∧
      (measureDual ν (ε : ℂ)).im = 0 := by
    have hs := congrArg Complex.im (measureSeries_conj ν (ε : ℂ))
    have hd := congrArg Complex.im (measureDual_conj ν (ε : ℂ))
    simp only [Complex.conj_ofReal, Complex.conj_im] at hs hd
    constructor <;> linarith only [hs, hd]
  have hlim := (Complex.continuous_im.tendsto _).comp
    (tendsto_mul_finiteEnergy_defectLaplace hg 0)
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.zero_im] at hlim
  change Tendsto (fun ε : ℝ => ((ε : ℂ) * defectLaplace g (ε : ℂ)).im)
    (𝓝[>] 0) (𝓝 0) at hlim
  simp only [Complex.im_ofReal_mul] at hlim
  have hid : ∀ ε : ℝ, 0 < ε →
      ε * (defectLaplace g (ε : ℂ)).im = β.im / Real.pi - ε * β.im := by
    intro ε hε
    have hh := congrArg Complex.im
      (measureSeries_eq_of_theta_defect hsupp hmom hgm hgb hθ
        (show 0 < (ε : ℂ).re from hε))
    rw [show (Real.pi : ℂ) * (ε : ℂ) = ((Real.pi * ε : ℝ) : ℂ) by push_cast; rfl] at hh
    simp only [Complex.add_im, Complex.div_ofReal_im, Complex.neg_im,
      (hreal ε).1, (hreal ε).2, zero_add] at hh
    field_simp [Real.pi_ne_zero, ne_of_gt hε] at hh ⊢
    nlinarith only [hh]
  have hother : Tendsto (fun ε : ℝ => β.im / Real.pi - ε * β.im)
      (𝓝[>] 0) (𝓝 (β.im / Real.pi)) := by
    have hc : Continuous (fun ε : ℝ => β.im / Real.pi - ε * β.im) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun ε : ℝ => β.im / Real.pi - ε * β.im)
      (𝓝[>] 0) (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hid ε hε
  have hi := (div_eq_zero_iff.mp (tendsto_nhds_unique hother hzero)).resolve_right Real.pi_ne_zero
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hi.symm

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.norm_mul_finiteEnergy_defectLaplace_le
#print axioms GaloisForLFunctions.EulerFETransportTheory.tendsto_mul_finiteEnergy_defectLaplace
#print axioms GaloisForLFunctions.EulerFETransportTheory.measure_pole_real_of_finiteEnergy_theta_defect
