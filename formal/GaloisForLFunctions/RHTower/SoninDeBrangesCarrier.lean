/-
Half-plane holomorphy of the completed Sonin transform: the two de Branges bricks.

On the Sonin carrier the completed multiplicative transform

`M̌(f)(z) = 2 Γ_ℝ(z) ∫_{t>0} f(t) t^{-z} dt`

is absolutely convergent and holomorphic on the physical half-plane `Re z > 1/2`: the support
gap of the carrier pairs `f` against a square-integrable power kernel by Cauchy--Schwarz, and
a pure-power dominant — the logarithm is absorbed by `|log t| ≤ δ⁻¹(t^δ + t^{-δ})` — controls
the derivative of the integrand locally uniformly. Applying the same brick to the Fourier
transform of a carrier element and reflecting the variable `z ↦ 1-z` gives holomorphy of the
dual transform on the Fourier half-plane `Re z < 1/2`.

These are the two polarized halves of the entire-function carrier of the Sonin space: every
carrier element has a holomorphic completed transform on each of the two open half-planes cut
by the critical line. The remaining de Branges weld glues the two halves across the critical
line into a single entire function.
-/
import GaloisForLFunctions.RHTower.HardyTitchmarshSemilocalSquare
import Mathlib.Analysis.MellinTransform
import GaloisForLFunctions.RHTower.GammaRealHalfPlane

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace RHTower

/-! ### Support extraction from the Sonin constraints -/

theorem indicator_ae_zero_of_mem_physicalForbidden_orthogonal
    {s : Set ℝ} {hs : MeasurableSet s} {f : SoninL2}
    (hf : f ∈ (physicalForbidden s hs)ᗮ) :
    s.indicator (⇑f) =ᵐ[volume] 0 := by
  have h0 : indicatorCutoff s hs f = 0 := by
    rw [indicatorCutoff_eq_physicalForbidden_starProjection]
    exact (Submodule.starProjection_apply_eq_zero_iff (K := physicalForbidden s hs)).mpr hf
  have hae := indicatorCutoff_ae s hs f
  rw [h0] at hae
  filter_upwards [hae, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))]
    with t h1 h2
  rw [← h1, h2]

theorem physical_indicator_ae_zero_of_mem_centralSoninCarrier
    {a : ℝ} {f : SoninL2} (hf : f ∈ centralSoninCarrier a) :
    (centralInterval a).indicator (⇑f) =ᵐ[volume] 0 :=
  indicator_ae_zero_of_mem_physicalForbidden_orthogonal hf.1

theorem fourier_indicator_ae_zero_of_mem_fourierOrthogonal
    {a : ℝ} {f : SoninL2} (hf : f ∈ (centralFourierForbidden a)ᗮ) :
    (centralInterval a).indicator (⇑(fourierUnitary f)) =ᵐ[volume] 0 := by
  have h0 : fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f = 0 := by
    rw [fourierCutoff_eq_fourierForbidden_starProjection]
    exact (Submodule.starProjection_apply_eq_zero_iff
      (K := fourierForbidden (centralInterval a) (measurableSet_centralInterval a))).mpr hf
  have hcut : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (fourierUnitary f) = 0 := by
    have h1 := congrArg fourierUnitary h0
    rw [fourierCutoff_apply] at h1
    simpa using h1
  have hae := indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a)
    (fourierUnitary f)
  rw [hcut] at hae
  filter_upwards [hae, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))]
    with t h1 h2
  rw [← h1, h2]

/-! ### The square-integrable power kernels -/

private theorem continuousOn_rpow_kernel (a c : ℝ) (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => t ^ c) (Ioi a) := by
  intro t ht
  exact (Real.continuousAt_rpow_const t c
    (Or.inl (ne_of_gt (ha.trans (mem_Ioi.mp ht))))).continuousWithinAt

private theorem continuousOn_cpow_kernel (z : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-z)) (Ioi (0 : ℝ)) := by
  intro t ht
  have hslit : ((t : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using mem_Ioi.mp ht
  exact ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
    hslit).continuousWithinAt

private theorem memLp_two_rpow_Ioi {a c : ℝ} (ha : 0 < a) (hc : c < -(1 / 2)) :
    MemLp (fun t : ℝ => t ^ c) 2 ((volume : Measure ℝ).restrict (Ioi a)) := by
  rw [memLp_two_iff_integrable_sq_norm]
  · have h2c : IntegrableOn (fun t : ℝ => t ^ (2 * c)) (Ioi a) := by
      rw [integrableOn_Ioi_rpow_iff ha]
      linarith
    apply h2c.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : (0 : ℝ) < t := ha.trans (mem_Ioi.mp ht)
    show t ^ (2 * c) = ‖t ^ c‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le c),
      ← Real.rpow_natCast (t ^ c) 2, ← Real.rpow_mul ht0.le]
    norm_num [mul_comm]
  · exact (continuousOn_rpow_kernel a c ha).aestronglyMeasurable measurableSet_Ioi

private theorem memLp_two_cpow_kernel_Ioi {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 1 / 2 < z.re) :
    MemLp (fun t : ℝ => (t : ℂ) ^ (-z)) 2 ((volume : Measure ℝ).restrict (Ioi a)) := by
  apply MemLp.of_le (memLp_two_rpow_Ioi ha (c := -z.re) (by linarith))
  · exact ((continuousOn_cpow_kernel z).mono
      (fun t ht => ha.trans (mem_Ioi.mp ht))).aestronglyMeasurable measurableSet_Ioi
  · have hmem : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioi a)), t ∈ Ioi a :=
      ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with t ht
    have ht0 : (0 : ℝ) < t := ha.trans (mem_Ioi.mp ht)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.neg_re, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]

/-! ### The pure-power dominant -/

private def powerDominant (δ σmin σmax : ℝ) (t : ℝ) : ℝ :=
  δ⁻¹ * (t ^ (δ - σmin) + t ^ (δ - σmax) + t ^ (-δ - σmin) + t ^ (-δ - σmax))

private theorem abs_log_le_inv_mul_rpow_add {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    |Real.log t| ≤ δ⁻¹ * (t ^ δ + t ^ (-δ)) := by
  have hδinv : (0 : ℝ) ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hpos : (0 : ℝ) ≤ t ^ (-δ) := Real.rpow_nonneg ht.le _
  have hpos' : (0 : ℝ) ≤ t ^ δ := Real.rpow_nonneg ht.le _
  rcases le_or_gt 1 t with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have h := Real.log_le_rpow_div ht.le hδ
    rw [div_eq_inv_mul] at h
    calc Real.log t ≤ δ⁻¹ * t ^ δ := h
      _ ≤ δ⁻¹ * (t ^ δ + t ^ (-δ)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hpos) hδinv
  · rw [abs_of_nonpos (Real.log_nonpos ht.le h1.le)]
    have hinv : Real.log t⁻¹ ≤ δ⁻¹ * (t⁻¹) ^ δ := by
      have h := Real.log_le_rpow_div (inv_nonneg.mpr ht.le) hδ
      rwa [div_eq_inv_mul] at h
    rw [Real.log_inv] at hinv
    have hrw : (t⁻¹) ^ δ = t ^ (-δ) := by
      rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    rw [hrw] at hinv
    calc -Real.log t ≤ δ⁻¹ * t ^ (-δ) := hinv
      _ ≤ δ⁻¹ * (t ^ δ + t ^ (-δ)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hpos') hδinv

private theorem rpow_le_pair {t c cmin cmax : ℝ} (ht : 0 < t) (h1 : cmin ≤ c)
    (h2 : c ≤ cmax) :
    t ^ c ≤ t ^ cmin + t ^ cmax := by
  rcases le_or_gt 1 t with hone | hone
  · calc t ^ c ≤ t ^ cmax := Real.rpow_le_rpow_of_exponent_le hone h2
      _ ≤ t ^ cmin + t ^ cmax := le_add_of_nonneg_left (Real.rpow_nonneg ht.le _)
  · calc t ^ c ≤ t ^ cmin := Real.rpow_le_rpow_of_exponent_ge ht hone.le h1
      _ ≤ t ^ cmin + t ^ cmax := le_add_of_nonneg_right (Real.rpow_nonneg ht.le _)

private theorem abs_log_mul_rpow_le_powerDominant
    {t δ σmin σmax σ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hmin : σmin ≤ σ) (hmax : σ ≤ σmax) :
    |Real.log t| * t ^ (-σ) ≤ powerDominant δ σmin σmax t := by
  have hδinv : (0 : ℝ) ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hpow : (0 : ℝ) ≤ t ^ (-σ) := Real.rpow_nonneg ht.le _
  have h1 : |Real.log t| * t ^ (-σ) ≤ (δ⁻¹ * (t ^ δ + t ^ (-δ))) * t ^ (-σ) :=
    mul_le_mul_of_nonneg_right (abs_log_le_inv_mul_rpow_add ht hδ) hpow
  have hsplit : (δ⁻¹ * (t ^ δ + t ^ (-δ))) * t ^ (-σ) =
      δ⁻¹ * (t ^ (δ - σ) + t ^ (-δ - σ)) := by
    rw [mul_assoc, add_mul, ← Real.rpow_add ht, ← Real.rpow_add ht]
    ring_nf
  have hp1 : t ^ (δ - σ) ≤ t ^ (δ - σmax) + t ^ (δ - σmin) :=
    rpow_le_pair ht (by linarith) (by linarith)
  have hp2 : t ^ (-δ - σ) ≤ t ^ (-δ - σmax) + t ^ (-δ - σmin) :=
    rpow_le_pair ht (by linarith) (by linarith)
  calc |Real.log t| * t ^ (-σ) ≤ δ⁻¹ * (t ^ (δ - σ) + t ^ (-δ - σ)) := by
        rw [← hsplit]
        exact h1
    _ ≤ powerDominant δ σmin σmax t := by
        rw [powerDominant]
        exact mul_le_mul_of_nonneg_left (by linarith) hδinv

private theorem memLp_two_powerDominant_Ioi {a δ σmin σmax : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) (hband : 1 / 2 < σmin - δ) (hle : σmin ≤ σmax) :
    MemLp (powerDominant δ σmin σmax) 2 ((volume : Measure ℝ).restrict (Ioi a)) := by
  have h1 : MemLp (fun t : ℝ => t ^ (δ - σmin)) 2
      ((volume : Measure ℝ).restrict (Ioi a)) := memLp_two_rpow_Ioi ha (by linarith)
  have h2 : MemLp (fun t : ℝ => t ^ (δ - σmax)) 2
      ((volume : Measure ℝ).restrict (Ioi a)) := memLp_two_rpow_Ioi ha (by linarith)
  have h3 : MemLp (fun t : ℝ => t ^ (-δ - σmin)) 2
      ((volume : Measure ℝ).restrict (Ioi a)) := memLp_two_rpow_Ioi ha (by linarith)
  have h4 : MemLp (fun t : ℝ => t ^ (-δ - σmax)) 2
      ((volume : Measure ℝ).restrict (Ioi a)) := memLp_two_rpow_Ioi ha (by linarith)
  exact (((h1.add h2).add h3).add h4).const_mul δ⁻¹

/-! ### Convergence on the physical half-plane -/

/-- The multiplicative transform `∫_{t>0} f(t) t^{-z} dt`. -/
def soninMellinIntegral (f : SoninL2) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-z) * f t

theorem soninMellinIntegral_eq_mellin (f : SoninL2) (z : ℂ) :
    soninMellinIntegral f z = mellin (⇑f) (1 - z) := by
  rw [soninMellinIntegral, mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  show (t : ℂ) ^ (-z) * f t = (t : ℂ) ^ (1 - z - 1) • f t
  have hexp : (1 : ℂ) - z - 1 = -z := by ring
  rw [smul_eq_mul, hexp]

private theorem aestronglyMeasurable_cpow_mul (f : SoninL2) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-z) * f t)
      ((volume : Measure ℝ).restrict (Ioi 0)) :=
  ((continuousOn_cpow_kernel z).aestronglyMeasurable measurableSet_Ioi).mul
    ((Lp.aestronglyMeasurable f).restrict)

theorem soninMellin_integrableOn {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hsupp : (centralInterval a).indicator (⇑f) =ᵐ[volume] 0)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-z) * f t) (Ioi 0) := by
  have hzero : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → f t = 0 := by
    filter_upwards [hsupp] with t ht hts
    simpa [Set.indicator_of_mem hts] using ht
  have hIoc : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-z) * f t) (Ioc 0 a) := by
    apply (integrable_zero _ _ _).congr
    have hz0 : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioc 0 a)),
        t ∈ centralInterval a → f t = 0 := ae_restrict_of_ae hzero
    have hmem : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioc 0 a)), t ∈ Ioc 0 a :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hz0, hmem] with t h1 h2
    have htc : t ∈ centralInterval a := by
      simp only [centralInterval, mem_Icc]
      constructor
      · linarith [h2.1]
      · exact h2.2
    rw [h1 htc, mul_zero]
    rfl
  have hIoi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-z) * f t) (Ioi a) :=
    (memLp_two_cpow_kernel_Ioi ha hz).integrable_mul ((Lp.memLp f).restrict _)
  have hunion := hIoc.union hIoi
  rwa [Set.Ioc_union_Ioi_eq_Ioi ha.le] at hunion

/-! ### Holomorphy on the physical half-plane -/

private theorem hasDerivAt_const_cpow_real {t : ℝ} (ht : 0 < t) (y : ℂ) :
    HasDerivAt (fun w : ℂ => (t : ℂ) ^ w) ((t : ℂ) ^ y * Real.log t) y := by
  have h := HasDerivAt.const_cpow (c := (t : ℂ)) (hasDerivAt_id y)
    (Or.inl (by exact_mod_cast ht.ne'))
  simpa [Complex.ofReal_log ht.le, mul_comm] using h

theorem soninMellinIntegral_differentiableAt {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hsupp : (centralInterval a).indicator (⇑f) =ᵐ[volume] 0)
    {z₀ : ℂ} (hz₀ : 1 / 2 < z₀.re) :
    DifferentiableAt ℂ (soninMellinIntegral f) z₀ := by
  set ε : ℝ := (z₀.re - 1 / 2) / 4 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    linarith
  set σmin : ℝ := z₀.re - ε with hσmin
  set σmax : ℝ := z₀.re + ε with hσmax
  have hband : 1 / 2 < σmin - ε := by
    rw [hσmin, hε]
    linarith
  set G : ℝ → ℝ := (Ioi a).indicator (powerDominant ε σmin σmax) with hG
  set bound : ℝ → ℝ := fun t => ‖f t‖ * G t with hbound
  have hzero : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioi 0)),
      t ∈ centralInterval a → f t = 0 := by
    apply ae_restrict_of_ae
    filter_upwards [hsupp] with t ht hts
    simpa [Set.indicator_of_mem hts] using ht
  have hmem0 : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioi 0)), t ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  have hres : ∀ z ∈ Metric.ball z₀ ε, σmin ≤ z.re ∧ z.re ≤ σmax := by
    intro z hzball
    have hre : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm (z - z₀)
    have hdist : ‖z - z₀‖ < ε := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hzball
    rw [Complex.sub_re, abs_le] at hre
    constructor
    · rw [hσmin]; linarith [hre.1]
    · rw [hσmax]; linarith [hre.2]
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => (t : ℂ) ^ (-z) * f t)
    (F' := fun z t => (-(Real.log t : ℂ) * (t : ℂ) ^ (-z)) * f t)
    (x₀ := z₀) (bound := bound)
    (Metric.ball_mem_nhds z₀ hεpos)
    (Filter.Eventually.of_forall fun z => aestronglyMeasurable_cpow_mul f z)
    (soninMellin_integrableOn ha hsupp hz₀)
    (by
      apply AEStronglyMeasurable.mul ?_ ((Lp.aestronglyMeasurable f).restrict)
      apply AEStronglyMeasurable.mul ?_
        ((continuousOn_cpow_kernel z₀).aestronglyMeasurable measurableSet_Ioi)
      exact ((Complex.measurable_ofReal.comp Real.measurable_log).neg
        ).aestronglyMeasurable)
    (by
      filter_upwards [hzero, hmem0] with t hsup ht
      intro z hzball
      have ht0 : (0 : ℝ) < t := mem_Ioi.mp ht
      rcases le_or_gt t a with hta | hta
      · have htc : t ∈ centralInterval a := by
          simp only [centralInterval, mem_Icc]
          constructor
          · linarith
          · exact hta
        rw [hsup htc]
        simp only [mul_zero, norm_zero]
        apply mul_nonneg (norm_nonneg _)
        rw [hG]
        apply Set.indicator_nonneg
        intro x hx
        have hx0 : (0 : ℝ) < x := ha.trans (mem_Ioi.mp hx)
        rw [powerDominant]
        positivity
      · have hnorm : ‖(-(Real.log t : ℂ) * (t : ℂ) ^ (-z)) * f t‖ =
            (|Real.log t| * t ^ (-z.re)) * ‖f t‖ := by
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.neg_re]
        rw [hnorm]
        show (|Real.log t| * t ^ (-z.re)) * ‖f t‖ ≤ ‖f t‖ * G t
        have hGt : G t = powerDominant ε σmin σmax t := by
          rw [hG, Set.indicator_of_mem (mem_Ioi.mpr hta)]
        rw [hGt, mul_comm (‖f t‖)]
        apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact abs_log_mul_rpow_le_powerDominant ht0 hεpos (hres z hzball).1
          (hres z hzball).2)
    (by
      have hfn : MemLp (fun t : ℝ => ‖f t‖) 2 ((volume : Measure ℝ).restrict (Ioi 0)) :=
        ((Lp.memLp f).restrict _).norm
      have hGmem : MemLp G 2 ((volume : Measure ℝ).restrict (Ioi 0)) := by
        rw [hG, memLp_indicator_iff_restrict measurableSet_Ioi]
        have hmeas : ((volume : Measure ℝ).restrict (Ioi 0)).restrict (Ioi a) =
            (volume : Measure ℝ).restrict (Ioi a) := by
          rw [Measure.restrict_restrict measurableSet_Ioi]
          congr 1
          exact Set.inter_eq_left.mpr fun t ht => ha.trans (mem_Ioi.mp ht)
        rw [hmeas]
        exact memLp_two_powerDominant_Ioi ha hεpos hband (by rw [hσmin, hσmax]; linarith)
      exact hfn.integrable_mul hGmem)
    (by
      filter_upwards [hmem0] with t ht
      intro z hzball
      have ht0 : (0 : ℝ) < t := mem_Ioi.mp ht
      have hbase := hasDerivAt_const_cpow_real ht0 (-z)
      have hneg : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) z := (hasDerivAt_id z).neg
      have hcomp := hbase.comp z hneg
      have hfull := hcomp.mul_const (f t)
      have heq : (-(Real.log t : ℂ) * (t : ℂ) ^ (-z)) * f t =
          (t : ℂ) ^ (-z) * (Real.log t : ℂ) * -1 * f t := by ring
      rw [heq]
      exact hfull)
  exact hderiv.2.differentiableAt

/-! ### The completed transform and its two half-plane bricks -/

/-- The completed archimedean transform of the Sonin carrier. -/
def soninDeBrangesTransform (f : SoninL2) (z : ℂ) : ℂ :=
  2 * Complex.Gammaℝ z * soninMellinIntegral f z

/-- **The physical half-plane brick.** For a function vanishing on the physical cutoff, the
completed transform is holomorphic on `Re z > 1/2`. -/
theorem soninDeBrangesTransform_differentiableOn {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hsupp : (centralInterval a).indicator (⇑f) =ᵐ[volume] 0) :
    DifferentiableOn ℂ (soninDeBrangesTransform f) {z : ℂ | 1 / 2 < z.re} := by
  intro z₀ hz₀
  apply DifferentiableAt.differentiableWithinAt
  have hz₀' : 1 / 2 < z₀.re := hz₀
  apply DifferentiableAt.mul
  · exact ((differentiableAt_Gammaℝ_of_re_pos (by linarith)).const_mul 2)
  · exact soninMellinIntegral_differentiableAt ha hsupp hz₀'

/-- The dual completed transform: the transform of the Fourier image at the reflected
variable. -/
def soninDeBrangesDualTransform (f : SoninL2) (z : ℂ) : ℂ :=
  soninDeBrangesTransform (fourierUnitary f) (1 - z)

/-- **The Fourier half-plane brick.** For a function whose Fourier transform vanishes on the
cutoff, the dual completed transform is holomorphic on `Re z < 1/2`. -/
theorem soninDeBrangesDualTransform_differentiableOn {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hsuppF : (centralInterval a).indicator (⇑(fourierUnitary f)) =ᵐ[volume] 0) :
    DifferentiableOn ℂ (soninDeBrangesDualTransform f) {z : ℂ | z.re < 1 / 2} := by
  intro z₀ hz₀
  apply DifferentiableAt.differentiableWithinAt
  have hz₀' : (z₀ : ℂ).re < 1 / 2 := hz₀
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (1 - z₀) ∈ {z : ℂ | 1 / 2 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.one_re]
    linarith
  have h1 : DifferentiableAt ℂ (soninDeBrangesTransform (fourierUnitary f)) (1 - z₀) :=
    (soninDeBrangesTransform_differentiableOn ha hsuppF).differentiableAt
      (hopen.mem_nhds hmem)
  exact h1.comp z₀ ((differentiableAt_const 1).sub differentiableAt_id)

/-! ### The two bricks on the Sonin carrier -/

/-- **The polarized entire-carrier bricks.** Every member of the Sonin carrier has a
holomorphic completed transform on the physical half-plane and a holomorphic dual completed
transform on the Fourier half-plane: the two halves of its de Branges entire realization. -/
theorem soninCarrier_deBranges_bricks {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) :
    DifferentiableOn ℂ (soninDeBrangesTransform f) {z : ℂ | 1 / 2 < z.re} ∧
      DifferentiableOn ℂ (soninDeBrangesDualTransform f) {z : ℂ | z.re < 1 / 2} :=
  ⟨soninDeBrangesTransform_differentiableOn ha
      (physical_indicator_ae_zero_of_mem_centralSoninCarrier hf),
    soninDeBrangesDualTransform_differentiableOn ha
      (fourier_indicator_ae_zero_of_mem_fourierOrthogonal hf.2)⟩

/-- The bricks on the actual even Sonin carrier. -/
theorem evenSoninCarrier_deBranges_bricks {a : ℝ} (ha : 0 < a) {f : evenSubspace}
    (hf : f ∈ evenCentralSoninCarrier a) :
    DifferentiableOn ℂ (soninDeBrangesTransform (f : SoninL2)) {z : ℂ | 1 / 2 < z.re} ∧
      DifferentiableOn ℂ (soninDeBrangesDualTransform (f : SoninL2))
        {z : ℂ | z.re < 1 / 2} :=
  soninCarrier_deBranges_bricks ha (Submodule.mem_comap.mp hf)

end RHTower
