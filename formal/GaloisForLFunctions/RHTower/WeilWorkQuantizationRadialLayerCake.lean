import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialTheta
import GaloisForLFunctions.RHTower.WeilFractionalMassSummableRigidity

/-!
# Layer-cake cancellation for the canonical radial trace

A bounded nonnegative monotone phase vanishing at minus infinity produces no positive-integer
radial residue. The proof uses the actual source's uniform signed truncation bound and measurable
trace, so it needs no continuous extension to the critical edge. The phase assumptions are
analytic helper inputs, to be discharged by the canonical finite residual measure before any
source-rigidity conclusion is drawn.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
open WeilHerglotz IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  WeilWorkSettledPhase GaloisForLFunctions.HTGeometry HamburgerStability AbelianTwist
  MonotoneTwistLock

/-- Fixed-window vanishing in the Mellin variable. -/
theorem tendsto_quantization_signed_fixed_truncation_two_mul {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {m : ℕ} (hm : 1 ≤ m) (a b : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in a..b, quantizationTraceF hW (2 * t) *
      pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  have hchange : ∀ ε : ℝ, (ε : ℂ) * ∫ t in a..b, quantizationTraceF hW (2 * t) *
      pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) =
      (1 / 2 : ℂ) * ((ε : ℂ) * ∫ y in (2 * a)..(2 * b), quantizationTraceF hW y *
        pairKernel y ((ε : ℂ) + (m : ℂ) * I)) := by
    intro ε
    let f : ℝ → ℂ := fun y => quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (m : ℂ) * I)
    have hc := intervalIntegral.integral_comp_mul_left f (a := a) (b := b) (two_ne_zero' ℝ)
    change (ε : ℂ) * ∫ t in a..b, f (2 * t) = (1 / 2 : ℂ) * ((ε : ℂ) * ∫ y in (2 * a)..(2 * b), f y)
    rw [hc, real_smul]
    push_cast
    ring
  simp_rw [hchange]
  simpa only [mul_zero] using
    (tendsto_quantization_signed_fixed_truncation hW hm (2 * a) (2 * b)).const_mul (1 / 2 : ℂ)

/-- Layer-cake vanishing from actual-source contour bounds and measurable radial traces.
The monotone function will be supplied by the finite positive residual measure. -/
theorem tendsto_quantization_radial_monotone_twist {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {h : ℝ → ℝ} (hmono : Monotone h) (hh0 : ∀ t, 0 ≤ h t) {H : ℝ} (hhH : ∀ t, h t ≤ H)
    (hlim : Tendsto h atBot (𝓝 0)) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
        (Complex.exp (-(2 * Real.pi * I) * h t) - 1) *
          (quantizationTraceF hW (2 * t) * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := exists_bound_quantization_signed_truncation_two_mul hW hm
  obtain ⟨CB, _, hpoly⟩ := exists_quantization_trace_pair_bound hW
  have hfm : Measurable (fun t : ℝ => quantizationTraceF hW (2 * t)) :=
    (measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)
  set f : ℝ → ℝ → ℂ := fun ε t => quantizationTraceF hW (2 * t) * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) with hf
  have hτre : ∀ ε : ℝ, 0 < ε → 0 < ((ε : ℂ) + (m : ℂ) * I).re := fun ε hε => by simp [hε]
  have hτ0 : ∀ ε : ℝ, 0 < ε → ((ε : ℂ) + (m : ℂ) * I) ≠ 0 := fun ε hε h0 => by
    have := hτre ε hε; rw [h0] at this; simp at this
  have hfint : ∀ ε : ℝ, 0 < ε → Integrable (f ε) := fun ε hε =>
    integrable_defectLaplace_integrand hfm.aestronglyMeasurable (fun t => (hpoly t).1) (hτre ε hε)
  have hfmeas : ∀ ε : ℝ, 0 < ε → Measurable (f ε) := fun ε hε =>
    hfm.mul (TruncatedRadial.continuous_pairKernel_two_mul (hτ0 ε hε)).measurable
  -- Fubini: the layer-cake form
  set F : ℝ → ℝ → ℂ := fun ε x => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
    (if x ≤ h t then layerDensity x * f ε t else 0) with hF
  have hmeasS : MeasurableSet {p : ℝ × ℝ | p.2 ≤ h p.1} :=
    measurableSet_le measurable_snd (hmono.measurable.comp measurable_fst)
  have hprod : ∀ ε : ℝ, 0 < ε → Integrable
      (Function.uncurry fun t x => if x ≤ h t then layerDensity x * f ε t else 0)
      ((volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioc 0 H))) := by
    intro ε hε
    have hdom : Integrable (fun p : ℝ × ℝ => ‖f ε p.1‖ * (2 * Real.pi))
        ((volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioc 0 H))) :=
      Integrable.mul_prod (hfint ε hε).norm.integrableOn
        (integrableOn_const (C := 2 * Real.pi) (hs := measure_Ioc_lt_top.ne))
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hm : Measurable fun p : ℝ × ℝ => layerDensity p.2 * f ε p.1 :=
        (continuous_layerDensity.measurable.comp measurable_snd).mul
          ((hfmeas ε hε).comp measurable_fst)
      exact (Measurable.ite hmeasS hm measurable_const).aestronglyMeasurable
    · simp only [Function.uncurry]
      split_ifs
      · rw [norm_mul, norm_layerDensity, mul_comm]
      · rw [norm_zero]; positivity
  have hfub : ∀ ε : ℝ, 0 < ε → (ε : ℂ) * ∫ t in Iio (0 : ℝ),
      (Complex.exp (-(2 * Real.pi * I) * h t) - 1) * f ε t = ∫ x in Ioc 0 H, F ε x := by
    intro ε hε
    have e1 : ∀ t : ℝ, (Complex.exp (-(2 * Real.pi * I) * h t) - 1) * f ε t =
        ∫ x in Ioc 0 H, (if x ≤ h t then layerDensity x * f ε t else 0) := by
      intro t
      rw [twist_eq_setIntegral (hh0 t) (hhH t), ← integral_mul_const]
      congr 1; funext x; split_ifs <;> simp
    simp only [e1]
    rw [integral_integral_swap (hprod ε hε), ← integral_const_mul]
  -- dominated convergence in `x`
  have hFb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x ∈ Ioc 0 H, ‖F ε x‖ ≤ 2 * Real.pi * B := by
    intro ε hε hε1 x hx
    obtain ⟨a, ha0, hint⟩ := exists_interval_superlevel hmono hlim hx.1
    have e : F ε x = layerDensity x * ((ε : ℂ) * ∫ t in a..0, f ε t) := by
      simp only [hF]
      rw [← hint]
      have : ∀ t, (if x ≤ h t then layerDensity x * f ε t else 0) =
          layerDensity x * (if x ≤ h t then f ε t else 0) := fun t => by
        split_ifs <;> simp
      simp only [this, integral_const_mul]
      ring
    rw [e, norm_mul, norm_layerDensity]
    exact mul_le_mul_of_nonneg_left (hB ε hε hε1 a ha0) (by positivity)
  have hFlim : ∀ x ∈ Ioc 0 H, Tendsto (fun ε => F ε x) (𝓝[>] 0) (𝓝 0) := by
    intro x hx
    obtain ⟨a, ha0, hint⟩ := exists_interval_superlevel hmono hlim hx.1
    have e : ∀ ε : ℝ, F ε x = layerDensity x * ((ε : ℂ) * ∫ t in a..0, f ε t) := by
      intro ε
      simp only [hF]
      rw [← hint]
      have he : ∀ t, (if x ≤ h t then layerDensity x * f ε t else 0) =
          layerDensity x * (if x ≤ h t then f ε t else 0) := fun t => by
        split_ifs <;> simp
      simp only [he, integral_const_mul]
      ring
    simp_rw [e]
    simpa only [mul_zero, hf] using
      (tendsto_quantization_signed_fixed_truncation_two_mul hW hm a 0).const_mul (layerDensity x)
  have hDCT : Tendsto (fun ε => ∫ x in Ioc 0 H, F ε x) (𝓝[>] 0) (𝓝 (∫ x in Ioc 0 H, (0 : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * Real.pi * B) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have h1 := (hprod ε hε).integral_prod_right
      exact (h1.aestronglyMeasurable.const_mul (ε : ℂ))
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with
        ε hε hε1
      exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall fun x hx => hFb ε hε hε1.2.le x hx)
    · exact integrableOn_const (C := 2 * Real.pi * B) (hs := measure_Ioc_lt_top.ne)
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hFlim)
  rw [integral_zero] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hfub ε hε).symm

end RHTower.WeilSpectral
