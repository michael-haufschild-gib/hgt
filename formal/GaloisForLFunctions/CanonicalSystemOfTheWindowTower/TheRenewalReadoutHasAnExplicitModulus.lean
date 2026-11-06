import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicRenewalCouplingHasItsExactNormalization
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheHalfLineLogarithmicGreenSolutionsHaveBoundaryValues

/-!
# The renewal readout has an explicit modulus

Write `v` for the causal density, `V` for its cumulative mass and `J = v * V` for the coupled mass.
Positivity and monotonicity of `v` give estimates that depend only on sizes of the forcing.

* `v(ρ) ≤ 1/ρ`, so `|∫ v(y−x) f(y) dy| ≤ ‖f‖_∞ V(ρ) + ‖f‖₁/ρ`.
* `‖v(·−x) − v‖₁ = 2V(x)` exactly, so the backward convolution has modulus `2‖f‖_∞ V(x)` at zero.
* The Green solution obeys `|u(x) − τ V(x)| ≤ 2‖f‖_∞ V(x)²`, with `τ = ∫ v f`: a uniform edge law.
* A profile `G` with `|G − τV| ≤ A V²` reads `∫ v(y) G(ε−y) dy = τ J(ε) + O(A V(ε) J(ε))`.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open HTGeometry

local notation "v" => logarithmicCausalKernel
local notation "V" => logarithmicRenewalMass

/-- The causal density at `ρ` is at most `1/ρ`. -/
theorem logarithmicCausalKernel_le_inv {ρ : ℝ} (hρ : 0 < ρ) : v ρ ≤ 1 / ρ := by
  have hle : (∫ _ in Ioc (0 : ℝ) ρ, v ρ) ≤ ∫ t in Ioc (0 : ℝ) ρ, v t := by
    refine setIntegral_mono_on (by
      rw [IntegrableOn, integrable_const_iff]
      exact Or.inr (by rw [isFiniteMeasure_restrict]; simp))
      logarithmicCausalKernel_mass_one.1.integrableOn measurableSet_Ioc fun t ht => ?_
    exact antitoneOn_logarithmicCausalKernel ht.1 hρ ht.2
  have hval : (∫ _ in Ioc (0 : ℝ) ρ, v ρ) = ρ * v ρ := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hρ.le, smul_eq_mul, sub_zero]
  rw [hval] at hle
  have hV : ρ * v ρ ≤ 1 := hle.trans (logarithmicRenewalMass_le_one ρ)
  rw [le_div_iff₀ hρ]
  linarith only [hV]

private theorem integrable_kernel_shift (x : ℝ) : Integrable (fun y : ℝ => v (y - x)) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_right (volume : Measure ℝ) (-x)).integrable_comp_of_integrable
      logarithmicCausalKernel_mass_one.1

private theorem integral_kernel_shift (x : ℝ) : ∫ y : ℝ, v (y - x) = 1 := by
  rw [integral_sub_right_eq_self, logarithmicCausalKernel_mass_one.2]

private theorem integrable_readout {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {A : ℝ}
    (hb : ∀ᵐ y ∂volume, ‖f y‖ ≤ A) (x : ℝ) :
    Integrable (fun y : ℝ => (v (y - x) : ℂ) * f y) := by
  have ht : Integrable (fun y : ℝ => (v (y - x) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (integrable_kernel_shift x)
  exact ht.mul_bdd hf hb

/-- **The split bound.** The near part of the kernel sees the sup norm, the far part the `L¹` norm. -/
theorem norm_logarithmicBackwardConvolution_le_split {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 < ρ)
    (hb : ∀ᵐ y ∂volume, ‖f y‖ ≤ A) (hi : Integrable f) (x : ℝ) :
    ‖logarithmicBackwardConvolution f x‖ ≤ A * V ρ + (∫ y, ‖f y‖) / ρ := by
  let G : ℝ → ℝ := (Ioc (0 : ℝ) ρ).indicator (fun t => v t * A)
  have hGi : Integrable G :=
    (logarithmicCausalKernel_mass_one.1.mul_const A).integrableOn.integrable_indicator
      measurableSet_Ioc
  have hG : ∫ t, G t = A * V ρ := by
    rw [integral_indicator measurableSet_Ioc, integral_mul_const]
    change V ρ * A = _
    ring
  have hGs : Integrable (fun y : ℝ => G (y - x)) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-x)).integrable_comp_of_integrable hGi
  have hmaj : Integrable (fun y : ℝ => G (y - x) + ‖f y‖ / ρ) := hGs.add (hi.norm.div_const ρ)
  calc
    ‖logarithmicBackwardConvolution f x‖
        ≤ ∫ y, ‖(v (y - x) : ℂ) * f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (G (y - x) + ‖f y‖ / ρ) := by
      apply integral_mono_ae (integrable_readout hf hb x).norm hmaj
      filter_upwards [hb] with y hy
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _)]
      have hG0 : 0 ≤ G (y - x) := indicator_nonneg
        (fun t _ => mul_nonneg (logarithmicCausalKernel_nonneg t) hA) _
      have hf0 : 0 ≤ ‖f y‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
      by_cases hy0 : y - x ≤ 0
      · rw [logarithmicCausalKernel_of_nonpos hy0, zero_mul]
        exact add_nonneg hG0 hf0
      push Not at hy0
      by_cases hyρ : y - x ≤ ρ
      · have hG1 : G (y - x) = v (y - x) * A := indicator_of_mem (show y - x ∈ Ioc 0 ρ from ⟨hy0, hyρ⟩) _
        rw [hG1]
        exact (mul_le_mul_of_nonneg_left hy (logarithmicCausalKernel_nonneg _)).trans
          (le_add_of_nonneg_right hf0)
      · push Not at hyρ
        have hvle : v (y - x) ≤ 1 / ρ :=
          (antitoneOn_logarithmicCausalKernel hρ hy0 hyρ.le).trans
            (logarithmicCausalKernel_le_inv hρ)
        have h2 : v (y - x) * ‖f y‖ ≤ ‖f y‖ / ρ := by
          calc
            _ ≤ 1 / ρ * ‖f y‖ := mul_le_mul_of_nonneg_right hvle (norm_nonneg _)
            _ = _ := by ring
        exact h2.trans (le_add_of_nonneg_left hG0)
    _ = _ := by
      rw [integral_add hGs (hi.norm.div_const ρ), integral_div,
        integral_sub_right_eq_self (fun t => G t) x, hG]

/-- The `L¹` distance between the causal density and its translate. -/
theorem abs_kernel_shift_sub_eq {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    |v (y - x) - v y| = v (y - x) - v y + 2 * (Ioc (0 : ℝ) x).indicator v y := by
  by_cases hy0 : y ≤ 0
  · have h1 : v (y - x) = 0 := logarithmicCausalKernel_of_nonpos (by linarith only [hy0, hx])
    have h2 : v y = 0 := logarithmicCausalKernel_of_nonpos hy0
    have h3 : (Ioc (0 : ℝ) x).indicator v y = 0 :=
      indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hy0)) _
    rw [h1, h2, h3]
    simp
  push Not at hy0
  by_cases hyx : y ≤ x
  · have h1 : v (y - x) = 0 := logarithmicCausalKernel_of_nonpos (by linarith only [hyx])
    have h3 : (Ioc (0 : ℝ) x).indicator v y = v y :=
      indicator_of_mem (show y ∈ Ioc (0 : ℝ) x from ⟨hy0, hyx⟩) _
    rw [h1, h3, zero_sub, abs_neg, abs_of_nonneg (logarithmicCausalKernel_nonneg _)]
    ring
  · push Not at hyx
    have h1 : v y ≤ v (y - x) :=
      antitoneOn_logarithmicCausalKernel (sub_pos.mpr hyx) hy0 (by linarith only [hx])
    have h3 : (Ioc (0 : ℝ) x).indicator v y = 0 :=
      indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hyx)) _
    rw [h3, abs_of_nonneg (sub_nonneg.mpr h1)]
    ring

/-- **The modulus of the readout**: `|W*f(x) − W*f(0)| ≤ 2‖f‖_∞ V(x)` for `x ≥ 0`. -/
theorem norm_logarithmicBackwardConvolution_sub_le {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) {A : ℝ} (hb : ∀ᵐ y ∂volume, ‖f y‖ ≤ A) {x : ℝ}
    (hx : 0 ≤ x) :
    ‖logarithmicBackwardConvolution f x - logarithmicBackwardConvolution f 0‖ ≤ 2 * A * V x := by
  have hi0 := integrable_readout hf hb 0
  have hix := integrable_readout hf hb x
  simp only [sub_zero] at hi0
  have hind : Integrable ((Ioc (0 : ℝ) x).indicator v) :=
    logarithmicCausalKernel_mass_one.1.integrableOn.integrable_indicator measurableSet_Ioc
  have hdiff : Integrable (fun y : ℝ => v (y - x) - v y) :=
    (integrable_kernel_shift x).sub logarithmicCausalKernel_mass_one.1
  have hmajF : Integrable (fun y : ℝ => v (y - x) - v y + 2 * (Ioc (0 : ℝ) x).indicator v y) :=
    hdiff.add (hind.const_mul 2)
  have hint : ∫ y : ℝ, (v (y - x) - v y + 2 * (Ioc (0 : ℝ) x).indicator v y) = 2 * V x := by
    rw [integral_add hdiff (hind.const_mul 2), integral_sub (integrable_kernel_shift x)
      logarithmicCausalKernel_mass_one.1, integral_kernel_shift, logarithmicCausalKernel_mass_one.2,
      integral_const_mul, integral_indicator measurableSet_Ioc]
    change 1 - 1 + 2 * V x = _
    ring
  have hsub : logarithmicBackwardConvolution f x - logarithmicBackwardConvolution f 0 =
      ∫ y : ℝ, ((v (y - x) : ℂ) * f y - (v y : ℂ) * f y) := by
    rw [integral_sub hix hi0]
    simp only [logarithmicBackwardConvolution, sub_zero]
  rw [hsub]
  calc
    _ ≤ ∫ y : ℝ, (v (y - x) - v y + 2 * (Ioc (0 : ℝ) x).indicator v y) * A := by
      apply norm_integral_le_of_norm_le (hmajF.mul_const A)
      filter_upwards [hb] with y hy
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_kernel_shift_sub_eq hx]
      refine mul_le_mul_of_nonneg_left hy ?_
      rw [← abs_kernel_shift_sub_eq hx]
      exact abs_nonneg _
    _ = _ := by
      rw [integral_mul_const, hint]
      ring

/-- **The uniform edge law**: `|u(x) − τ V(x)| ≤ 2‖f‖_∞ V(x)²`, with `τ = ∫ v f` the trace. -/
theorem norm_logarithmicGreenRepresentative_sub_le (f : LogarithmicHalfLineL2) {A : ℝ}
    (hb : ∀ᵐ y ∂volume, ‖(f : RealLineL2) y‖ ≤ A) {x : ℝ} (hx : 0 < x) :
    ‖logarithmicGreenRepresentative f x -
        logarithmicBackwardConvolution (f : RealLineL2) 0 * (V x : ℂ)‖ ≤ 2 * A * V x ^ 2 := by
  have hm := (Lp.stronglyMeasurable (f : RealLineL2)).measurable
  have hae : AEStronglyMeasurable ((f : RealLineL2) : ℝ → ℂ) volume :=
    (Lp.stronglyMeasurable (f : RealLineL2)).aestronglyMeasurable
  have hA : 0 ≤ A := by
    obtain ⟨y, hy⟩ := hb.exists
    exact (norm_nonneg _).trans hy
  have hmono := monotone_logarithmicRenewalMass
  have hV := logarithmicRenewalMass_pos hx
  have hVne : (V x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have havg := norm_logarithmicBoundaryAverage_sub_le (C := 2 * A * V x)
    (measurable_logarithmicBackwardConvolution hm) hx (fun s hs =>
      (norm_logarithmicBackwardConvolution_sub_le hae hb hs.1).trans
        (mul_le_mul_of_nonneg_left (hmono hs.2) (by positivity)))
  have he : logarithmicGreenRepresentative f x -
      logarithmicBackwardConvolution (f : RealLineL2) 0 * (V x : ℂ) =
      (logarithmicBoundaryAverage (logarithmicBackwardConvolution (f : RealLineL2)) x -
        logarithmicBackwardConvolution (f : RealLineL2) 0) * (V x : ℂ) := by
    rw [logarithmicBoundaryAverage, sub_mul, div_mul_cancel₀ _ hVne]
    rfl
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hV.le]
  calc
    _ ≤ (2 * A * V x) * V x := mul_le_mul_of_nonneg_right havg hV.le
    _ = _ := by ring

/-- The Green solution is bounded by the sup of its readout times the renewal mass. -/
theorem norm_logarithmicGreenRepresentative_le (f : LogarithmicHalfLineL2) {B : ℝ}
    (hB : ∀ r, 0 ≤ r → ‖logarithmicBackwardConvolution (f : RealLineL2) r‖ ≤ B) {x : ℝ} :
    ‖logarithmicGreenRepresentative f x‖ ≤ B * V x := by
  by_cases hx : x ≤ 0
  · rw [logarithmicGreenRepresentative_of_nonpos f hx, norm_zero]
    have hV : V x = 0 := by
      change ∫ t in Ioc (0 : ℝ) x, v t = 0
      rw [Ioc_eq_empty_of_le hx]
      simp
    rw [hV, mul_zero]
  push Not at hx
  have hm := (Lp.stronglyMeasurable (f : RealLineL2)).measurable
  have hbound : ∀ t ∈ Ioc (0 : ℝ) x,
      ‖(v t : ℂ) * logarithmicBackwardConvolution (f : RealLineL2) (x - t)‖ ≤ v t * B := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hB _ (sub_nonneg.mpr ht.2)) (logarithmicCausalKernel_nonneg _)
  unfold logarithmicGreenRepresentative
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) x, v t * B :=
      norm_integral_le_of_norm_le
        ((logarithmicCausalKernel_mass_one.1.mul_const B).integrableOn)
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hbound))
    _ = _ := by
      rw [integral_mul_const]
      change V x * B = _
      ring

/-- **The coupled readout of a profile with an edge law.** If `|G − τV| ≤ A V²` on `[0,ε]`, then
`∫ v(y) G(ε−y) dy` is `τ J(ε)` up to `A V(ε) J(ε)`. -/
theorem norm_integral_kernel_mul_sub_coupling_le {G : ℝ → ℂ} {τ : ℂ} {A ε : ℝ} (hA : 0 ≤ A)
    (hG : Measurable G) (hB : ∃ C, ∀ t, ‖G t‖ ≤ C)
    (hedge : ∀ t ∈ Icc (0 : ℝ) ε, ‖G t - τ * (V t : ℂ)‖ ≤ A * V t ^ 2) :
    ‖(∫ y in Ioc (0 : ℝ) ε, (v y : ℂ) * G (ε - y)) - τ * (logarithmicRenewalCoupling ε : ℂ)‖ ≤
      A * V ε * logarithmicRenewalCoupling ε := by
  obtain ⟨C, hC⟩ := hB
  have hi1 : IntegrableOn (fun y : ℝ => (v y : ℂ) * G (ε - y)) (Ioc 0 ε) := by
    have ht : Integrable (fun y : ℝ => (v y : ℂ)) :=
      Complex.ofRealCLM.integrable_comp logarithmicCausalKernel_mass_one.1
    exact (ht.mul_bdd ((hG.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (Eventually.of_forall fun y => hC _)).integrableOn
  have hi2 : Integrable (fun y : ℝ => v y * V (ε - y)) := integrable_logarithmicRenewalCoupling ε
  have hi2C : IntegrableOn (fun y : ℝ => (v y : ℂ) * ((τ * (V (ε - y) : ℂ)))) (Ioc 0 ε) := by
    have h : Integrable (fun y : ℝ => τ * ((v y * V (ε - y) : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.integrable_comp hi2).const_mul τ
    refine (h.congr (Eventually.of_forall fun y => ?_)).integrableOn
    simp only [Complex.ofReal_mul]
    ring
  have hval : τ * (logarithmicRenewalCoupling ε : ℂ) =
      ∫ y in Ioc (0 : ℝ) ε, (v y : ℂ) * (τ * (V (ε - y) : ℂ)) := by
    rw [logarithmicRenewalCoupling, ← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    simp only [Complex.ofReal_mul]
    ring
  rw [hval, ← integral_sub hi1 hi2C]
  have hmono := monotone_logarithmicRenewalMass
  calc
    _ ≤ ∫ y in Ioc (0 : ℝ) ε, (A * V ε) * (v y * V (ε - y)) := by
      apply norm_integral_le_of_norm_le ((hi2.const_mul (A * V ε)).integrableOn)
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y hy => ?_)
      have ht : ε - y ∈ Icc (0 : ℝ) ε := ⟨sub_nonneg.mpr hy.2, by linarith only [hy.1]⟩
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _)]
      have hV0 := logarithmicRenewalMass_nonneg (ε - y)
      calc
        _ ≤ v y * (A * V (ε - y) ^ 2) :=
          mul_le_mul_of_nonneg_left (hedge _ ht) (logarithmicCausalKernel_nonneg _)
        _ ≤ v y * (A * (V ε * V (ε - y))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hA)
            (logarithmicCausalKernel_nonneg _)
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hmono ht.2) hV0
        _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul]
      rfl

/-! ### Scales -/

/-- The cumulative mass vanishes at the edge. -/
theorem tendsto_logarithmicRenewalMass_zero : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hn := tendsto_logarithmicRenewalMass_normalized
  have hL : Tendsto (fun x : ℝ => Real.log (1 / x)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hs : Tendsto (fun x : ℝ => (Real.sqrt (Real.log (1 / x)))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hL)
  have hp := hn.mul hs
  rw [mul_zero] at hp
  refine hp.congr' ?_
  filter_upwards [hL.eventually (eventually_gt_atTop 0)] with x hx
  have hsq : Real.sqrt (Real.log (1 / x)) ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  field_simp

private theorem tendsto_sqrt_sqrt : Tendsto (fun h : ℝ => Real.sqrt (Real.sqrt h)) (𝓝[>] (0 : ℝ))
    (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have hc : Continuous (fun h : ℝ => Real.sqrt (Real.sqrt h)) :=
      Real.continuous_sqrt.comp Real.continuous_sqrt
    have h := hc.tendsto 0
    simp only [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hh)

/-- The scale `ρ = h^{1/4}`: `V(ρ)²` is comparable with `1/log(1/h)`. -/
theorem tendsto_renewalMass_quarter_sq_mul_log :
    Tendsto (fun h : ℝ => V (Real.sqrt (Real.sqrt h)) ^ 2 * Real.log (1 / h)) (𝓝[>] (0 : ℝ))
      (𝓝 4) := by
  have hn := (tendsto_logarithmicRenewalMass_normalized.comp tendsto_sqrt_sqrt).pow 2
  have h4 := hn.const_mul 4
  rw [one_pow, mul_one] at h4
  refine h4.congr' ?_
  have hL : Tendsto (fun x : ℝ => Real.log (1 / x)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  filter_upwards [self_mem_nhdsWithin, hL.eventually (eventually_gt_atTop 0)] with h hh hlog
  have hh' : 0 < h := hh
  have hs : Real.log (1 / Real.sqrt (Real.sqrt h)) = Real.log (1 / h) / 4 := by
    rw [one_div, Real.log_inv, Real.log_sqrt (Real.sqrt_nonneg h), Real.log_sqrt hh'.le, one_div,
      Real.log_inv]
    ring
  simp only [Function.comp_apply]
  rw [mul_pow, Real.sq_sqrt (by rw [hs]; linarith only [hlog]), hs]
  ring

/-- The polynomial scale beats the logarithm: `h^{1/4} log(1/h) → 0`. -/
theorem tendsto_sqrt_sqrt_mul_log :
    Tendsto (fun h : ℝ => Real.sqrt (Real.sqrt h) * Real.log (1 / h)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hL : Tendsto (fun x : ℝ => -Real.log x / 4) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).atTop_div_const (by norm_num)
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hL
  have h4 := h1.const_mul 4
  rw [mul_zero] at h4
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  have hexp : Real.sqrt (Real.sqrt h) = Real.exp (-(-Real.log h / 4)) := by
    have hpos : 0 < Real.sqrt (Real.sqrt h) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hh')
    rw [← Real.exp_log hpos, Real.log_sqrt (Real.sqrt_nonneg h), Real.log_sqrt hh'.le]
    congr 1
    ring
  simp only [Function.comp_apply, pow_one]
  rw [hexp, one_div, Real.log_inv]
  ring

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
