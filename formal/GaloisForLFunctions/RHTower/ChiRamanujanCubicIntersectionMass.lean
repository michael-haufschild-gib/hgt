import GaloisForLFunctions.RHTower.ChiRamanujanCubicRegularSource
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Intersection mass of the complete BAG cubic trace

The literal intersection summand of the complete connected arithmetic trace has
compact-test boundary action `-pi^2 Phi(0,0)`. Both frequencies are scaled together;
the actual moving zeta/Euler source is bounded on the support of the test before
product-space dominated convergence. The other finite-part and mixed-PV summands
are not discarded and their joint boundary remains a separate obligation.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace RHTower.BAGTrace

private theorem continuousAt_realCubicSource_prod {x : ℝ × (ℝ × ℝ)} (hx : 1 ≤ x.1) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => realCubicSource z.1 z.2.1 z.2.2) x := by
  have he : Continuous (fun z : ℝ × (ℝ × ℝ) => ![z.1,z.2.1,z.2.2]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact ContinuousAt.comp (f := fun z : ℝ × (ℝ × ℝ) => ![z.1,z.2.1,z.2.2])
    (contDiffAt_realCubicSource (w := ![x.1,x.2.1,x.2.2]) hx).continuousAt he.continuousAt

private theorem continuous_realCubicSource_fixed {σ : ℝ} (hσ : 1 ≤ σ) :
    Continuous (fun w : ℝ × ℝ => realCubicSource σ w.1 w.2) := by
  apply continuous_iff_continuousAt.2
  intro w
  exact (continuousAt_realCubicSource_prod (x := (σ,w)) hσ).comp
    (continuous_const.prodMk continuous_id).continuousAt

/-- Compact tests bound the actual moving arithmetic source uniformly through the critical
plane. No bound on a hypothetical replacement source is assumed. -/
theorem exists_bound_tested_realCubicSource {Φ : ℝ × ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc (1 : ℝ) 2, ∀ w : ℝ × ℝ,
      ‖realCubicSource σ w.1 w.2 * Φ w‖ ≤ C := by
  have hc : IsCompact (Icc (1 : ℝ) 2 ×ˢ tsupport Φ) := isCompact_Icc.prod hΦc
  have hf : ContinuousOn
      (fun x : ℝ × (ℝ × ℝ) => realCubicSource x.1 x.2.1 x.2.2 * Φ x.2)
      (Icc (1 : ℝ) 2 ×ˢ tsupport Φ) := by
    intro x hx
    exact ((continuousAt_realCubicSource_prod hx.1.1).mul
      (hΦ.comp continuous_snd).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn hf
  refine ⟨max C 0, le_max_right _ _, fun σ hσ w => ?_⟩
  by_cases hw : Φ w = 0
  · simp only [hw, mul_zero, norm_zero]
    exact le_max_right _ _
  · exact (hC (σ,w) ⟨hσ, subset_closure hw⟩).trans (le_max_left _ _)

/-- Product Cauchy density without the normalization by pi squared. -/
def cubicIntersectionDensity (w : ℝ × ℝ) : ℝ :=
  (1+w.1^2)⁻¹*(1+w.2^2)⁻¹

private theorem continuous_cubicIntersectionDensity : Continuous cubicIntersectionDensity := by
  unfold cubicIntersectionDensity
  have h1 : Continuous (fun w : ℝ × ℝ => 1+w.1^2) := by fun_prop
  have h2 : Continuous (fun w : ℝ × ℝ => 1+w.2^2) := by fun_prop
  exact (h1.inv₀ (fun w => by positivity)).mul (h2.inv₀ (fun w => by positivity))

private theorem cubicIntersectionDensity_nonneg (w : ℝ × ℝ) :
    0 ≤ cubicIntersectionDensity w := by unfold cubicIntersectionDensity; positivity

theorem integrable_cubicIntersectionDensity : Integrable cubicIntersectionDensity :=
  integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq

theorem integral_cubicIntersectionDensity : ∫ w : ℝ × ℝ, cubicIntersectionDensity w = Real.pi^2 := by
  have h := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => (1+x^2)⁻¹) (fun x : ℝ => (1+x^2)⁻¹)
  have h' : (∫ w : ℝ × ℝ, cubicIntersectionDensity w) =
      (∫ x : ℝ, (1+x^2)⁻¹)*(∫ x : ℝ, (1+x^2)⁻¹) := by
    convert h using 1
    rfl
  rw [integral_univ_inv_one_add_sq] at h'
  simpa only [pow_two] using h'

/-- Simultaneous scaling of both frequencies gives the full intersection mass, even though
the zeta/Euler source itself moves with the damping parameter. -/
theorem tendsto_scaled_cubic_intersection {Φ : ℝ × ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,
      cubicIntersectionDensity w •
        (realCubicSource (1+ε) (ε*w.1) (ε*w.2) * Φ (ε • w)))
      (𝓝[>] 0) (𝓝 ((Real.pi^2 : ℝ) • Φ (0,0))) := by
  obtain ⟨C,hC0,hC⟩ := exists_bound_tested_realCubicSource hΦ hΦc
  have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 :=
    (eventually_mem_nhdsWithin).and ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
  have hlim (w : ℝ × ℝ) : Tendsto
      (fun ε : ℝ => realCubicSource (1+ε) (ε*w.1) (ε*w.2) * Φ (ε • w))
      (𝓝[>] 0) (𝓝 (Φ (0,0))) := by
    have he : Continuous (fun ε : ℝ => (1+ε,(ε*w.1,ε*w.2))) := by fun_prop
    have he0 : Tendsto (fun ε : ℝ => (1+ε,(ε*w.1,ε*w.2))) (𝓝[>] 0)
        (𝓝 (1,(0,0))) := by
      simpa using (he.tendsto 0).mono_left nhdsWithin_le_nhds
    have hs := (continuousAt_realCubicSource_prod (x := (1,(0,0))) (by norm_num)).tendsto.comp he0
    have hp0 : Tendsto (fun ε : ℝ => ε • w) (𝓝[>] 0) (𝓝 (0,0)) := by
      have hc : Continuous (fun ε : ℝ => ε • w) := continuous_id.smul continuous_const
      have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simp only [zero_smul] at h
      convert h using 1
      rfl
    have hp := (hΦ.tendsto (0,0)).comp hp0
    have h := hs.mul hp
    simp only [realCubicSource_intersection, one_mul, Function.comp_def] at h
    convert h using 1
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun w : ℝ × ℝ => cubicIntersectionDensity w •
        (realCubicSource (1+ε) (ε*w.1) (ε*w.2) * Φ (ε • w))) := by
    filter_upwards [hε] with ε he
    have hec : Continuous (fun w : ℝ × ℝ => ε • w) := by
      change Continuous (fun w : ℝ × ℝ => (ε*w.1,ε*w.2))
      fun_prop
    have hs := (continuous_realCubicSource_fixed (σ := 1+ε) (by linarith)).comp hec
    exact (continuous_cubicIntersectionDensity.smul (hs.mul (hΦ.comp hec))).aestronglyMeasurable
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ w : ℝ × ℝ,
      ‖cubicIntersectionDensity w •
        (realCubicSource (1+ε) (ε*w.1) (ε*w.2) * Φ (ε • w))‖ ≤
          cubicIntersectionDensity w*C := by
    filter_upwards [hε] with ε he
    exact ae_of_all _ fun w => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cubicIntersectionDensity_nonneg w)]
      exact mul_le_mul_of_nonneg_left
        (hC (1+ε) ⟨by linarith, by linarith⟩ (ε • w)) (cubicIntersectionDensity_nonneg w)
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun ε w => cubicIntersectionDensity w •
      (realCubicSource (1+ε) (ε*w.1) (ε*w.2) * Φ (ε • w)))
    (f := fun w => cubicIntersectionDensity w • Φ (0,0))
    (fun w => cubicIntersectionDensity w*C) hmeas hbound
    (integrable_cubicIntersectionDensity.mul_const C)
    (ae_of_all _ fun w => (hlim w).const_smul _)
  simpa only [integral_smul_const, integral_cubicIntersectionDensity] using ht

/-- Literal intersection kernel from the complete connected trace. -/
def cubicIntersectionKernel (ε : ℝ) (w : ℝ × ℝ) : ℝ :=
  ε^2/((ε^2+w.1^2)*(ε^2+w.2^2))

private theorem continuous_cubicIntersectionKernel {ε : ℝ} (hε : 0 < ε) :
    Continuous (cubicIntersectionKernel ε) := by
  have h1 : Continuous (fun w : ℝ × ℝ => ε^2+w.1^2) := by fun_prop
  have h2 : Continuous (fun w : ℝ × ℝ => ε^2+w.2^2) := by fun_prop
  exact continuous_const.div (h1.mul h2) (fun w => by positivity)

theorem integrable_tested_cubicIntersectionKernel {ε : ℝ} (hε : 0 < ε)
    {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    Integrable (fun w : ℝ × ℝ => cubicIntersectionKernel ε w •
      (realCubicSource (1+ε) w.1 w.2 * Φ w)) := by
  have hc := (continuous_cubicIntersectionKernel hε).smul
    ((continuous_realCubicSource_fixed (σ := 1+ε) (by linarith)).mul hΦ)
  have hs0 := hΦc.mul_left (f := fun w : ℝ × ℝ => realCubicSource (1+ε) w.1 w.2)
  have hs : HasCompactSupport (fun w : ℝ × ℝ => cubicIntersectionKernel ε w •
      (realCubicSource (1+ε) w.1 w.2 * Φ w)) := by
    convert hs0.smul_left (f := cubicIntersectionKernel ε) using 1 <;> rfl
  exact hc.integrable_of_hasCompactSupport hs

private theorem cubicIntersectionKernel_scale {ε : ℝ} (hε : ε ≠ 0) (w : ℝ × ℝ) :
    ε^2*cubicIntersectionKernel ε (ε • w) = cubicIntersectionDensity w := by
  dsimp [cubicIntersectionKernel, cubicIntersectionDensity]
  field_simp

/-- Exact change of variables in the actual-source pairing, before taking any limit. -/
theorem integral_cubicIntersectionKernel_scale {ε : ℝ} (hε : 0 < ε) (Φ : ℝ × ℝ → ℂ) :
    (∫ w : ℝ × ℝ, cubicIntersectionKernel ε w •
      (realCubicSource (1+ε) w.1 w.2 * Φ w)) =
    ∫ w : ℝ × ℝ, cubicIntersectionDensity w •
      (realCubicSource (1+ε) (ε*w.1) (ε*w.2) * Φ (ε • w)) := by
  let f : ℝ × ℝ → ℂ := fun w => cubicIntersectionKernel ε w •
    (realCubicSource (1+ε) w.1 w.2 * Φ w)
  have h := Measure.integral_comp_smul_of_nonneg volume f ε (hR := hε.le)
  norm_num only [Module.finrank_prod, Module.finrank_self] at h
  have hi : (∫ w, f w) = ε^2 • ∫ w, f (ε • w) := by
    rw [h, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hε.ne'), one_smul]
  rw [hi, ← integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    dsimp only [f]
    rw [smul_smul, cubicIntersectionKernel_scale hε.ne']
    rfl

/-- The actual cubic intersection term converges to pi squared times the point mass at
zero. In the complete signed trace this term appears with a minus sign. -/
theorem tendsto_cubic_intersection {Φ : ℝ × ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ, cubicIntersectionKernel ε w •
      (realCubicSource (1+ε) w.1 w.2 * Φ w))
      (𝓝[>] 0) (𝓝 ((Real.pi^2 : ℝ) • Φ (0,0))) := by
  apply (tendsto_scaled_cubic_intersection hΦ hΦc).congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  exact (integral_cubicIntersectionKernel_scale hε Φ).symm

/-- Identification with the literal complex-valued intersection summand of the full trace. -/
theorem cubicIntersectionKernel_smul (ε : ℝ) (w : ℝ × ℝ) (A z : ℂ) :
    cubicIntersectionKernel ε w • (A*z) =
      ((ε : ℂ)^2*A / (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)))*z := by
  change (((ε^2/((ε^2+w.1^2)*(ε^2+w.2^2)) : ℝ) : ℂ)*(A*z)) = _
  rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul]
  ring

/-- The signed intersection summand of the complete connected arithmetic trace has
boundary action `-pi^2 Phi(0,0)`. The full finite-part/PV boundary is a separate obligation. -/
theorem tendsto_literal_signed_cubic_intersection {Φ : ℝ × ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,
      -(((ε : ℂ)^2*realCubicSource (1+ε) w.1 w.2 /
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)))*Φ w))
      (𝓝[>] 0) (𝓝 (-((Real.pi^2 : ℝ) : ℂ)*Φ (0,0))) := by
  have h := (tendsto_cubic_intersection hΦ hΦc).neg
  have heq (ε : ℝ) :
      (∫ w : ℝ × ℝ, -(((ε : ℂ)^2*realCubicSource (1+ε) w.1 w.2 /
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)))*Φ w)) =
      -(∫ w : ℝ × ℝ, cubicIntersectionKernel ε w •
        (realCubicSource (1+ε) w.1 w.2 * Φ w)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ fun w => congrArg Neg.neg
      (cubicIntersectionKernel_smul ε w (realCubicSource (1+ε) w.1 w.2) (Φ w)).symm
  simp_rw [heq]
  convert h using 1
  simp only [Complex.real_smul, neg_mul]

end RHTower.BAGTrace
