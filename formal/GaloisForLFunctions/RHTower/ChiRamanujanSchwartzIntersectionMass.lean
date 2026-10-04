import GaloisForLFunctions.RHTower.ChiRamanujanSchwartzSourceDecay

/-!
# Noncompact Schwartz boundary of the actual BAG intersection term

The actual moving source, uniformly controlled by proved Schwartz seminorms,
retains its full signed intersection mass. The tested pairings are integrable
near the critical damping. Finite parts and product PV are separate terms.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff SchwartzMap
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

private theorem continuous_cubicIntersectionDensity : Continuous cubicIntersectionDensity := by
  unfold cubicIntersectionDensity
  have h1 : Continuous (fun w : ℝ × ℝ => 1+w.1^2) := by fun_prop
  have h2 : Continuous (fun w : ℝ × ℝ => 1+w.2^2) := by fun_prop
  exact (h1.inv₀ (fun w => by positivity)).mul (h2.inv₀ (fun w => by positivity))

private theorem cubicIntersectionDensity_nonneg (w : ℝ × ℝ) :
    0 ≤ cubicIntersectionDensity w := by unfold cubicIntersectionDensity; positivity

theorem tendsto_schwartz_scaled_cubic_intersection (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,
      cubicIntersectionDensity w •
        (realCubicSource (1+ε) (ε*w.1) (ε*w.2) * Φ (ε • w)))
      (𝓝[>] 0) (𝓝 ((Real.pi^2 : ℝ) • Φ (0,0))) := by
  have hΦ : Continuous (Φ : ℝ × ℝ → ℂ) := Φ.continuous
  obtain ⟨C,hC0,hC⟩ := exists_bound_schwartz_realCubicSource Φ
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

theorem tendsto_schwartz_cubic_intersection (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ, cubicIntersectionKernel ε w •
      (realCubicSource (1+ε) w.1 w.2 * Φ w))
      (𝓝[>] 0) (𝓝 ((Real.pi^2 : ℝ) • Φ (0,0))) := by
  apply (tendsto_schwartz_scaled_cubic_intersection Φ).congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  exact (integral_cubicIntersectionKernel_scale hε Φ).symm

theorem tendsto_schwartz_literal_signed_cubic_intersection (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,
      -(((ε : ℂ)^2*realCubicSource (1+ε) w.1 w.2 /
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)))*Φ w))
      (𝓝[>] 0) (𝓝 (-((Real.pi^2 : ℝ) : ℂ)*Φ (0,0))) := by
  have h := (tendsto_schwartz_cubic_intersection Φ).neg
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

private theorem cubicIntersectionKernel_scale_point {ε : ℝ} (hε : ε ≠ 0) (w : ℝ × ℝ) :
    ε^2*cubicIntersectionKernel ε (ε • w) = cubicIntersectionDensity w := by
  dsimp [cubicIntersectionKernel,cubicIntersectionDensity]
  field_simp

/-- The literal intersection kernel is integrable for every positive damping. -/
theorem integrable_cubicIntersectionKernel {ε : ℝ} (hε : 0 < ε) :
    Integrable (cubicIntersectionKernel ε) := by
  have hi := (integrable_cubicIntersectionDensity.comp_smul (inv_ne_zero hε.ne')).const_mul ((ε^2)⁻¹)
  convert hi using 1
  funext w
  rw [← cubicIntersectionKernel_scale_point hε.ne' (ε⁻¹ • w),smul_smul,
    mul_inv_cancel₀ hε.ne',one_smul,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hε.ne'),one_mul]

/-- Noncompact tested intersection pairings are genuine integrable pairings near the boundary. -/
theorem integrable_schwartz_cubicIntersectionKernel (Φ : 𝓢(ℝ × ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun w : ℝ × ℝ => cubicIntersectionKernel ε w •
      (realCubicSource (1+ε) w.1 w.2*Φ w)) := by
  obtain ⟨C,hC0,hC⟩ := exists_bound_schwartz_realCubicSource Φ
  have hcK : Continuous (cubicIntersectionKernel ε) := by
    have h1 : Continuous (fun w : ℝ × ℝ => ε^2+w.1^2) := by fun_prop
    have h2 : Continuous (fun w : ℝ × ℝ => ε^2+w.2^2) := by fun_prop
    exact continuous_const.div (h1.mul h2) (fun w => by positivity)
  have hc := hcK.smul ((continuous_realCubicSource_fixed (σ := 1+ε) (by linarith)).mul Φ.continuous)
  apply ((integrable_cubicIntersectionKernel hε).mul_const C).mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun w => by
    have hK : 0 ≤ cubicIntersectionKernel ε w := by unfold cubicIntersectionKernel; positivity
    change ‖cubicIntersectionKernel ε w • (realCubicSource (1+ε) w.1 w.2*Φ w)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left (hC (1+ε) ⟨by linarith,by linarith⟩ w) hK

end RHTower.BAGTrace
