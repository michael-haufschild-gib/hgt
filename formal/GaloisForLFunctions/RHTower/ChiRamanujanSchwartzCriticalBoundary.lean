import GaloisForLFunctions.RHTower.ChiRamanujanSchwartzQuotientBounds
import GaloisForLFunctions.RHTower.ChiRamanujanSchwartzIntersectionMass
import GaloisForLFunctions.RHTower.ChiRamanujanRationalCriticalBoundary

/-!
# Complete Schwartz critical boundary of the actual BAG rational cubic

Proved integrable full-plane envelopes give the two finite parts and product
principal value. Original-kernel integrability justifies exact reflection
averages; joint concentration retains the signed intersection mass. The
complete tested rational series is identified before taking the critical
limit. Physical contraction matching and coupled height limits remain separate.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology SchwartzMap
namespace RHTower.BAGTrace

private theorem continuous_cubicMixedDifference {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) : Continuous (cubicMixedDifference Φ σ) := by
  have hs := continuous_cubicTestedSlice hΦ hσ
  have h1 : Continuous (fun w : ℝ × ℝ => (-w.1,w.2)) := by fun_prop
  have h2 : Continuous (fun w : ℝ × ℝ => (w.1,-w.2)) := by fun_prop
  have h12 : Continuous (fun w : ℝ × ℝ => (-w.1,-w.2)) := by fun_prop
  convert ((hs.sub (hs.comp h1)).sub (hs.comp h2)).add (hs.comp h12) using 1
  rfl

private theorem continuousAt_cubicTestedParameter {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) (u v : ℝ) :
    ContinuousAt (fun τ : ℝ => cubicTestedSource Φ ![τ,u,v]) σ := by
  have he : Continuous (fun τ : ℝ => ![τ,u,v]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact ContinuousAt.comp (f := fun τ : ℝ => ![τ,u,v])
    (contDiffAt_cubicTestedSource hΦ (w := ![σ,u,v]) hσ).continuousAt he.continuousAt

private theorem continuousAt_cubicMixedParameter {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) (w : ℝ × ℝ) :
    ContinuousAt (fun τ : ℝ => cubicMixedDifference Φ τ w) σ :=
  (((continuousAt_cubicTestedParameter hΦ hσ w.1 w.2).sub
    (continuousAt_cubicTestedParameter hΦ hσ (-w.1) w.2)).sub
    (continuousAt_cubicTestedParameter hΦ hσ w.1 (-w.2))).add
    (continuousAt_cubicTestedParameter hΦ hσ (-w.1) (-w.2))

private theorem measurable_cubicMixedQuotient {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) : Measurable (cubicMixedQuotient Φ σ) := by
  have hc : Continuous (fun w : ℝ × ℝ => ((w.1*w.2 : ℝ) : ℂ)) := by fun_prop
  convert (continuous_cubicMixedDifference hΦ hσ).measurable.div hc.measurable using 1
  rfl

private theorem cubicDampingFactor_nonneg (ε u : ℝ) : 0 ≤ cubicDampingFactor ε u := by
  unfold cubicDampingFactor
  positivity

private theorem cubicDampingFactor_le_one (ε u : ℝ) : cubicDampingFactor ε u ≤ 1 := by
  unfold cubicDampingFactor
  exact div_le_one_of_le₀ (by nlinarith [sq_nonneg ε]) (by positivity)

private theorem continuous_cubicDampingFactor {ε : ℝ} (hε : 0 < ε) :
    Continuous (cubicDampingFactor ε) := by
  exact (continuous_id.pow 2).div (continuous_const.add (continuous_id.pow 2))
    (fun u => by positivity)

private theorem tendsto_cubicDampingFactor {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun ε : ℝ => cubicDampingFactor ε u) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun ε : ℝ => u^2/(ε^2+u^2)) 0 :=
    continuousAt_const.div ((continuousAt_id.pow 2).add continuousAt_const)
      (by simpa using pow_ne_zero 2 hu)
  simpa [cubicDampingFactor, hu] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

private theorem tendsto_damped_cubicMixedQuotient {Φ : ℝ × ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (w : ℝ × ℝ) :
    Tendsto (fun ε : ℝ => (cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) •
      cubicMixedQuotient Φ (1+ε) w) (𝓝[>] 0) (𝓝 (cubicMixedQuotient Φ 1 w)) := by
  by_cases hu : w.1=0
  · simp [cubicDampingFactor,cubicMixedQuotient,hu]
  by_cases hv : w.2=0
  · simp [cubicDampingFactor,cubicMixedQuotient,hv]
  have hq : ContinuousAt (fun σ : ℝ => cubicMixedQuotient Φ σ w) 1 :=
    (continuousAt_cubicMixedParameter hΦ (by norm_num) w).div_const _
  have he : Tendsto (fun ε : ℝ => 1+ε) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun ε : ℝ => 1+ε) := by fun_prop
    simpa only [add_zero] using (hc.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h := ((tendsto_cubicDampingFactor hu).mul (tendsto_cubicDampingFactor hv)).smul
    (hq.tendsto.comp he)
  simpa only [one_mul,one_smul,Function.comp_def] using h

private theorem continuous_cubicAxisDifference {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) : Continuous (cubicAxisDifference Φ σ) := by
  have hs := continuous_cubicTestedAxisSlice hΦ hσ
  have h1 : Continuous (fun w : ℝ × ℝ => (-w.1,w.2)) := by fun_prop
  convert hs.add (hs.comp h1) using 1
  rfl

private theorem continuousAt_cubicAxisTestParameter {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) (u v : ℝ) :
    ContinuousAt (fun τ : ℝ => cubicTestedAxisNumerator Φ ![τ,u,v]) σ := by
  have he : Continuous (fun τ : ℝ => ![τ,u,v]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact ContinuousAt.comp (f := fun τ : ℝ => ![τ,u,v])
    (contDiffAt_cubicTestedAxisNumerator hΦ (w := ![σ,u,v]) hσ).continuousAt he.continuousAt

private theorem continuousAt_cubicAxisParameter {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) (w : ℝ × ℝ) :
    ContinuousAt (fun τ : ℝ => cubicAxisDifference Φ τ w) σ :=
  (continuousAt_cubicAxisTestParameter hΦ hσ w.1 w.2).add
    (continuousAt_cubicAxisTestParameter hΦ hσ (-w.1) w.2)

private theorem measurable_cubicAxisQuotient {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) : Measurable (cubicAxisQuotient Φ σ) := by
  have hc : Continuous (fun w : ℝ × ℝ => ((w.1^2 : ℝ) : ℂ)) := by fun_prop
  convert (continuous_cubicAxisDifference hΦ hσ).measurable.div hc.measurable using 1
  rfl

private theorem tendsto_damped_cubicAxisQuotient {Φ : ℝ × ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (w : ℝ × ℝ) :
    Tendsto (fun ε : ℝ => cubicDampingFactor ε w.1 • cubicAxisQuotient Φ (1+ε) w)
      (𝓝[>] 0) (𝓝 (cubicAxisQuotient Φ 1 w)) := by
  by_cases hu : w.1=0
  · simp [cubicDampingFactor,cubicAxisQuotient,hu]
  have hq : ContinuousAt (fun σ : ℝ => cubicAxisQuotient Φ σ w) 1 :=
    (continuousAt_cubicAxisParameter hΦ (by norm_num) w).div_const _
  have he : Tendsto (fun ε : ℝ => 1+ε) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun ε : ℝ => 1+ε) := by fun_prop
    simpa only [add_zero] using (hc.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h := (tendsto_cubicDampingFactor hu).smul (hq.tendsto.comp he)
  simpa only [one_smul,Function.comp_def] using h

private theorem norm_damped_axis_le (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) :
    ‖cubicDampingFactor ε w.1 • cubicAxisQuotient Φ (1+ε) w‖ ≤
      ‖cubicAxisQuotient Φ (1+ε) w‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (cubicDampingFactor_nonneg ε w.1)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cubicDampingFactor_le_one ε w.1)

private theorem norm_damped_mixed_le (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) :
    ‖(cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) • cubicMixedQuotient Φ (1+ε) w‖ ≤
      ‖cubicMixedQuotient Φ (1+ε) w‖ := by
  have h0 := mul_nonneg (cubicDampingFactor_nonneg ε w.1) (cubicDampingFactor_nonneg ε w.2)
  have h1 : cubicDampingFactor ε w.1*cubicDampingFactor ε w.2 ≤ 1 :=
    mul_le_one₀ (cubicDampingFactor_le_one ε w.1) (cubicDampingFactor_nonneg ε w.2)
      (cubicDampingFactor_le_one ε w.2)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg h0]
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/-- Both critical quotients are genuine integrable functions on the whole plane. -/
theorem integrable_schwartz_cubicQuotients (Φ : 𝓢(ℝ × ℝ, ℂ))
    {σ : ℝ} (hσ : σ ∈ Icc (1 : ℝ) 2) :
    Integrable (cubicAxisQuotient Φ σ) ∧ Integrable (cubicMixedQuotient Φ σ) := by
  obtain ⟨C,_hC,hb⟩ := exists_schwartz_cubicQuotients_global_bound
  have hi := integrable_cubicIntersectionDensity.const_mul (C*cubicSchwartzSeminorm 76 2 Φ)
  exact ⟨hi.mono' (measurable_cubicAxisQuotient (Φ.smooth (⊤ : ℕ∞)) hσ.1).aestronglyMeasurable
      (ae_of_all _ fun w => (hb Φ σ hσ w).1),
    hi.mono' (measurable_cubicMixedQuotient (Φ.smooth (⊤ : ℕ∞)) hσ.1).aestronglyMeasurable
      (ae_of_all _ fun w => (hb Φ σ hσ w).2)⟩

/-- The first reflected finite part has a full noncompact critical limit. -/
theorem tendsto_integral_schwartz_cubicAxisQuotient (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,
      cubicDampingFactor ε w.1 • cubicAxisQuotient Φ (1+ε) w)
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ,cubicAxisQuotient Φ 1 w)) := by
  obtain ⟨C,_hC,hb⟩ := exists_schwartz_cubicQuotients_global_bound
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 :=
    eventually_mem_nhdsWithin.and
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
  have hm : ∀ᶠ ε : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun w : ℝ × ℝ => cubicDampingFactor ε w.1 • cubicAxisQuotient Φ (1+ε) w) := by
    filter_upwards [he] with ε hε
    have hd : Continuous (fun w : ℝ × ℝ => cubicDampingFactor ε w.1) :=
      (continuous_cubicDampingFactor hε.1).comp continuous_fst
    exact (hd.measurable.smul (measurable_cubicAxisQuotient (Φ.smooth (⊤ : ℕ∞))
      (by linarith [hε.1]))).aestronglyMeasurable
  have hb' : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ w : ℝ × ℝ,
      ‖cubicDampingFactor ε w.1 • cubicAxisQuotient Φ (1+ε) w‖ ≤
        C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity w := by
    filter_upwards [he] with ε hε
    exact ae_of_all _ fun w => (norm_damped_axis_le Φ ε w).trans
      (hb Φ (1+ε) ⟨by linarith [hε.1],by linarith [hε.2]⟩ w).1
  exact tendsto_integral_filter_of_dominated_convergence
    (fun w => C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity w) hm hb'
    (integrable_cubicIntersectionDensity.const_mul _)
    (ae_of_all _ fun w => tendsto_damped_cubicAxisQuotient (Φ.smooth (⊤ : ℕ∞)) w)

/-- The product principal value has a full noncompact critical limit. -/
theorem tendsto_integral_schwartz_cubicMixedQuotient (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,
      (cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) • cubicMixedQuotient Φ (1+ε) w)
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ,cubicMixedQuotient Φ 1 w)) := by
  obtain ⟨C,_hC,hb⟩ := exists_schwartz_cubicQuotients_global_bound
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 :=
    eventually_mem_nhdsWithin.and
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
  have hm : ∀ᶠ ε : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun w : ℝ × ℝ => (cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) •
        cubicMixedQuotient Φ (1+ε) w) := by
    filter_upwards [he] with ε hε
    have hd := continuous_cubicDampingFactor hε.1
    exact (((hd.comp continuous_fst).mul (hd.comp continuous_snd)).measurable.smul
      (measurable_cubicMixedQuotient (Φ.smooth (⊤ : ℕ∞))
      (by linarith [hε.1]))).aestronglyMeasurable
  have hb' : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ w : ℝ × ℝ,
      ‖(cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) • cubicMixedQuotient Φ (1+ε) w‖ ≤
        C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity w := by
    filter_upwards [he] with ε hε
    exact ae_of_all _ fun w => (norm_damped_mixed_le Φ ε w).trans
      (hb Φ (1+ε) ⟨by linarith [hε.1],by linarith [hε.2]⟩ w).2
  exact tendsto_integral_filter_of_dominated_convergence
    (fun w => C*cubicSchwartzSeminorm 76 2 Φ*cubicIntersectionDensity w) hm hb'
    (integrable_cubicIntersectionDensity.const_mul _)
    (ae_of_all _ fun w => tendsto_damped_cubicMixedQuotient (Φ.smooth (⊤ : ℕ∞)) w)

theorem tendsto_integral_schwartz_literal_cubicAxis (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,
      cubicAxisDifference Φ (1+ε) w / ((ε^2+w.1^2 : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ,cubicAxisQuotient Φ 1 w)) := by
  apply (tendsto_integral_schwartz_cubicAxisQuotient Φ).congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  exact ae_of_all _ fun w => damped_cubicAxisQuotient_eq hε Φ w

theorem tendsto_integral_schwartz_literal_cubicMixed (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,
      ((w.1 : ℂ)*(w.2 : ℂ)*cubicMixedDifference Φ (1+ε) w) /
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)))
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ,cubicMixedQuotient Φ 1 w)) := by
  apply (tendsto_integral_schwartz_cubicMixedQuotient Φ).congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  exact ae_of_all _ fun w => damped_cubicMixedQuotient_eq hε Φ w

private theorem continuous_cubicMixedKernel {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {ε : ℝ} (hε : 0 < ε) : Continuous (cubicMixedKernel Φ ε) := by
  have hn : Continuous (fun w : ℝ × ℝ =>
      (w.1 : ℂ)*(w.2 : ℂ)*cubicTestedSource Φ ![1+ε,w.1,w.2]) :=
    ((Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_ofReal.comp continuous_snd)).mul
      (continuous_cubicTestedSlice hΦ (by linarith))
  have hd : Continuous (fun w : ℝ × ℝ =>
      (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ))) := by fun_prop
  apply hn.div hd
  intro w
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt (show 0 < ε^2+w.1^2 by positivity))
  · exact_mod_cast (ne_of_gt (show 0 < ε^2+w.2^2 by positivity))

private theorem continuous_cubicAxisKernel {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {ε : ℝ} (hε : 0 < ε) : Continuous (cubicAxisKernel Φ ε) := by
  have hn := continuous_cubicTestedAxisSlice hΦ (σ := 1+ε) (by linarith)
  have hd : Continuous (fun w : ℝ × ℝ => ((ε^2+w.1^2 : ℝ) : ℂ)) := by fun_prop
  exact hn.div hd (fun w => by exact_mod_cast (ne_of_gt (show 0 < ε^2+w.1^2 by positivity)))

private theorem cubicMixedKernel_reflections (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) :
    cubicMixedKernel Φ ε w+cubicMixedKernel Φ ε (-w.1,w.2)+
      (cubicMixedKernel Φ ε (w.1,-w.2)+cubicMixedKernel Φ ε (-w.1,-w.2)) =
      ((w.1 : ℂ)*(w.2 : ℂ)*cubicMixedDifference Φ (1+ε) w) /
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)) := by
  dsimp only [cubicMixedKernel,cubicMixedDifference]
  simp only [neg_sq,Complex.ofReal_neg]
  ring

private theorem cubicAxisKernel_reflection (Φ : ℝ × ℝ → ℂ) (ε : ℝ) (w : ℝ × ℝ) :
    cubicAxisKernel Φ ε w+cubicAxisKernel Φ ε (-w.1,w.2) =
      cubicAxisDifference Φ (1+ε) w / ((ε^2+w.1^2 : ℝ) : ℂ) := by
  dsimp only [cubicAxisKernel,cubicAxisDifference]
  simp only [neg_sq]
  ring

private theorem norm_frequency_cauchy_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    |u|/(ε^2+u^2) ≤ 1/ε := by
  apply (div_le_div_iff₀ (by positivity : 0 < ε^2+u^2) hε).mpr
  nlinarith [sq_nonneg (ε-|u|),sq_abs u]

private theorem norm_cubicMixedKernel_le (Φ : ℝ × ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (w : ℝ × ℝ) :
    ‖cubicMixedKernel Φ ε w‖ ≤ (ε^2)⁻¹*‖cubicTestedSource Φ ![1+ε,w.1,w.2]‖ := by
  have hu : 0 < ε^2+w.1^2 := by positivity
  have hv : 0 < ε^2+w.2^2 := by positivity
  have hr : 0 ≤ |w.2|/(ε^2+w.2^2) := by positivity
  have hb := mul_le_mul (norm_frequency_cauchy_le hε w.1)
    (norm_frequency_cauchy_le hε w.2) hr (by positivity : 0 ≤ 1/ε)
  have hn := mul_le_mul_of_nonneg_right hb (norm_nonneg (cubicTestedSource Φ ![1+ε,w.1,w.2]))
  simp only [cubicMixedKernel,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hu,abs_of_pos hv]
  calc
    _ = (|w.1|/(ε^2+w.1^2))*(|w.2|/(ε^2+w.2^2))*
        ‖cubicTestedSource Φ ![1+ε,w.1,w.2]‖ := by
      simp only [div_eq_mul_inv,mul_inv]
      ring
    _ ≤ (1/ε)*(1/ε)*‖cubicTestedSource Φ ![1+ε,w.1,w.2]‖ := hn
    _ = _ := by simp only [one_div,← pow_two,← inv_pow]

/-- Both original, unreflected singular kernels are integrable at every nearby positive damping. -/
theorem integrable_schwartz_cubicKernels (Φ : 𝓢(ℝ × ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (cubicAxisKernel Φ ε) ∧ Integrable (cubicMixedKernel Φ ε) := by
  obtain ⟨C,_hC,hb⟩ := exists_schwartz_testedSources_density_bound
  let D := C*cubicSchwartzSeminorm 76 2 Φ
  have hi := integrable_cubicIntersectionDensity.const_mul ((ε^2)⁻¹*D)
  have hσ : 1+ε ∈ Icc (1 : ℝ) 2 := ⟨by linarith,by linarith⟩
  have hε2 : 0 < ε^2 := sq_pos_of_pos hε
  constructor
  · apply hi.mono' (continuous_cubicAxisKernel (Φ.smooth (⊤ : ℕ∞)) hε).aestronglyMeasurable
    exact ae_of_all _ fun w => by
      have hd : 0 < ε^2+w.1^2 := by positivity
      change ‖cubicAxisKernel Φ ε w‖ ≤ _
      rw [cubicAxisKernel,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
      calc
        _ ≤ ‖cubicTestedAxisNumerator Φ ![1+ε,w.1,w.2]‖/ε^2 :=
          div_le_div₀ (norm_nonneg _) le_rfl hε2 (by nlinarith [sq_nonneg w.1])
        _ ≤ (D*cubicIntersectionDensity w)/ε^2 :=
          div_le_div_of_nonneg_right (hb Φ (1+ε) hσ w).2 hε2.le
        _ = _ := by dsimp only [D]; ring
  · apply hi.mono' (continuous_cubicMixedKernel (Φ.smooth (⊤ : ℕ∞)) hε).aestronglyMeasurable
    exact ae_of_all _ fun w => by
      change ‖cubicMixedKernel Φ ε w‖ ≤ _
      exact (norm_cubicMixedKernel_le Φ hε w).trans (by
        simpa only [D,mul_assoc] using mul_le_mul_of_nonneg_left
          (hb Φ (1+ε) hσ w).1 (inv_nonneg.mpr hε2.le))

private def firstReflection : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)

private def secondReflection : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)

private theorem firstReflection_preserving : MeasurePreserving firstReflection :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id volume)

private theorem secondReflection_preserving : MeasurePreserving secondReflection :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg volume)

private theorem integral_firstReflection (f : ℝ × ℝ → ℂ) :
    (∫ w : ℝ × ℝ,f (-w.1,w.2))=∫ w : ℝ × ℝ,f w :=
  firstReflection_preserving.integral_comp firstReflection.measurableEmbedding f

private theorem integral_secondReflection (f : ℝ × ℝ → ℂ) :
    (∫ w : ℝ × ℝ,f (w.1,-w.2))=∫ w : ℝ × ℝ,f w :=
  secondReflection_preserving.integral_comp secondReflection.measurableEmbedding f

/-- Exact full-plane reflection formula for the first finite part. -/
theorem integral_schwartz_cubicAxisKernel_eq_reflected (Φ : 𝓢(ℝ × ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ w : ℝ × ℝ,cubicAxisKernel Φ ε w) = (2 : ℂ)⁻¹*
      (∫ w : ℝ × ℝ,cubicAxisDifference Φ (1+ε) w/((ε^2+w.1^2 : ℝ) : ℂ)) := by
  have hi := (integrable_schwartz_cubicKernels Φ hε hε1).1
  have hr := firstReflection_preserving.integrable_comp_of_integrable hi
  change Integrable (fun w : ℝ × ℝ => cubicAxisKernel Φ ε (-w.1,w.2)) at hr
  have he : (∫ w : ℝ × ℝ,cubicAxisDifference Φ (1+ε) w/((ε^2+w.1^2 : ℝ) : ℂ)) =
      2*(∫ w : ℝ × ℝ,cubicAxisKernel Φ ε w) := by
    simp_rw [← cubicAxisKernel_reflection]
    rw [integral_add hi hr,integral_firstReflection]
    ring
  rw [he]
  ring

/-- Exact full-plane reflection formula retaining all four signed mixed quadrants. -/
theorem integral_schwartz_cubicMixedKernel_eq_reflected (Φ : 𝓢(ℝ × ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ w : ℝ × ℝ,cubicMixedKernel Φ ε w) = (4 : ℂ)⁻¹*
      (∫ w : ℝ × ℝ,((w.1 : ℂ)*(w.2 : ℂ)*cubicMixedDifference Φ (1+ε) w)/
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ))) := by
  have hi := (integrable_schwartz_cubicKernels Φ hε hε1).2
  have hr1 := firstReflection_preserving.integrable_comp_of_integrable hi
  have hr2 := secondReflection_preserving.integrable_comp_of_integrable hi
  have hr12 := firstReflection_preserving.integrable_comp_of_integrable hr2
  change Integrable (fun w : ℝ × ℝ => cubicMixedKernel Φ ε (-w.1,w.2)) at hr1
  change Integrable (fun w : ℝ × ℝ => cubicMixedKernel Φ ε (w.1,-w.2)) at hr2
  change Integrable (fun w : ℝ × ℝ => cubicMixedKernel Φ ε (-w.1,-w.2)) at hr12
  have hi1 : Integrable (fun w : ℝ × ℝ => cubicMixedKernel Φ ε w+cubicMixedKernel Φ ε (-w.1,w.2)) := hi.add hr1
  have hi2 : Integrable (fun w : ℝ × ℝ => cubicMixedKernel Φ ε (w.1,-w.2)+cubicMixedKernel Φ ε (-w.1,-w.2)) := hr2.add hr12
  have he : (∫ w : ℝ × ℝ,((w.1 : ℂ)*(w.2 : ℂ)*cubicMixedDifference Φ (1+ε) w)/
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ))) =
      4*(∫ w : ℝ × ℝ,cubicMixedKernel Φ ε w) := by
    simp_rw [← cubicMixedKernel_reflections]
    rw [integral_add hi1 hi2,integral_add hi hr1,integral_add hr2 hr12,
      integral_firstReflection,integral_secondReflection,
      integral_firstReflection (fun w => cubicMixedKernel Φ ε (w.1,-w.2)),integral_secondReflection]
    ring
  rw [he]
  ring

/-- Coordinate exchange of a Schwartz frequency test. -/
def cubicSchwartzSwap (Φ : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) Φ

theorem cubicSchwartzSwap_apply (Φ : 𝓢(ℝ × ℝ, ℂ)) (w : ℝ × ℝ) :
    cubicSchwartzSwap Φ w=Φ (w.2,w.1) := rfl

private theorem cubicOtherAxisKernel_swap (Φ : 𝓢(ℝ × ℝ, ℂ)) (ε : ℝ) (w : ℝ × ℝ) :
    cubicOtherAxisKernel Φ ε w=cubicAxisKernel (cubicSchwartzSwap Φ) ε (w.2,w.1) := by
  change (realCubicSource (1+ε) w.1 w.2-realAxisSource (1+ε) w.2)*Φ w/((ε^2+w.2^2 : ℝ) : ℂ) =
    (realCubicSource (1+ε) w.2 w.1-realAxisSource (1+ε) w.2)*Φ w/((ε^2+w.2^2 : ℝ) : ℂ)
  rw [realCubicSource_swap (1+ε) w.2 w.1]

theorem integrable_schwartz_cubicOtherAxisKernel (Φ : 𝓢(ℝ × ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : Integrable (cubicOtherAxisKernel Φ ε) := by
  have he : cubicOtherAxisKernel Φ ε =
      (fun w : ℝ × ℝ => cubicAxisKernel (cubicSchwartzSwap Φ) ε (w.2,w.1)) :=
    funext (cubicOtherAxisKernel_swap Φ ε)
  rw [he]
  exact (integrable_schwartz_cubicKernels (cubicSchwartzSwap Φ) hε hε1).1.swap

theorem integral_schwartz_cubicOtherAxisKernel_swap (Φ : 𝓢(ℝ × ℝ, ℂ)) (ε : ℝ) :
    (∫ w : ℝ × ℝ,cubicOtherAxisKernel Φ ε w)=
      ∫ w : ℝ × ℝ,cubicAxisKernel (cubicSchwartzSwap Φ) ε w := by
  simp_rw [cubicOtherAxisKernel_swap]
  exact integral_prod_swap _

/-- Full-plane form of the complete Schwartz boundary action. The factors one half and
one quarter undo the exact two- and four-reflection averages. -/
def cubicSchwartzBoundaryValue (Φ : 𝓢(ℝ × ℝ, ℂ)) : ℂ :=
  (2 : ℂ)⁻¹*(∫ w : ℝ × ℝ,cubicAxisQuotient Φ 1 w)+
  (2 : ℂ)⁻¹*(∫ w : ℝ × ℝ,cubicAxisQuotient (cubicSchwartzSwap Φ) 1 w)-
  (Real.pi^2 : ℝ) • Φ (0,0)-
  2*((4 : ℂ)⁻¹*(∫ w : ℝ × ℝ,cubicMixedQuotient Φ 1 w))+
  ∫ w : ℝ × ℝ,Φ w

private theorem eventually_near_damping :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 :=
  eventually_mem_nhdsWithin.and
    ((eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)

theorem tendsto_integral_schwartz_cubicAxisKernel (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,cubicAxisKernel Φ ε w) (𝓝[>] 0)
      (𝓝 ((2 : ℂ)⁻¹*(∫ w : ℝ × ℝ,cubicAxisQuotient Φ 1 w))) := by
  apply ((tendsto_integral_schwartz_literal_cubicAxis Φ).const_mul ((2 : ℂ)⁻¹)).congr'
  filter_upwards [eventually_near_damping] with ε hε
  exact (integral_schwartz_cubicAxisKernel_eq_reflected Φ hε.1 hε.2).symm

theorem tendsto_integral_schwartz_cubicMixedKernel (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,cubicMixedKernel Φ ε w) (𝓝[>] 0)
      (𝓝 ((4 : ℂ)⁻¹*(∫ w : ℝ × ℝ,cubicMixedQuotient Φ 1 w))) := by
  apply ((tendsto_integral_schwartz_literal_cubicMixed Φ).const_mul ((4 : ℂ)⁻¹)).congr'
  filter_upwards [eventually_near_damping] with ε hε
  exact (integral_schwartz_cubicMixedKernel_eq_reflected Φ hε.1 hε.2).symm

theorem tendsto_integral_schwartz_cubicOtherAxisKernel (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,cubicOtherAxisKernel Φ ε w) (𝓝[>] 0)
      (𝓝 ((2 : ℂ)⁻¹*(∫ w : ℝ × ℝ,cubicAxisQuotient (cubicSchwartzSwap Φ) 1 w))) := by
  simpa only [integral_schwartz_cubicOtherAxisKernel_swap] using
    tendsto_integral_schwartz_cubicAxisKernel (cubicSchwartzSwap Φ)

theorem integrable_schwartz_cubicConnectedKernel (Φ : 𝓢(ℝ × ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : Integrable (cubicConnectedKernel Φ ε) := by
  obtain ⟨ha,hm⟩ := integrable_schwartz_cubicKernels Φ hε hε1
  exact (((ha.add (integrable_schwartz_cubicOtherAxisKernel Φ hε hε1)).sub
    (integrable_schwartz_cubicIntersectionKernel Φ hε hε1)).sub
    (hm.const_mul 2)).add Φ.integrable

/-- Complete noncompact critical boundary of the actual connected arithmetic cubic:
both finite parts, product PV, signed intersection mass, and ordinary test integral. -/
theorem tendsto_integral_schwartz_cubicConnectedKernel (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ,cubicConnectedKernel Φ ε w)
      (𝓝[>] 0) (𝓝 (cubicSchwartzBoundaryValue Φ)) := by
  have hl := ((((tendsto_integral_schwartz_cubicAxisKernel Φ).add
    (tendsto_integral_schwartz_cubicOtherAxisKernel Φ)).sub
    (tendsto_schwartz_cubic_intersection Φ)).sub
    ((tendsto_integral_schwartz_cubicMixedKernel Φ).const_mul 2)).add
    (tendsto_const_nhds (x := ∫ w : ℝ × ℝ,Φ w))
  apply hl.congr'
  filter_upwards [eventually_near_damping] with ε hε
  obtain ⟨ha,hm⟩ := integrable_schwartz_cubicKernels Φ hε.1 hε.2
  have hb := integrable_schwartz_cubicOtherAxisKernel Φ hε.1 hε.2
  have hi := integrable_schwartz_cubicIntersectionKernel Φ hε.1 hε.2
  change _ = ∫ w : ℝ × ℝ, cubicAxisKernel Φ ε w+cubicOtherAxisKernel Φ ε w-
    cubicIntersectionKernel ε w • (realCubicSource (1+ε) w.1 w.2*Φ w)-
    2*cubicMixedKernel Φ ε w+Φ w
  have hab : Integrable (fun w : ℝ × ℝ => cubicAxisKernel Φ ε w+cubicOtherAxisKernel Φ ε w) := ha.add hb
  have habi : Integrable (fun w : ℝ × ℝ => cubicAxisKernel Φ ε w+cubicOtherAxisKernel Φ ε w-
      cubicIntersectionKernel ε w • (realCubicSource (1+ε) w.1 w.2*Φ w)) := hab.sub hi
  have habim : Integrable (fun w : ℝ × ℝ => cubicAxisKernel Φ ε w+cubicOtherAxisKernel Φ ε w-
      cubicIntersectionKernel ε w • (realCubicSource (1+ε) w.1 w.2*Φ w)-2*cubicMixedKernel Φ ε w) :=
    habi.sub (hm.const_mul 2)
  rw [integral_add habim Φ.integrable,
    integral_sub habi (hm.const_mul 2),integral_sub hab hi,
    integral_add ha hb,integral_const_mul]

/-- The complete unordered rational cubic series has the full Schwartz critical boundary.
All source growth, cancellations, integrability, and termwise integration are proved. -/
theorem tendsto_schwartz_rationalCubicTest_criticalBoundary (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    Tendsto (fun ε : ℝ => ∑' a,rationalCubicTest Φ (1+ε) a)
      (𝓝[>] 0) (𝓝 (cubicSchwartzBoundaryValue Φ)) := by
  apply (tendsto_integral_schwartz_cubicConnectedKernel Φ).congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  exact (rationalCubicTest_hasSum Φ.integrable hε).tsum_eq.symm

end RHTower.BAGTrace
