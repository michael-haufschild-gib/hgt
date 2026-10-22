import GaloisForLFunctions.RHTower.ChiRamanujanCubicBoundaryCancellation

/-!
# Compensated critical limits of the actual BAG cubic source

The actual reflected mixed and axis numerators have uniform compact-source bounds.
Their totalized quotients admit joint dominated-convergence limits with the original
moving zeta/Euler source. Exact algebra recovers the literal reflected kernels.
Reflection back to the full symmetric test box is a separate identity.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace RHTower.BAGTrace

theorem continuous_cubicTestedSlice {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    Continuous (fun w : ℝ × ℝ => cubicTestedSource Φ ![σ,w.1,w.2]) := by
  have he : Continuous (fun w : ℝ × ℝ => ![σ,w.1,w.2]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  apply continuous_iff_continuousAt.2
  intro w
  exact ContinuousAt.comp (f := fun w : ℝ × ℝ => ![σ,w.1,w.2])
    (contDiffAt_cubicTestedSource hΦ (w := ![σ,w.1,w.2]) hσ).continuousAt he.continuousAt

theorem continuous_cubicMixedDifference {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) : Continuous (cubicMixedDifference Φ σ) := by
  have hs := continuous_cubicTestedSlice hΦ hσ
  have h1 : Continuous (fun w : ℝ × ℝ => (-w.1,w.2)) := by fun_prop
  have h2 : Continuous (fun w : ℝ × ℝ => (w.1,-w.2)) := by fun_prop
  have h12 : Continuous (fun w : ℝ × ℝ => (-w.1,-w.2)) := by fun_prop
  convert ((hs.sub (hs.comp h1)).sub (hs.comp h2)).add (hs.comp h12) using 1
  rfl

theorem continuousAt_cubicTestedParameter {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) (u v : ℝ) :
    ContinuousAt (fun τ : ℝ => cubicTestedSource Φ ![τ,u,v]) σ := by
  have he : Continuous (fun τ : ℝ => ![τ,u,v]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact ContinuousAt.comp (f := fun τ : ℝ => ![τ,u,v])
    (contDiffAt_cubicTestedSource hΦ (w := ![σ,u,v]) hσ).continuousAt he.continuousAt

theorem continuousAt_cubicMixedParameter {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) (w : ℝ × ℝ) :
    ContinuousAt (fun τ : ℝ => cubicMixedDifference Φ τ w) σ :=
  (((continuousAt_cubicTestedParameter hΦ hσ w.1 w.2).sub
    (continuousAt_cubicTestedParameter hΦ hσ (-w.1) w.2)).sub
    (continuousAt_cubicTestedParameter hΦ hσ w.1 (-w.2))).add
    (continuousAt_cubicTestedParameter hΦ hσ (-w.1) (-w.2))

/-- Totalized reflected product-PV quotient. Values on the axes are zero. -/
def cubicMixedQuotient (Φ : ℝ × ℝ → ℂ) (σ : ℝ) (w : ℝ × ℝ) : ℂ :=
  cubicMixedDifference Φ σ w / ((w.1*w.2 : ℝ) : ℂ)

theorem measurable_cubicMixedQuotient {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) : Measurable (cubicMixedQuotient Φ σ) := by
  have hc : Continuous (fun w : ℝ × ℝ => ((w.1*w.2 : ℝ) : ℂ)) := by fun_prop
  convert (continuous_cubicMixedDifference hΦ hσ).measurable.div hc.measurable using 1
  rfl

theorem exists_bound_cubicMixedQuotient {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc (1 : ℝ) 2, ∀ w ∈ Icc (0,0) (R,R),
      ‖cubicMixedQuotient Φ σ w‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := exists_bound_cubicMixedDifference hΦ R
  refine ⟨C,hC, fun σ hσ w hw => ?_⟩
  by_cases hz : w.1*w.2=0
  · simp only [cubicMixedQuotient, hz, Complex.ofReal_zero, div_zero, norm_zero]
    exact hC
  · have hp : 0 < w.1*w.2 := lt_of_le_of_ne (mul_nonneg hw.1.1 hw.1.2) (Ne.symm hz)
    have h := hb σ hσ w.1 ⟨hw.1.1,hw.2.1⟩ w.2 ⟨hw.1.2,hw.2.2⟩
    rw [cubicMixedQuotient, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    apply (div_le_iff₀ hp).2
    simpa only [mul_assoc] using h

/-- Attenuation factor that remains after exact axis cancellation. -/
def cubicDampingFactor (ε u : ℝ) : ℝ := u^2/(ε^2+u^2)

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

theorem tendsto_cubicDampingFactor {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun ε : ℝ => cubicDampingFactor ε u) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun ε : ℝ => u^2/(ε^2+u^2)) 0 :=
    continuousAt_const.div ((continuousAt_id.pow 2).add continuousAt_const)
      (by simpa using pow_ne_zero 2 hu)
  simpa [cubicDampingFactor, hu] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

theorem tendsto_damped_cubicMixedQuotient {Φ : ℝ × ℝ → ℂ}
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

/-- The actual compensated mixed term has a joint critical limit on every compact quadrant.
The estimate comes from its actual complete source, not a bound assumed as a premise. -/
theorem tendsto_integral_cubicMixedQuotient {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ in Icc (0,0) (R,R),
      (cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) • cubicMixedQuotient Φ (1+ε) w)
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ in Icc (0,0) (R,R), cubicMixedQuotient Φ 1 w)) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_cubicMixedQuotient hΦ R
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 :=
    eventually_mem_nhdsWithin.and
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
  have hm : ∀ᶠ ε : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun w : ℝ × ℝ => (cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) •
        cubicMixedQuotient Φ (1+ε) w) (volume.restrict (Icc (0,0) (R,R))) := by
    filter_upwards [he] with ε hε
    have hd := continuous_cubicDampingFactor hε.1
    have hdm : Measurable (fun w : ℝ × ℝ => cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) :=
      ((hd.comp continuous_fst).mul (hd.comp continuous_snd)).measurable
    exact (hdm.smul (measurable_cubicMixedQuotient hΦ (by linarith [hε.1]))).aestronglyMeasurable
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ w : ℝ × ℝ ∂volume.restrict (Icc (0,0) (R,R)),
      ‖(cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) •
        cubicMixedQuotient Φ (1+ε) w‖ ≤ C := by
    filter_upwards [he] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    have hd0 := mul_nonneg (cubicDampingFactor_nonneg ε w.1) (cubicDampingFactor_nonneg ε w.2)
    have hd1 : cubicDampingFactor ε w.1*cubicDampingFactor ε w.2 ≤ 1 := by
      nlinarith [cubicDampingFactor_le_one ε w.1,cubicDampingFactor_le_one ε w.2,
        mul_nonneg (sub_nonneg.mpr (cubicDampingFactor_le_one ε w.1))
          (cubicDampingFactor_nonneg ε w.2)]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd0]
    calc _ ≤ 1*‖cubicMixedQuotient Φ (1+ε) w‖ :=
          mul_le_mul_of_nonneg_right hd1 (norm_nonneg _)
      _ ≤ C := by simpa only [one_mul] using hb (1+ε) ⟨by linarith [hε.1],by linarith [hε.2]⟩ w hw
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => C) hm hbound
    (integrableOn_const (isCompact_Icc.measure_lt_top.ne))
    (ae_of_all _ fun w => tendsto_damped_cubicMixedQuotient hΦ w)


/-- Totalized reflected first finite-part quotient. -/
def cubicAxisQuotient (Φ : ℝ × ℝ → ℂ) (σ : ℝ) (w : ℝ × ℝ) : ℂ :=
  cubicAxisDifference Φ σ w / ((w.1^2 : ℝ) : ℂ)

theorem continuous_cubicTestedAxisSlice {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    Continuous (fun w : ℝ × ℝ => cubicTestedAxisNumerator Φ ![σ,w.1,w.2]) := by
  have he : Continuous (fun w : ℝ × ℝ => ![σ,w.1,w.2]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  apply continuous_iff_continuousAt.2
  intro w
  exact ContinuousAt.comp (f := fun w : ℝ × ℝ => ![σ,w.1,w.2])
    (contDiffAt_cubicTestedAxisNumerator hΦ (w := ![σ,w.1,w.2]) hσ).continuousAt he.continuousAt

theorem continuous_cubicAxisDifference {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) : Continuous (cubicAxisDifference Φ σ) := by
  have hs := continuous_cubicTestedAxisSlice hΦ hσ
  have h1 : Continuous (fun w : ℝ × ℝ => (-w.1,w.2)) := by fun_prop
  convert hs.add (hs.comp h1) using 1
  rfl

theorem continuousAt_cubicAxisTestParameter {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) (u v : ℝ) :
    ContinuousAt (fun τ : ℝ => cubicTestedAxisNumerator Φ ![τ,u,v]) σ := by
  have he : Continuous (fun τ : ℝ => ![τ,u,v]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact ContinuousAt.comp (f := fun τ : ℝ => ![τ,u,v])
    (contDiffAt_cubicTestedAxisNumerator hΦ (w := ![σ,u,v]) hσ).continuousAt he.continuousAt

theorem continuousAt_cubicAxisParameter {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) (w : ℝ × ℝ) :
    ContinuousAt (fun τ : ℝ => cubicAxisDifference Φ τ w) σ :=
  (continuousAt_cubicAxisTestParameter hΦ hσ w.1 w.2).add
    (continuousAt_cubicAxisTestParameter hΦ hσ (-w.1) w.2)

theorem measurable_cubicAxisQuotient {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {σ : ℝ} (hσ : 1 ≤ σ) : Measurable (cubicAxisQuotient Φ σ) := by
  have hc : Continuous (fun w : ℝ × ℝ => ((w.1^2 : ℝ) : ℂ)) := by fun_prop
  convert (continuous_cubicAxisDifference hΦ hσ).measurable.div hc.measurable using 1
  rfl

theorem exists_bound_cubicAxisQuotient {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc (1 : ℝ) 2, ∀ w ∈ Icc (0,-R) (R,R),
      ‖cubicAxisQuotient Φ σ w‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := exists_bound_cubicAxisDifference hΦ R
  refine ⟨C,hC, fun σ hσ w hw => ?_⟩
  by_cases hz : w.1=0
  · simp only [cubicAxisQuotient,hz,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Complex.ofReal_zero,div_zero,norm_zero]
    exact hC
  · have hp : 0 < w.1^2 := sq_pos_of_ne_zero hz
    have h := hb σ hσ w.1 ⟨hw.1.1,hw.2.1⟩ w.2 ⟨hw.1.2,hw.2.2⟩
    rw [cubicAxisQuotient,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
    exact (div_le_iff₀ hp).2 h

theorem tendsto_damped_cubicAxisQuotient {Φ : ℝ × ℝ → ℂ}
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

/-- Joint critical limit of the actual reflected first finite part on every compact box. -/
theorem tendsto_integral_cubicAxisQuotient {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ in Icc (0,-R) (R,R),
      cubicDampingFactor ε w.1 • cubicAxisQuotient Φ (1+ε) w)
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ in Icc (0,-R) (R,R), cubicAxisQuotient Φ 1 w)) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_cubicAxisQuotient hΦ R
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 :=
    eventually_mem_nhdsWithin.and
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)
  have hm : ∀ᶠ ε : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun w : ℝ × ℝ => cubicDampingFactor ε w.1 • cubicAxisQuotient Φ (1+ε) w)
      (volume.restrict (Icc (0,-R) (R,R))) := by
    filter_upwards [he] with ε hε
    have hd : Continuous (fun w : ℝ × ℝ => cubicDampingFactor ε w.1) :=
      (continuous_cubicDampingFactor hε.1).comp continuous_fst
    exact (hd.measurable.smul (measurable_cubicAxisQuotient hΦ (by linarith [hε.1]))).aestronglyMeasurable
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ w : ℝ × ℝ ∂volume.restrict (Icc (0,-R) (R,R)),
      ‖cubicDampingFactor ε w.1 • cubicAxisQuotient Φ (1+ε) w‖ ≤ C := by
    filter_upwards [he] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (cubicDampingFactor_nonneg ε w.1)]
    calc _ ≤ 1*‖cubicAxisQuotient Φ (1+ε) w‖ :=
          mul_le_mul_of_nonneg_right (cubicDampingFactor_le_one ε w.1) (norm_nonneg _)
      _ ≤ C := by simpa only [one_mul] using hb (1+ε) ⟨by linarith [hε.1],by linarith [hε.2]⟩ w hw
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => C) hm hbound
    (integrableOn_const (isCompact_Icc.measure_lt_top.ne))
    (ae_of_all _ fun w => tendsto_damped_cubicAxisQuotient hΦ w)


/-- Exact identification of the compensated mixed integrand with its literal kernel. -/
theorem damped_cubicMixedQuotient_eq {ε : ℝ} (hε : 0 < ε) (Φ : ℝ × ℝ → ℂ) (w : ℝ × ℝ) :
    (cubicDampingFactor ε w.1*cubicDampingFactor ε w.2) • cubicMixedQuotient Φ (1+ε) w =
      ((w.1 : ℂ)*(w.2 : ℂ)*cubicMixedDifference Φ (1+ε) w) /
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)) := by
  by_cases hu : w.1=0
  · simp [cubicDampingFactor,cubicMixedQuotient,hu]
  by_cases hv : w.2=0
  · simp [cubicDampingFactor,cubicMixedQuotient,hv]
  have hdu : (((ε^2+w.1^2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < ε^2+w.1^2 by positivity))
  have hdv : (((ε^2+w.2^2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < ε^2+w.2^2 by positivity))
  have hu' : (w.1 : ℂ) ≠ 0 := by exact_mod_cast hu
  have hv' : (w.2 : ℂ) ≠ 0 := by exact_mod_cast hv
  change (((w.1^2/(ε^2+w.1^2)*(w.2^2/(ε^2+w.2^2)) : ℝ) : ℂ)*
    (cubicMixedDifference Φ (1+ε) w / ((w.1*w.2 : ℝ) : ℂ))) = _
  rw [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_pow,Complex.ofReal_mul]
  field_simp

/-- The reflected actual mixed kernel converges to its product-PV action. -/
theorem tendsto_integral_literal_cubicMixed {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ in Icc (0,0) (R,R),
      ((w.1 : ℂ)*(w.2 : ℂ)*cubicMixedDifference Φ (1+ε) w) /
        (((ε^2+w.1^2 : ℝ) : ℂ)*((ε^2+w.2^2 : ℝ) : ℂ)))
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ in Icc (0,0) (R,R), cubicMixedQuotient Φ 1 w)) := by
  apply (tendsto_integral_cubicMixedQuotient hΦ R).congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  exact ae_of_all _ fun w => damped_cubicMixedQuotient_eq hε Φ w

/-- Exact identification of the compensated first finite-part integrand. -/
theorem damped_cubicAxisQuotient_eq {ε : ℝ} (hε : 0 < ε) (Φ : ℝ × ℝ → ℂ) (w : ℝ × ℝ) :
    cubicDampingFactor ε w.1 • cubicAxisQuotient Φ (1+ε) w =
      cubicAxisDifference Φ (1+ε) w / ((ε^2+w.1^2 : ℝ) : ℂ) := by
  by_cases hu : w.1=0
  · have hz : cubicAxisDifference Φ (1+ε) w=0 := by
      simp only [cubicAxisDifference,cubicTestedAxisNumerator,Matrix.cons_val_zero,
        Matrix.cons_val_one,hu,neg_zero]
      rw [realCubicSource_axis_left (by linarith : 1 ≤ 1+ε),zero_mul,zero_add]
    simp [cubicDampingFactor,cubicAxisQuotient,hu,hz]
  have hu' : (w.1 : ℂ) ≠ 0 := by exact_mod_cast hu
  have hdu : (((ε^2+w.1^2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < ε^2+w.1^2 by positivity))
  change (((w.1^2/(ε^2+w.1^2) : ℝ) : ℂ)*
    (cubicAxisDifference Φ (1+ε) w / ((w.1^2 : ℝ) : ℂ))) = _
  rw [Complex.ofReal_div,Complex.ofReal_pow]
  field_simp

/-- The reflected actual first finite-part kernel has the claimed critical limit. -/
theorem tendsto_integral_literal_cubicAxis {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ in Icc (0,-R) (R,R),
      cubicAxisDifference Φ (1+ε) w / ((ε^2+w.1^2 : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (∫ w : ℝ × ℝ in Icc (0,-R) (R,R), cubicAxisQuotient Φ 1 w)) := by
  apply (tendsto_integral_cubicAxisQuotient hΦ R).congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  exact ae_of_all _ fun w => damped_cubicAxisQuotient_eq hε Φ w

end RHTower.BAGTrace
