import GaloisForLFunctions.HTGeometry.HardyLineMass
import GaloisForLFunctions.HTGeometry.ExpTestTransform
import GaloisForLFunctions.HTGeometry.VerticalStripContourShiftSeq
import GaloisForLFunctions.HTGeometry.WeightedHolder

/-!
# The line integral of a Hardy function against a test multiplier is line-independent

Multiplying a Hardy function by the exponential transform of a compactly supported smooth test
function produces an integrand which is absolutely integrable on every vertical line of the
half-plane and whose horizontal mass vanishes along a sequence of heights.  Cauchy's theorem then
says the line integral does not depend on the line.

## Main results

* `integral_hardyMulTest_line_indep`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology

open scoped ContDiff

noncomputable section

theorem aestronglyMeasurable_hardySegment {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {c d : ℝ} (hc : 0 < c) (T : ℝ) :
    AEStronglyMeasurable (fun σ : ℝ => F ((σ : ℂ) + (T : ℝ) * Complex.I))
      (volume.restrict (Icc c d)) := by
  have hcont : Continuous fun σ : ℝ => stripClamp F c d ((σ : ℂ) + (T : ℝ) * Complex.I) := by
    have h1 : Continuous fun σ : ℝ => ((σ : ℂ) + (T : ℝ) * Complex.I) := by fun_prop
    exact (continuous_stripClamp hF hc).comp h1
  refine hcont.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
  exact stripClamp_eq hσ T

/-- The `L¹` mass of a Hardy function on a horizontal segment is controlled by its `L²` mass. -/
theorem integral_norm_hardySegment_le {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (T : ℝ) :
    (∫ σ in Icc c d, ‖F ((σ : ℂ) + (T : ℝ) * Complex.I)‖)
      ≤ Real.sqrt (stripMass F c d T) * Real.sqrt (d - c) := by
  have hm1 := aestronglyMeasurable_hardySegment hF (d := d) hc T
  have hm2 : AEStronglyMeasurable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Icc c d)) :=
    aestronglyMeasurable_const
  have h1 : Integrable (fun σ : ℝ => ‖F ((σ : ℂ) + (T : ℝ) * Complex.I)‖ ^ 2)
      (volume.restrict (Icc c d)) := integrableOn_stripMassIntegrand (d := d) hF hc T
  have h2 : Integrable (fun _ : ℝ => ‖(1 : ℂ)‖ ^ 2) (volume.restrict (Icc c d)) := by
    simp only [norm_one, one_pow]
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hcs := integral_mul_le_sqrt_mul_sqrt_measure (μ := volume.restrict (Icc c d)) hm1 hm2 h1 h2
  simp only [norm_one, mul_one, one_pow] at hcs
  have hconst : (∫ _σ in Icc c d, (1 : ℝ)) = d - c := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le hcd]
  rw [hconst] at hcs
  exact hcs

/-- The integrand of the line integral, for a fixed test multiplier. -/
theorem integrable_hardyMulTest_line {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun y : ℝ => F ((σ : ℂ) + (y : ℝ) * Complex.I)
      * expTestTransform ψ ((σ : ℂ) + (y : ℝ) * Complex.I)) volume :=
  (memLp_two_hardyLine hF hσ).integrable_mul (memLp_two_expTestTransform_line hψ hs σ)

theorem verticalStrip_subset_halfPlane {c d : ℝ} (hc : 0 < c) :
    verticalStrip c d ⊆ {w : ℂ | 0 < w.re} := by
  intro w hw
  exact lt_of_lt_of_le hc hw.1

/-- The line integral is the same on two lines, when the left one is not to the right. -/
theorem integral_hardyMulTest_line_indep_of_le {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) :
    (∫ y : ℝ, F ((β : ℂ) + (y : ℝ) * Complex.I)
        * expTestTransform ψ ((β : ℂ) + (y : ℝ) * Complex.I))
      = ∫ y : ℝ, F ((α : ℂ) + (y : ℝ) * Complex.I)
          * expTestTransform ψ ((α : ℂ) + (y : ℝ) * Complex.I) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  set G : ℂ → ℂ := fun w => F w * expTestTransform ψ w with hG
  have hdiff : DifferentiableOn ℂ G (verticalStrip α β) := by
    refine DifferentiableOn.mul (hF.holo.mono (verticalStrip_subset_halfPlane hα)) ?_
    exact (differentiable_expTestTransform hψ.continuous hs).differentiableOn
  have hcint : Integrable fun y : ℝ => G ((α : ℂ) + (y : ℝ) * Complex.I) :=
    integrable_hardyMulTest_line hF hψ hs hα
  have hdint : Integrable fun y : ℝ => G ((β : ℂ) + (y : ℝ) * Complex.I) :=
    integrable_hardyMulTest_line hF hψ hs hβ
  obtain ⟨C, hC0, hC⟩ := exists_expTestTransform_decay hψ hs α β
  obtain ⟨T, hT, hzero, hzero'⟩ := exists_seq_stripMass_tendsto_zero (d := β) hF hα
  -- the horizontal edges
  have hedge : ∀ S : ℝ, ‖∫ u in α..β, G ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖
      ≤ C * (Real.sqrt (stripMass F α β S) * Real.sqrt (β - α)) := by
    intro S
    have hle : ‖∫ u in α..β, G ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖
        ≤ ∫ u in Icc α β, ‖G ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖ := by
      rw [intervalIntegral.integral_of_le hαβ, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      exact norm_integral_le_integral_norm _
    have hptwise : ∀ u ∈ Icc α β, ‖G ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖
        ≤ C * ‖F ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖ := by
      intro u hu
      have hre : ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I).re = u := by simp
      have hmem : ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I).re ∈ uIcc α β := by
        rw [hre, Set.uIcc_of_le hαβ]
        exact hu
      have hb := hC _ hmem
      have hden : (0 : ℝ) < 1 + ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I).im ^ 2 := by positivity
      have hbC : ‖expTestTransform ψ ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖ ≤ C := by
        refine le_trans hb ?_
        rw [div_le_iff₀ hden]
        nlinarith [sq_nonneg ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I).im]
      rw [hG, norm_mul]
      calc ‖F ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖
              * ‖expTestTransform ψ ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖
          ≤ ‖F ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖ * C :=
            mul_le_mul_of_nonneg_left hbC (norm_nonneg _)
        _ = C * ‖F ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖ := by ring
    have hint1 : IntegrableOn (fun u : ℝ => ‖G ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖)
        (Icc α β) := by
      have hcont : Continuous fun u : ℝ =>
          stripClamp F α β ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)
            * expTestTransform ψ ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I) := by
        have h1 : Continuous fun u : ℝ => ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I) := by fun_prop
        exact ((continuous_stripClamp hF hα).comp h1).mul
          (((differentiable_expTestTransform hψ.continuous hs).continuous).comp h1)
      refine ((hcont.norm).integrableOn_Icc).congr_fun (fun u hu => ?_) measurableSet_Icc
      show ‖stripClamp F α β ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)
          * expTestTransform ψ ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖
        = ‖G ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖
      rw [hG, stripClamp_eq hu S]
    have hint2 : IntegrableOn (fun u : ℝ => C * ‖F ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖)
        (Icc α β) := by
      have hbase : IntegrableOn (fun u : ℝ => ‖F ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖)
          (Icc α β) := by
        have hcont : Continuous fun u : ℝ =>
            stripClamp F α β ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I) := by
          have h1 : Continuous fun u : ℝ => ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I) := by fun_prop
          exact (continuous_stripClamp hF hα).comp h1
        refine ((hcont.norm).integrableOn_Icc).congr_fun (fun u hu => ?_) measurableSet_Icc
        show ‖stripClamp F α β ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖
          = ‖F ((u : ℂ) + ((S : ℝ) : ℂ) * Complex.I)‖
        rw [stripClamp_eq hu S]
      exact hbase.const_mul C
    refine le_trans hle ?_
    refine le_trans (setIntegral_mono_on hint1 hint2 measurableSet_Icc hptwise) ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_norm_hardySegment_le hF hα hαβ S) hC0
  have hbotlim : Tendsto
      (fun n : ℕ => ∫ u in α..β, G ((u : ℂ) + ((-(T n) : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => hedge (-(T n))) ?_
    have h1 : Tendsto (fun n : ℕ => Real.sqrt (stripMass F α β (-(T n)))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hzero'
      simpa [Function.comp_def] using this
    simpa [mul_assoc] using (h1.const_mul C).mul_const (Real.sqrt (β - α))
  have htoplim : Tendsto
      (fun n : ℕ => ∫ u in α..β, G ((u : ℂ) + ((T n : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => hedge (T n)) ?_
    have h1 : Tendsto (fun n : ℕ => Real.sqrt (stripMass F α β (T n))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hzero
      simpa [Function.comp_def] using this
    simpa [mul_assoc] using (h1.const_mul C).mul_const (Real.sqrt (β - α))
  exact integral_vertical_line_eq_of_horizontal_tendsto_seq hαβ hdiff hcint hdint hT
    hbotlim htoplim

/-- **The line integral of a Hardy function against a test multiplier does not depend on the
line.** -/
theorem integral_hardyMulTest_line_indep {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    (∫ y : ℝ, F ((α : ℂ) + (y : ℝ) * Complex.I)
        * expTestTransform ψ ((α : ℂ) + (y : ℝ) * Complex.I))
      = ∫ y : ℝ, F ((β : ℂ) + (y : ℝ) * Complex.I)
          * expTestTransform ψ ((β : ℂ) + (y : ℝ) * Complex.I) := by
  rcases le_total α β with h | h
  · exact (integral_hardyMulTest_line_indep_of_le hF hψ hs hα h).symm
  · exact integral_hardyMulTest_line_indep_of_le hF hψ hs hβ h

end

end GaloisForLFunctions.HTGeometry
