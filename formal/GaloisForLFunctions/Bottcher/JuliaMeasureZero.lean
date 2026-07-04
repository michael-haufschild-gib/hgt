/-
# Lebesgue-null disconnected filled Julia sets

This file builds the local infrastructure for the disconnected quadratic
filled-Julia nullity theorem.  The first reusable layer is the standard
backward-trapping escape disk and the named nested-preimage characterization.
-/
import GaloisForLFunctions.Bottcher.Dynamics
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Topology

namespace Bottcher

noncomputable section

/-- The standard escape radius for `f_c(z)=z^2+c`. -/
def quadraticEscapeRadius (c : ℂ) : ℝ := max 2 ‖c‖

/-- The standard closed escape disk is backward-trapping for the quadratic map. -/
theorem quadratic_preimage_closedBall_subset (c : ℂ) :
    (quadratic c) ⁻¹' Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) ⊆
      Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) := by
  intro z hz
  change quadratic c z ∈ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) at hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
  have htri : ‖z‖ ^ 2 ≤ ‖quadratic c z‖ + ‖c‖ := by
    have hsub : ‖(z ^ 2 + c) - c‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := norm_sub_le (z ^ 2 + c) c
    have hnorm : ‖(z ^ 2 + c) - c‖ = ‖z‖ ^ 2 := by
      rw [show (z ^ 2 + c) - c = z ^ 2 by ring, norm_pow]
    rw [quadratic_apply]
    rwa [hnorm] at hsub
  have hR2 : quadraticEscapeRadius c + ‖c‖ ≤ (quadraticEscapeRadius c) ^ 2 := by
    unfold quadraticEscapeRadius
    by_cases h : ‖c‖ ≤ 2
    · have hmax : max (2 : ℝ) ‖c‖ = 2 := max_eq_left h
      rw [hmax]
      nlinarith [norm_nonneg c, h]
    · have hc2 : 2 ≤ ‖c‖ := le_of_not_ge h
      have hmax : max (2 : ℝ) ‖c‖ = ‖c‖ := max_eq_right hc2
      rw [hmax]
      nlinarith [norm_nonneg c, hc2]
  have hzsq : ‖z‖ ^ 2 ≤ (quadraticEscapeRadius c) ^ 2 := by
    have htri2 : ‖quadratic c z‖ + ‖c‖ ≤ quadraticEscapeRadius c + ‖c‖ := by
      nlinarith [hz]
    exact le_trans htri (le_trans htri2 hR2)
  have hRnonneg : 0 ≤ quadraticEscapeRadius c := by
    unfold quadraticEscapeRadius
    exact le_trans (by norm_num) (le_max_left (2 : ℝ) ‖c‖)
  nlinarith [hzsq, norm_nonneg z, hRnonneg]

/-- `K_c` as the nested intersection of inverse images of the standard closed escape disk. -/
theorem filledJulia_eq_iInter_preimage_closedBall (c : ℂ) :
    filledJulia c =
      ⋂ n : ℕ, (fun z => (quadratic c)^[n] z) ⁻¹'
        Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) := by
  simpa [quadraticEscapeRadius] using filledJulia_eq_iInter c

/-- The `n`th pullback of the standard closed escape disk. -/
def quadraticPreimageClosedBall (c : ℂ) (n : ℕ) : Set ℂ :=
  (fun z => (quadratic c)^[n] z) ⁻¹' Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c)

theorem quadraticPreimageClosedBall_zero (c : ℂ) :
    quadraticPreimageClosedBall c 0 = Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) := by
  ext z
  simp [quadraticPreimageClosedBall]

/-- The pullbacks of the trapping disk form a decreasing sequence. -/
theorem quadraticPreimageClosedBall_succ_subset (c : ℂ) (n : ℕ) :
    quadraticPreimageClosedBall c (n + 1) ⊆ quadraticPreimageClosedBall c n := by
  intro z hz
  change (quadratic c)^[n] z ∈ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c)
  change (quadratic c)^[n + 1] z ∈ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) at hz
  rw [Function.iterate_succ' (quadratic c) n, Function.comp_apply] at hz
  exact quadratic_preimage_closedBall_subset c hz

/-- Antitone form of `quadraticPreimageClosedBall_succ_subset`. -/
theorem antitone_quadraticPreimageClosedBall (c : ℂ) :
    Antitone (quadraticPreimageClosedBall c) :=
  antitone_nat_of_succ_le (fun n =>
    show quadraticPreimageClosedBall c (n + 1) ≤ quadraticPreimageClosedBall c n from
      quadraticPreimageClosedBall_succ_subset c n)

theorem measurableSet_quadraticPreimageClosedBall (c : ℂ) (n : ℕ) :
    MeasurableSet (quadraticPreimageClosedBall c n) := by
  dsimp [quadraticPreimageClosedBall]
  exact isClosed_closedBall.measurableSet.preimage ((continuous_quadratic c).iterate n).measurable

/-- Every pullback of the trapping disk is still contained in the original trapping disk. -/
theorem quadraticPreimageClosedBall_subset_closedBall (c : ℂ) (n : ℕ) :
    quadraticPreimageClosedBall c n ⊆ Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c) := by
  simpa [quadraticPreimageClosedBall_zero] using
    (antitone_quadraticPreimageClosedBall c (Nat.zero_le n))

theorem volume_quadraticPreimageClosedBall_lt_top (c : ℂ) (n : ℕ) :
    volume (quadraticPreimageClosedBall c n) < ⊤ := by
  exact lt_of_le_of_lt (measure_mono (quadraticPreimageClosedBall_subset_closedBall c n))
    ((isCompact_closedBall (0 : ℂ) (quadraticEscapeRadius c)).measure_lt_top)

theorem filledJulia_subset_quadraticPreimageClosedBall (c : ℂ) (n : ℕ) :
    filledJulia c ⊆ quadraticPreimageClosedBall c n := by
  rw [filledJulia_eq_iInter_preimage_closedBall]
  exact Set.iInter_subset (fun n : ℕ => (fun z => (quadratic c)^[n] z) ⁻¹'
    Metric.closedBall (0 : ℂ) (quadraticEscapeRadius c)) n

theorem volume_filledJulia_le_quadraticPreimageClosedBall (c : ℂ) (n : ℕ) :
    volume (filledJulia c) ≤ volume (quadraticPreimageClosedBall c n) :=
  measure_mono (filledJulia_subset_quadraticPreimageClosedBall c n)

/-- Continuity from above for the decreasing pullbacks of the trapping disk. -/
theorem volume_filledJulia_eq_iInf_quadraticPreimageClosedBall (c : ℂ) :
    volume (filledJulia c) = ⨅ n : ℕ, volume (quadraticPreimageClosedBall c n) := by
  rw [filledJulia_eq_iInter_preimage_closedBall]
  change volume (⋂ n : ℕ, quadraticPreimageClosedBall c n) =
    ⨅ n : ℕ, volume (quadraticPreimageClosedBall c n)
  exact (antitone_quadraticPreimageClosedBall c).measure_iInter
    (fun n => (measurableSet_quadraticPreimageClosedBall c n).nullMeasurableSet)
    ⟨0, ne_of_lt (volume_quadraticPreimageClosedBall_lt_top c 0)⟩

/-- It suffices to prove that the trapping-disk pullback volumes tend to zero. -/
theorem volume_filledJulia_eq_zero_of_tendsto_preimage_closedBall_zero {c : ℂ}
    (hlim : Tendsto (fun n : ℕ => volume (quadraticPreimageClosedBall c n)) atTop (𝓝 0)) :
    volume (filledJulia c) = 0 := by
  have hle : (fun _ : ℕ => volume (filledJulia c)) ≤ᶠ[atTop]
      fun n : ℕ => volume (quadraticPreimageClosedBall c n) :=
    Filter.Eventually.of_forall (volume_filledJulia_le_quadraticPreimageClosedBall c)
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle) bot_le

/-- Complex-plane area formula for an injective real-`C¹` map on a measurable set, in
`lintegral` form. -/
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul_complex
    {s : Set ℂ} {f : ℂ → ℂ} {f' : ℂ → ℂ →L[ℝ] ℂ}
    (hs : MeasurableSet s) (hf' : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hf : Set.InjOn f s) (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in f '' s, g z ∂(volume : Measure ℂ) =
      ∫⁻ z in s, ENNReal.ofReal |(f' z).det| * g (f z) ∂(volume : Measure ℂ) :=
  MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hs hf' hf g

/-- Complex-plane area formula for the measure of the image of an injective real-`C¹` map. -/
theorem volume_image_eq_lintegral_abs_det_fderiv_complex
    {s : Set ℂ} {f : ℂ → ℂ} {f' : ℂ → ℂ →L[ℝ] ℂ}
    (hs : MeasurableSet s) (hf' : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hf : Set.InjOn f s) :
    volume (f '' s) = ∫⁻ z in s, ENNReal.ofReal |(f' z).det| ∂(volume : Measure ℂ) := by
  exact (MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image (μ := volume) hs hf' hf).symm

/-- The critical value `c` has the unique preimage `0` under `z ↦ z^2+c`. -/
theorem quadratic_preimage_singleton_criticalValue (c : ℂ) :
    (quadratic c) ⁻¹' ({c} : Set ℂ) = ({0} : Set ℂ) := by
  ext z
  simp [quadratic_apply, pow_two, mul_eq_zero]

/-- The branch-overlap locus over the critical value is Lebesgue-null. -/
theorem volume_quadratic_preimage_singleton_criticalValue (c : ℂ) :
    volume ((quadratic c) ⁻¹' ({c} : Set ℂ)) = 0 := by
  rw [quadratic_preimage_singleton_criticalValue]
  exact measure_singleton 0

end

end Bottcher
