import GaloisForLFunctions.RHTower.Suzuki.SuzukiBoundaryLayerFormCore
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHlogDilationContinuity
import GaloisForLFunctions.RHTower.SoninPacketFourierModulation

/-!
# Logarithmic form-energy growth of the CCM aperture modes

Connes--Consani's Laurent-polynomial form-core argument needs more than membership of each
aperture mode in the logarithmic form domain: it uses the published estimate
`‖U^k‖₁² = O(log |k|)`.  This file proves a stronger explicit translation inequality.

The zero-extended mode of frequency `κ` is the modulation of the zero mode by
`κ / (2π)`.  Its Fourier transform is therefore translated by that amount.  Subadditivity of
`1 + log⁺ |ξ|` then bounds the translated energy by the zero-mode energy times one additional
logarithmic weight.  No asymptotic premise and no unproved Fourier formula is used.
-/

open MeasureTheory Set Filter Topology
open scoped FourierTransform ENNReal

noncomputable section

namespace RHTower

/-- The Suzuki logarithmic weight is subadditive. -/
theorem suzukiLogWeight_add_le (x y : ℝ) :
    suzukiLogWeight (x + y) ≤ suzukiLogWeight x + suzukiLogWeight y := by
  rw [suzukiLogWeight_eq_one_add_posLog, suzukiLogWeight_eq_one_add_posLog,
    suzukiLogWeight_eq_one_add_posLog]
  have hadd := Real.posLog_add (x := x) (y := y)
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith

/-- The defining weighted density of every `H^log` vector is integrable. -/
theorem integrable_suzukiHlogFourierDensity (f : SuzukiHlogFourierL2) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ * ‖(f : ℝ → ℂ) ξ‖ ^ 2) := by
  have hfint : Integrable (fun ξ : ℝ => ‖(f : ℝ → ℂ) ξ‖ ^ 2)
      suzukiHlogMeasure :=
    (MeasureTheory.Lp.memLp f).integrable_norm_pow (by norm_num)
  unfold suzukiHlogMeasure at hfint
  rw [integrable_withDensity_iff_integrable_smul
    measurable_suzukiLogWeightNNReal] at hfint
  refine hfint.congr ?_
  filter_upwards with ξ
  rw [NNReal.smul_def, smul_eq_mul, coe_suzukiLogWeightNNReal]
  rfl

/-- The zero-extended aperture exponential is integrable for every real frequency. -/
theorem integrable_suzukiApertureModeCutoff (a κ : ℝ) :
    Integrable (suzukiApertureModeCutoff a κ) := by
  have hOn : IntegrableOn (suzukiApertureMode κ) (Icc (-a) a) volume :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      (contDiff_suzukiApertureMode κ).continuous.continuousOn
  simpa [suzukiApertureModeCutoff] using hOn.integrable_indicator measurableSet_Icc

/-- Classical Fourier representative of the frequency coordinate of an aperture mode. -/
theorem suzukiApertureModeFormVector_frequency_ae
    (a : SuzukiPositiveAperture) (κ : ℝ) :
    ((suzukiApertureModeFormVector a κ).1 : ℝ → ℂ) =ᵐ[volume]
      fun ξ => 𝓕 (suzukiApertureModeCutoff a.1 κ) ξ := by
  let q := suzukiApertureModeFormVector a κ
  have htime :
      (suzukiHlogFormEmbedding a q : ℝ → ℂ) =ᵐ[volume]
        suzukiApertureModeCutoff a.1 κ :=
    suzukiHlogFormEmbedding_apertureModeFormVector_coeFn a κ
  have hmem : MemLp (suzukiApertureModeCutoff a.1 κ) 2 volume :=
    (MeasureTheory.memLp_congr_ae htime).mp
      (MeasureTheory.Lp.memLp (suzukiHlogFormEmbedding a q))
  have htoLp : hmem.toLp (suzukiApertureModeCutoff a.1 κ) =
      suzukiHlogFormEmbedding a q := by
    apply Lp.ext
    exact hmem.coeFn_toLp.trans htime.symm
  have hclassical :
      ((fourierUnitary (suzukiHlogFormEmbedding a q) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        fun ξ => 𝓕 (suzukiApertureModeCutoff a.1 κ) ξ :=
    by
      have h := GaloisForLFunctions.RHTower.coeFn_fourier_toLp
        (integrable_suzukiApertureModeCutoff a.1 κ) hmem
      rw [htoLp] at h
      exact h
  have hunitary :
      fourierUnitary (suzukiHlogFormEmbedding a q) =
        suzukiHlogWeightedToL2 q.1 := by
    exact fourierUnitary_suzukiHlogFourierToTime q.1
  rw [hunitary] at hclassical
  exact (suzukiHlogWeightedToL2_coeFn q.1).symm.trans hclassical

/-- Pointwise modulation identity for zero-extended aperture modes. -/
theorem suzukiApertureModeCutoff_eq_modulation (a κ x : ℝ) :
    suzukiApertureModeCutoff a κ x =
      Complex.exp
          ((↑(2 * Real.pi * (κ / (2 * Real.pi)) * x) : ℂ) * Complex.I) *
        suzukiApertureModeCutoff a 0 x := by
  by_cases hx : x ∈ Icc (-a) a
  · rw [suzukiApertureModeCutoff, suzukiApertureModeCutoff,
      indicator_of_mem hx, indicator_of_mem hx]
    have hzero : suzukiApertureMode 0 x = 1 := by
      simp [suzukiApertureMode]
    rw [hzero, mul_one]
    unfold suzukiApertureMode
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  · rw [suzukiApertureModeCutoff, suzukiApertureModeCutoff,
      indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- Fourier transform of an aperture mode is the translated transform of the zero mode. -/
theorem fourier_suzukiApertureModeCutoff_eq_shift (a κ ξ : ℝ) :
    𝓕 (suzukiApertureModeCutoff a κ) ξ =
      𝓕 (suzukiApertureModeCutoff a 0) (ξ - κ / (2 * Real.pi)) := by
  rw [show suzukiApertureModeCutoff a κ = fun x : ℝ =>
      Complex.exp
          ((↑(2 * Real.pi * (κ / (2 * Real.pi)) * x) : ℂ) * Complex.I) *
        suzukiApertureModeCutoff a 0 x by
    funext x
    exact suzukiApertureModeCutoff_eq_modulation a κ x]
  exact fourier_exp_mul (suzukiApertureModeCutoff a 0)
    (κ / (2 * Real.pi)) ξ

/-- Exact integral formula for the squared weighted norm of an aperture mode. -/
theorem norm_sq_suzukiApertureModeFormVector_eq_shiftedIntegral
    (a : SuzukiPositiveAperture) (κ : ℝ) :
    ‖suzukiApertureModeFormVector a κ‖ ^ 2 =
      ∫ ξ : ℝ, suzukiLogWeight ξ *
        ‖𝓕 (suzukiApertureModeCutoff a.1 0)
          (ξ - κ / (2 * Real.pi))‖ ^ 2 := by
  change ‖(suzukiApertureModeFormVector a κ).1‖ ^ 2 = _
  rw [norm_sq_suzukiHlogFourierL2]
  apply integral_congr_ae
  filter_upwards [suzukiApertureModeFormVector_frequency_ae a κ] with ξ hξ
  rw [hξ, fourier_suzukiApertureModeCutoff_eq_shift]

/-- **Published CCM logarithmic mode-growth estimate, explicit form.**

The squared form norm at frequency `κ` grows by at most one translated logarithmic weight over
the zero mode.  In particular this is `O(log |κ|)` with all constants internal to the theorem. -/
theorem norm_sq_suzukiApertureModeFormVector_le
    (a : SuzukiPositiveAperture) (κ : ℝ) :
    ‖suzukiApertureModeFormVector a κ‖ ^ 2 ≤
      (1 + suzukiLogWeight (κ / (2 * Real.pi))) *
        ‖suzukiApertureModeFormVector a 0‖ ^ 2 := by
  let F : ℝ → ℂ := fun ξ => 𝓕 (suzukiApertureModeCutoff a.1 0) ξ
  let α : ℝ := κ / (2 * Real.pi)
  let q0 := suzukiApertureModeFormVector a 0
  have hfreq : (q0.1 : ℝ → ℂ) =ᵐ[volume] F := by
    simpa [q0, F] using suzukiApertureModeFormVector_frequency_ae a 0
  have hweighted : Integrable (fun ξ : ℝ => suzukiLogWeight ξ * ‖F ξ‖ ^ 2) :=
    (integrable_suzukiHlogFourierDensity q0.1).congr <| by
      filter_upwards [hfreq] with ξ hξ
      rw [hξ]
  have hunweighted : Integrable (fun ξ : ℝ => ‖F ξ‖ ^ 2) := by
    have hmeas : AEStronglyMeasurable (fun ξ : ℝ => ‖F ξ‖ ^ 2) :=
      (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
        (integrable_suzukiApertureModeCutoff a.1 0)).norm.pow 2 |>.aestronglyMeasurable
    refine Integrable.mono' hweighted
      hmeas ?_
    filter_upwards with ξ
    have hw := one_le_suzukiLogWeight ξ
    have hn : 0 ≤ ‖F ξ‖ ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw hn
  have hshifted : Integrable (fun ξ : ℝ =>
      suzukiLogWeight (ξ + α) * ‖F ξ‖ ^ 2) := by
    have hmajor : Integrable (fun ξ : ℝ =>
        suzukiLogWeight ξ * ‖F ξ‖ ^ 2 +
          suzukiLogWeight α * ‖F ξ‖ ^ 2) :=
      by
        have hsecond : Integrable (fun ξ : ℝ =>
            suzukiLogWeight α * ‖F ξ‖ ^ 2) :=
          hunweighted.const_mul (suzukiLogWeight α)
        exact hweighted.add hsecond
    have hmeas : AEStronglyMeasurable (fun ξ : ℝ =>
        suzukiLogWeight (ξ + α) * ‖F ξ‖ ^ 2) :=
      ((measurable_suzukiLogWeight.comp (measurable_add_const α)).mul
        ((GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
          (integrable_suzukiApertureModeCutoff a.1 0)).norm.pow 2).measurable).aestronglyMeasurable
    refine Integrable.mono' hmajor
      hmeas ?_
    filter_upwards with ξ
    have hw := suzukiLogWeight_add_le ξ α
    have hn : 0 ≤ ‖F ξ‖ ^ 2 := sq_nonneg _
    have hleft : 0 ≤ suzukiLogWeight (ξ + α) * ‖F ξ‖ ^ 2 :=
      mul_nonneg (suzukiLogWeight_nonneg _) hn
    have hright : 0 ≤ suzukiLogWeight ξ * ‖F ξ‖ ^ 2 +
        suzukiLogWeight α * ‖F ξ‖ ^ 2 :=
      add_nonneg (mul_nonneg (suzukiLogWeight_nonneg _) hn)
        (mul_nonneg (suzukiLogWeight_nonneg _) hn)
    rw [Real.norm_eq_abs, abs_of_nonneg hleft]
    exact (mul_le_mul_of_nonneg_right hw hn).trans_eq (add_mul _ _ _)
  have hchange :
      (∫ ξ : ℝ, suzukiLogWeight ξ * ‖F (ξ - α)‖ ^ 2) =
        ∫ ξ : ℝ, suzukiLogWeight (ξ + α) * ‖F ξ‖ ^ 2 := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun ξ : ℝ => suzukiLogWeight (ξ + α) * ‖F ξ‖ ^ 2) (-α)
    simpa [sub_eq_add_neg, add_assoc] using h
  have hmono :
      (∫ ξ : ℝ, suzukiLogWeight (ξ + α) * ‖F ξ‖ ^ 2) ≤
        ∫ ξ : ℝ, (suzukiLogWeight ξ + suzukiLogWeight α) * ‖F ξ‖ ^ 2 := by
    apply integral_mono hshifted
    · have hsecond : Integrable (fun ξ : ℝ =>
          suzukiLogWeight α * ‖F ξ‖ ^ 2) :=
        hunweighted.const_mul (suzukiLogWeight α)
      have hsum : Integrable (fun ξ : ℝ =>
          suzukiLogWeight ξ * ‖F ξ‖ ^ 2 +
            suzukiLogWeight α * ‖F ξ‖ ^ 2) :=
        hweighted.add hsecond
      simpa only [add_mul] using hsum
    · intro ξ
      exact mul_le_mul_of_nonneg_right (suzukiLogWeight_add_le ξ α) (sq_nonneg _)
  have hL2le :
      (∫ ξ : ℝ, ‖F ξ‖ ^ 2) ≤
        ∫ ξ : ℝ, suzukiLogWeight ξ * ‖F ξ‖ ^ 2 := by
    apply integral_mono hunweighted hweighted
    intro ξ
    calc
      ‖F ξ‖ ^ 2 = 1 * ‖F ξ‖ ^ 2 := by rw [one_mul]
      _ ≤ suzukiLogWeight ξ * ‖F ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (one_le_suzukiLogWeight ξ) (sq_nonneg _)
  have hzeroNorm :
      (∫ ξ : ℝ, suzukiLogWeight ξ * ‖F ξ‖ ^ 2) = ‖q0‖ ^ 2 := by
    rw [show ‖q0‖ = ‖q0.1‖ by rfl, norm_sq_suzukiHlogFourierL2]
    apply integral_congr_ae
    filter_upwards [hfreq] with ξ hξ
    rw [hξ]
  rw [norm_sq_suzukiApertureModeFormVector_eq_shiftedIntegral]
  change (∫ ξ : ℝ, suzukiLogWeight ξ * ‖F (ξ - α)‖ ^ 2) ≤ _
  rw [hchange]
  calc
    (∫ ξ : ℝ, suzukiLogWeight (ξ + α) * ‖F ξ‖ ^ 2)
        ≤ ∫ ξ : ℝ, (suzukiLogWeight ξ + suzukiLogWeight α) * ‖F ξ‖ ^ 2 := hmono
    _ = ∫ ξ : ℝ, (suzukiLogWeight ξ * ‖F ξ‖ ^ 2 +
        suzukiLogWeight α * ‖F ξ‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards with ξ
      ring
    _ = (∫ ξ : ℝ, suzukiLogWeight ξ * ‖F ξ‖ ^ 2) +
        ∫ ξ : ℝ, suzukiLogWeight α * ‖F ξ‖ ^ 2 := by
      rw [integral_add hweighted (hunweighted.const_mul _)]
    _ = (∫ ξ : ℝ, suzukiLogWeight ξ * ‖F ξ‖ ^ 2) +
        suzukiLogWeight α * ∫ ξ : ℝ, ‖F ξ‖ ^ 2 := by
      rw [integral_const_mul]
    _ ≤ (1 + suzukiLogWeight α) *
        (∫ ξ : ℝ, suzukiLogWeight ξ * ‖F ξ‖ ^ 2) := by
      have hwα := suzukiLogWeight_nonneg α
      nlinarith
    _ = (1 + suzukiLogWeight (κ / (2 * Real.pi))) * ‖q0‖ ^ 2 := by
      rw [hzeroNorm]

end RHTower

end
