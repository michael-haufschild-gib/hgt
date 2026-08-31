import GaloisForLFunctions.RHTower.SuzukiCanonicalSignedCompensationSaturation

/-!
# Fixed-affine signed-compensation classification

Every fixed affine mixing of the positive Suzuki transition core and its aligned completed energy
is classified.  Relative core cancellation forces coefficient one on the transition core.  The
remaining coefficient then yields exactly one of three chambers: a positive scalar copy of the
RH-equivalent aligned energy, complete source erasure, or sign-reversed vacuous upper boundedness.

Thus no constant affine coefficient choice supplies new source order for the shared
HB/FZZ-P/PW-B/RBH Ward endpoint.  The proof is unconditional and does not assume bounded aligned
energy or RH.
-/

open Complex Filter
open scoped Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Fixed affine mixing of the positive transition core and its aligned completed residual. -/
def suzukiTransitionCoreFixedAffineSignedCorrection
    (a b : ℝ) (N : ℕ) : ℝ :=
  a * suzukiNaturalApertureTransitionCoreCauchyEnergy N +
    b * suzukiTransitionCoreAlignedGammaCompletedEnergy N

/-- Transition-core residual left after a fixed affine signed correction. -/
def suzukiTransitionCoreFixedAffineResidual
    (a b : ℝ) (N : ℕ) : ℝ :=
  suzukiNaturalApertureTransitionCoreCauchyEnergy N -
    suzukiTransitionCoreFixedAffineSignedCorrection a b N

/-- Relative cancellation of the complete transition-core scale. -/
def SuzukiTransitionCoreFixedAffineCorrectionSaturates
    (a b : ℝ) : Prop :=
  Tendsto (fun N : ℕ =>
    suzukiTransitionCoreFixedAffineSignedCorrection a b N /
      suzukiNaturalApertureTransitionCoreCauchyEnergy N) atTop (𝓝 1)

/-- Eventual upper boundedness of the fixed-affine corrected residual. -/
def SuzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove
    (a b : ℝ) : Prop :=
  ∃ B : ℝ, ∀ᶠ N : ℕ in atTop,
    suzukiTransitionCoreFixedAffineResidual a b N ≤ B

/-- The relative limit of every fixed affine correction is exactly its transition-core
coefficient.  The aligned-energy coefficient disappears at relative scale. -/
theorem tendsto_suzukiTransitionCoreFixedAffineSignedCorrection_div_core_atTop
    (a b : ℝ) :
    Tendsto (fun N : ℕ =>
      suzukiTransitionCoreFixedAffineSignedCorrection a b N /
        suzukiNaturalApertureTransitionCoreCauchyEnergy N) atTop (𝓝 a) := by
  have ha : Tendsto (fun _N : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
  have hb : Tendsto (fun _N : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
  have hsum := ha.add
    (hb.mul tendsto_suzukiAlignedEnergy_div_transitionCore_atTop_zero)
  simpa only [mul_zero, add_zero] using hsum.congr' (by
    filter_upwards
      [eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ne_zero]
        with N hcore
    rw [suzukiTransitionCoreFixedAffineSignedCorrection]
    field_simp)

/-- Fixed-affine compensation cancels the complete transition-core scale exactly when the
coefficient of that core is one. -/
theorem suzukiTransitionCoreFixedAffineCorrectionSaturates_iff
    (a b : ℝ) :
    SuzukiTransitionCoreFixedAffineCorrectionSaturates a b ↔ a = 1 := by
  constructor
  · intro hsat
    exact tendsto_nhds_unique
      (tendsto_suzukiTransitionCoreFixedAffineSignedCorrection_div_core_atTop a b)
      hsat
  · rintro rfl
    exact tendsto_suzukiTransitionCoreFixedAffineSignedCorrection_div_core_atTop 1 b

/-- Once core saturation is imposed, the entire residual is exactly a scalar multiple of the
aligned completed energy. -/
theorem suzukiTransitionCoreFixedAffineResidual_one_eq
    (b : ℝ) (N : ℕ) :
    suzukiTransitionCoreFixedAffineResidual 1 b N =
      -b * suzukiTransitionCoreAlignedGammaCompletedEnergy N := by
  rw [suzukiTransitionCoreFixedAffineResidual,
    suzukiTransitionCoreFixedAffineSignedCorrection]
  ring

/-- Negative aligned coefficient is precisely the positive-energy chamber. -/
theorem suzukiTransitionCoreFixedAffineResidual_one_nonneg_of_neg
    {b : ℝ} (hb : b < 0) (N : ℕ) :
    0 ≤ suzukiTransitionCoreFixedAffineResidual 1 b N := by
  rw [suzukiTransitionCoreFixedAffineResidual_one_eq]
  exact mul_nonneg (by linarith)
    (suzukiTransitionCoreAlignedGammaCompletedEnergy_nonneg N)

/-- In the positive-energy chamber, boundedness of the affine residual is exactly boundedness of
the aligned completed energy. -/
theorem suzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove_iff_alignedEnergy
    {b : ℝ} (hb : b < 0) :
    SuzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove 1 b ↔
      SuzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded := by
  have hscale : 0 < -b := by linarith
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B / (-b), ?_⟩
    filter_upwards [hB] with N hN
    rw [suzukiTransitionCoreFixedAffineResidual_one_eq] at hN
    rw [le_div_iff₀ hscale]
    nlinarith
  · rintro ⟨B, hB⟩
    refine ⟨(-b) * B, ?_⟩
    filter_upwards [hB] with N hN
    rw [suzukiTransitionCoreFixedAffineResidual_one_eq]
    exact mul_le_mul_of_nonneg_left hN hscale.le

/-- Every nontrivial positive fixed-affine residual is bounded exactly under RH. -/
theorem riemannHypothesis_iff_suzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove_of_neg
    {b : ℝ} (hb : b < 0) :
    RiemannHypothesis ↔
      SuzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove 1 b := by
  exact
    riemannHypothesis_iff_suzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded.trans
      (suzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove_iff_alignedEnergy hb).symm

/-- Zero aligned coefficient erases the corrected source completely. -/
theorem suzukiTransitionCoreFixedAffineResidual_one_eq_zero_of_eq_zero
    {b : ℝ} (hb : b = 0) (N : ℕ) :
    suzukiTransitionCoreFixedAffineResidual 1 b N = 0 := by
  rw [hb, suzukiTransitionCoreFixedAffineResidual_one_eq]
  ring

/-- Positive aligned coefficient reverses the nonnegative energy sign. -/
theorem suzukiTransitionCoreFixedAffineResidual_one_nonpos_of_pos
    {b : ℝ} (hb : 0 < b) (N : ℕ) :
    suzukiTransitionCoreFixedAffineResidual 1 b N ≤ 0 := by
  rw [suzukiTransitionCoreFixedAffineResidual_one_eq]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
    (suzukiTransitionCoreAlignedGammaCompletedEnergy_nonneg N)

/-- Sign-reversed affine residuals are vacuously upper bounded by zero. -/
theorem suzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove_of_pos
    {b : ℝ} (hb : 0 < b) :
    SuzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove 1 b := by
  refine ⟨0, Filter.Eventually.of_forall fun N => ?_⟩
  exact suzukiTransitionCoreFixedAffineResidual_one_nonpos_of_pos hb N

/-- **Fixed-affine signed-compensation route classification.**  Every constant affine mixing is
either nonsaturating, a positive scalar copy of the exact RH-equivalent aligned energy, complete
source erasure, or sign-reversed vacuous upper boundedness. -/
theorem suzukiFixedAffineSignedCompensation_routeClassification
    (a b : ℝ) :
    Tendsto (fun N : ℕ =>
      suzukiTransitionCoreFixedAffineSignedCorrection a b N /
        suzukiNaturalApertureTransitionCoreCauchyEnergy N) atTop (𝓝 a) ∧
    (SuzukiTransitionCoreFixedAffineCorrectionSaturates a b ↔ a = 1) ∧
    (b < 0 →
      (∀ N : ℕ, 0 ≤ suzukiTransitionCoreFixedAffineResidual 1 b N) ∧
      (RiemannHypothesis ↔
        SuzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove 1 b)) ∧
    (b = 0 → ∀ N : ℕ,
      suzukiTransitionCoreFixedAffineResidual 1 b N = 0) ∧
    (0 < b →
      (∀ N : ℕ, suzukiTransitionCoreFixedAffineResidual 1 b N ≤ 0) ∧
      SuzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove 1 b) := by
  refine ⟨tendsto_suzukiTransitionCoreFixedAffineSignedCorrection_div_core_atTop a b,
    suzukiTransitionCoreFixedAffineCorrectionSaturates_iff a b, ?_, ?_, ?_⟩
  · intro hb
    exact ⟨suzukiTransitionCoreFixedAffineResidual_one_nonneg_of_neg hb,
      riemannHypothesis_iff_suzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove_of_neg hb⟩
  · intro hb N
    exact suzukiTransitionCoreFixedAffineResidual_one_eq_zero_of_eq_zero hb N
  · intro hb
    exact ⟨suzukiTransitionCoreFixedAffineResidual_one_nonpos_of_pos hb,
      suzukiTransitionCoreFixedAffineResidualEventuallyBoundedAbove_of_pos hb⟩

end

end GaloisForLFunctions.RHTower
