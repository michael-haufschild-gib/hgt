import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFloorTransportFromTheCertifiedEndpoint

/-!
# The aperture floor under absolute decay

The multiplicative transport of the aperture floor asks for a bound on the *relative* loss per step.
The additive form is often the one an estimate delivers, and it transports just as well, by
telescoping:

`μ_{j+1} ≥ μ_j − r_j`  ⟹  `μ_J ≥ μ_0 − Σ_{j<J} r_j`  (`sub_sum_le_of_additive_step`).

With the certified endpoint `μ(3/10) ≥ 1/5000` this gives the absolute-decay criterion: a total
absolute loss below `1/10000` along an unbounded aperture sequence keeps the ground energy above
`1/10000` at every aperture of the sequence (`groundEnergy_ge_of_additive_step`), hence the
nonnegative-ground-energy apertures are unbounded and the Riemann hypothesis holds
(`riemannHypothesis_of_groundEnergy_additive_step`).  Every aperture below one of the sequence is
then window positive, which is the aperture face's own unit
(`zetaWindowPositive_of_additive_step`).

Neither form differentiates the ground energy: both compare it only with its own previous value, so
they apply to a floor defined as an infimum.
-/

open Finset RHTower
open GaloisForLFunctions.SquareRootThreshold GaloisForLFunctions.ArithmeticCriticalityTheory

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Additive transport -/

/-- **Per-step absolute transport.**  A floor losing at most `r_j` per step keeps all but the total
loss. -/
theorem sub_sum_le_of_additive_step {μ r : ℕ → ℝ} (hstep : ∀ j, μ j - r j ≤ μ (j + 1)) (J : ℕ) :
    μ 0 - ∑ j ∈ range J, r j ≤ μ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    have h := hstep J
    rw [Finset.sum_range_succ]
    linarith

/-! ## §2. The aperture instance -/

/-- **The transported aperture floor under absolute decay.** -/
theorem groundEnergy_ge_of_additive_step {A : ℕ → SuzukiPositiveAperture} {r : ℕ → ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hr : ∀ J : ℕ, (∑ j ∈ range J, r j) ≤ 1 / 10000)
    (hstep : ∀ j, ccmRestrictedWeilGroundEnergy (A j) - r j ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1))) (J : ℕ) :
    1 / 10000 ≤ ccmRestrictedWeilGroundEnergy (A J) := by
  have hbase : 1 / 5000 ≤ ccmRestrictedWeilGroundEnergy (A 0) :=
    one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths hA0
  have h := sub_sum_le_of_additive_step
    (μ := fun j => ccmRestrictedWeilGroundEnergy (A j)) hstep J
  have hrJ := hr J
  linarith

/-- **The absolute-decay criterion for the Riemann hypothesis.** -/
theorem riemannHypothesis_of_groundEnergy_additive_step {A : ℕ → SuzukiPositiveAperture}
    {r : ℕ → ℝ} (hA0 : (A 0).1 ≤ 3 / 10)
    (hAtop : Filter.Tendsto (fun j => (A j).1) Filter.atTop Filter.atTop)
    (hr : ∀ J : ℕ, (∑ j ∈ range J, r j) ≤ 1 / 10000)
    (hstep : ∀ j, ccmRestrictedWeilGroundEnergy (A j) - r j ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1))) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures]
  rintro ⟨M, hM⟩
  obtain ⟨J, hJ⟩ := (hAtop.eventually_gt_atTop M).exists
  have hmem : (A J).1 ∈ groundEnergyNonnegApertures := by
    refine ⟨(A J).2, ?_⟩
    have h := groundEnergy_ge_of_additive_step hA0 hr hstep J
    have hcongr : ccmRestrictedWeilGroundEnergy ⟨(A J).1, (A J).2⟩ =
        ccmRestrictedWeilGroundEnergy (A J) := by congr 1
    rw [hcongr]
    linarith
  exact absurd (hM hmem) (not_le.mpr hJ)

/-- **Window positivity below every aperture of the sequence.**  The aperture face's own unit. -/
theorem zetaWindowPositive_of_additive_step {A : ℕ → SuzukiPositiveAperture} {r : ℕ → ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hr : ∀ J : ℕ, (∑ j ∈ range J, r j) ≤ 1 / 10000)
    (hstep : ∀ j, ccmRestrictedWeilGroundEnergy (A j) - r j ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1))) (J : ℕ) {B : ℝ} (hB : 0 < B)
    (hBA : B < (A J).1) : ZetaWindowPositive B := by
  have hmem : (A J).1 ∈ groundEnergyNonnegApertures := by
    refine ⟨(A J).2, ?_⟩
    have h := groundEnergy_ge_of_additive_step hA0 hr hstep J
    have hcongr : ccmRestrictedWeilGroundEnergy ⟨(A J).1, (A J).2⟩ =
        ccmRestrictedWeilGroundEnergy (A J) := by congr 1
    rw [hcongr]
    linarith
  exact (Ioo_subset_windowPositiveApertures hmem ⟨hB, hBA⟩).2

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
