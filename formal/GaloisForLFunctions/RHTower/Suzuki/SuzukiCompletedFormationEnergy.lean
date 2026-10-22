import GaloisForLFunctions.HTGeometry.AnchoredCesaroVarianceCompletion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAnchoredCesaroScaleConnection

/-!
# Suzuki completed formation energy

The exact terminal correction of the anchored Suzuki scale connection is integrated into a
canonical scale primitive.  The completed Abel source then becomes a pure connection current, and
its square is exact production of a monotone, divisor-free Dirichlet action.  Existing
condition-number transport proves that bounded local production of this source action is equivalent
to RH.  This equivalence does not prove the required bounded-production estimate.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Completed Suzuki scale potential after integrating the literal terminal correction current. -/
def suzukiCompletedFormationPotential (N : ℕ) : ℝ :=
  completedScalePotential suzukiCheckpointAffineSlope
    suzukiTransitionCoreCesaroTerminalCorrection N

/-- Divisor-free Dirichlet action of the completed Suzuki scale potential. -/
def suzukiCompletedFormationEnergy (N : ℕ) : ℝ :=
  completedScaleDirichletEnergy suzukiCheckpointAffineSlope
    suzukiTransitionCoreCesaroTerminalCorrection N

/-- Completed Suzuki formation energy is unconditionally monotone along scale. -/
theorem suzukiCompletedFormationEnergy_monotoneOn
    {K N : ℕ} (hK : 2 ≤ K) (hKN : K ≤ N) :
    suzukiCompletedFormationEnergy K ≤ suzukiCompletedFormationEnergy N := by
  exact completedScaleDirichletEnergy_monotoneOn
    suzukiCheckpointAffineSlope suzukiTransitionCoreCesaroTerminalCorrection hK hKN

/-- Completed Abel source is exactly the weighted increment of the completed potential. -/
theorem suzukiTransitionCoreCompletedAbelSource_succ_eq_completedFormationCurrent
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreCompletedAbelSource (N + 1) =
      (N + 2 : ℕ) *
        (suzukiCompletedFormationPotential (N + 1) -
          suzukiCompletedFormationPotential N) := by
  rw [suzukiTransitionCoreCompletedAbelSource_succ_eq_scaleConnection hN]
  rw [suzukiCompletedFormationPotential,
    suzukiCompletedFormationPotential]
  have hcurrent := completedScalePotential_scaled_succ_sub
    suzukiCheckpointAffineSlope suzukiTransitionCoreCesaroTerminalCorrection hN
  rw [anchoredCesaroHighPass_eq_scaled_potentialIncrement _ hN] at hcurrent
  unfold suzukiCheckpointAffineSlopeCesaroPotential
  linarith

/-- Completed formation-energy production is one positive Abel-current square. -/
theorem suzukiCompletedFormationEnergy_succ_sub
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCompletedFormationEnergy (N + 1) -
        suzukiCompletedFormationEnergy N =
      ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) *
        (suzukiTransitionCoreCompletedAbelSource (N + 1)) ^ (2 : ℕ) := by
  rw [suzukiCompletedFormationEnergy, suzukiCompletedFormationEnergy,
    completedScaleDirichletEnergy_succ_sub _ _ hN]
  have hsource := suzukiTransitionCoreCompletedAbelSource_succ_eq_scaleConnection hN
  rw [anchoredCesaroHighPass_eq_scaled_potentialIncrement _ hN]
  unfold suzukiCheckpointAffineSlopeCesaroPotential at hsource
  rw [← hsource]

/-- The Abel square is exactly the scale-normalised production of completed formation energy. -/
theorem suzukiCompletedAbelSource_sq_eq_scaledFormationProduction
    {N : ℕ} (hN : 2 ≤ N) :
    (suzukiTransitionCoreCompletedAbelSource (N + 1)) ^ (2 : ℕ) =
      (((N + 2 : ℕ) : ℝ) / (N + 1 : ℕ)) *
        (suzukiCompletedFormationEnergy (N + 1) -
          suzukiCompletedFormationEnergy N) := by
  rw [suzukiCompletedFormationEnergy_succ_sub hN]
  have hN1 : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hN2 : (((N + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hN1, hN2]

/-- Exact Gamma readout of completed formation-energy production. -/
theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_formationProduction
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) =
      (suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) /
          unitRieszCoherentPrimeOutgoingCharge (N + 1) ^ (2 : ℕ)) *
        (((N + 2 : ℕ) : ℝ) / (N + 1 : ℕ)) *
        (suzukiCompletedFormationEnergy (N + 1) -
          suzukiCompletedFormationEnergy N) := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy_eq_completedAbelSource
      (by omega : 2 ≤ N + 1) hcharge,
    suzukiCompletedFormationEnergy_succ_sub hN]
  have hN1 : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hN2 : (((N + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hcharge, hN1, hN2]

/-- Lower half of eventual condition comparison, valid whenever outgoing charge is nonzero. -/
theorem suzukiScaledFormationProduction_le_alignedGamma
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0) :
    (((N + 2 : ℕ) : ℝ) / (N + 1 : ℕ)) *
        (suzukiCompletedFormationEnergy (N + 1) -
          suzukiCompletedFormationEnergy N) ≤
      suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) := by
  rw [← suzukiCompletedAbelSource_sq_eq_scaledFormationProduction hN]
  rw [← suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource
    (by omega : 2 ≤ N + 1)]
  exact suzukiCompletedAnchor_sq_le_alignedEnergy (by omega) hcharge

/-- Upper half of condition comparison under the certified transition-core bound. -/
theorem suzukiAlignedGamma_le_condition_mul_scaledFormationProduction
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0)
    (hcore : suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) ≤
      suzukiTransitionCoreAnchorConditionNumberBound *
        unitRieszCoherentPrimeOutgoingCharge (N + 1) ^ (2 : ℕ)) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) ≤
      suzukiTransitionCoreAnchorConditionNumberBound *
        ((((N + 2 : ℕ) : ℝ) / (N + 1 : ℕ)) *
          (suzukiCompletedFormationEnergy (N + 1) -
            suzukiCompletedFormationEnergy N)) := by
  rw [← suzukiCompletedAbelSource_sq_eq_scaledFormationProduction hN]
  rw [← suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource
    (by omega : 2 ≤ N + 1)]
  exact suzukiAlignedEnergy_le_condition_mul_completedAnchor_sq hcharge hcore

/-- Unscaled production is bounded above by aligned Gamma energy. -/
theorem suzukiCompletedFormationEnergy_succ_sub_le_alignedGamma
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0) :
    suzukiCompletedFormationEnergy (N + 1) -
        suzukiCompletedFormationEnergy N ≤
      suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) := by
  have hprod := suzukiCompletedFormationEnergy_succ_sub hN
  have hsq := suzukiCompletedAnchor_sq_le_alignedEnergy
    (N := N + 1) (by omega) hcharge
  rw [suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource
    (by omega : 2 ≤ N + 1)] at hsq
  have hcoef : (((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ)) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    norm_num
  have hs : 0 ≤ (suzukiTransitionCoreCompletedAbelSource (N + 1)) ^ (2 : ℕ) := sq_nonneg _
  rw [hprod]
  exact (mul_le_of_le_one_left hs hcoef).trans hsq

/-- Aligned Gamma energy is eventually controlled by completed formation production. -/
theorem suzukiAlignedGamma_le_two_condition_mul_formationProduction
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0)
    (hcore : suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) ≤
      suzukiTransitionCoreAnchorConditionNumberBound *
        unitRieszCoherentPrimeOutgoingCharge (N + 1) ^ (2 : ℕ)) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) ≤
      2 * suzukiTransitionCoreAnchorConditionNumberBound *
        (suzukiCompletedFormationEnergy (N + 1) -
          suzukiCompletedFormationEnergy N) := by
  have hprod := suzukiCompletedFormationEnergy_succ_sub hN
  have hupper := suzukiAlignedEnergy_le_condition_mul_completedAnchor_sq
    hcharge hcore
  rw [suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource
    (by omega : 2 ≤ N + 1)] at hupper
  have hs : 0 ≤ (suzukiTransitionCoreCompletedAbelSource (N + 1)) ^ (2 : ℕ) := sq_nonneg _
  have hhalf : (1 / 2 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) := by
    have hden : (0 : ℝ) < (N + 2 : ℕ) := by positivity
    apply (le_div_iff₀ hden).2
    push_cast
    nlinarith
  have hsqprod :
      (suzukiTransitionCoreCompletedAbelSource (N + 1)) ^ (2 : ℕ) ≤
        2 * (suzukiCompletedFormationEnergy (N + 1) -
          suzukiCompletedFormationEnergy N) := by
    rw [hprod]
    nlinarith [mul_le_mul_of_nonneg_right hhalf hs]
  have hK : 0 ≤ suzukiTransitionCoreAnchorConditionNumberBound := by
    rw [suzukiTransitionCoreAnchorConditionNumberBound]
    positivity
  calc
    _ ≤ suzukiTransitionCoreAnchorConditionNumberBound *
        (suzukiTransitionCoreCompletedAbelSource (N + 1)) ^ (2 : ℕ) := hupper
    _ ≤ suzukiTransitionCoreAnchorConditionNumberBound *
        (2 * (suzukiCompletedFormationEnergy (N + 1) -
          suzukiCompletedFormationEnergy N)) :=
      mul_le_mul_of_nonneg_left hsqprod hK
    _ = _ := by ring

/-- Uniform eventual boundedness of local completed formation-energy production. -/
def SuzukiCompletedFormationEnergyIncrementEventuallyBounded : Prop :=
  ∃ B : ℝ, ∀ᶠ N : ℕ in atTop,
    suzukiCompletedFormationEnergy (N + 1) -
      suzukiCompletedFormationEnergy N ≤ B

private theorem eventuallyBounded_succ_iff (f : ℕ → ℝ) :
    (∃ B : ℝ, ∀ᶠ N : ℕ in atTop, f (N + 1) ≤ B) ↔
      (∃ B : ℝ, ∀ᶠ N : ℕ in atTop, f N ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rw [eventually_atTop] at hB ⊢
    obtain ⟨N₀, hN₀⟩ := hB
    refine ⟨N₀ + 1, ?_⟩
    intro N hN
    have hpos : 1 ≤ N := by omega
    have htail : N₀ ≤ N - 1 := by omega
    simpa [Nat.sub_add_cancel hpos] using hN₀ (N - 1) htail
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact (Filter.tendsto_add_atTop_nat 1).eventually hB

/-- Bounded completed formation production is exactly bounded aligned Gamma energy. -/
theorem suzukiCompletedFormationEnergyIncrementEventuallyBounded_iff_alignedGamma :
    SuzukiCompletedFormationEnergyIncrementEventuallyBounded ↔
      SuzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded := by
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have hcharge := hshift.eventually eventually_unitRieszCoherentPrimeOutgoingCharge_ne_zero
  have hcore := hshift.eventually eventually_suzukiTransitionCore_le_anchorConditionNumber_mul_sq
  have hshifted : SuzukiCompletedFormationEnergyIncrementEventuallyBounded ↔
      ∃ B : ℝ, ∀ᶠ N : ℕ in atTop,
        suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) ≤ B := by
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨2 * suzukiTransitionCoreAnchorConditionNumberBound * B, ?_⟩
      filter_upwards [hB, hcharge, hcore, eventually_ge_atTop (2 : ℕ)]
        with N hbound hchargeN hcoreN hN
      exact (suzukiAlignedGamma_le_two_condition_mul_formationProduction
        hN hchargeN hcoreN).trans (mul_le_mul_of_nonneg_left hbound (by
          have hK : 0 ≤ suzukiTransitionCoreAnchorConditionNumberBound := by
            rw [suzukiTransitionCoreAnchorConditionNumberBound]
            positivity
          positivity))
    · rintro ⟨B, hB⟩
      refine ⟨B, ?_⟩
      filter_upwards [hB, hcharge, eventually_ge_atTop (2 : ℕ)]
        with N hbound hchargeN hN
      exact (suzukiCompletedFormationEnergy_succ_sub_le_alignedGamma
        hN hchargeN).trans hbound
  exact hshifted.trans
    (eventuallyBounded_succ_iff suzukiTransitionCoreAlignedGammaCompletedEnergy)

/-- Exact divisor-free properness coordinate: RH iff completed formation production is bounded. -/
theorem riemannHypothesis_iff_suzukiCompletedFormationEnergyIncrementEventuallyBounded :
    RiemannHypothesis ↔ SuzukiCompletedFormationEnergyIncrementEventuallyBounded :=
  riemannHypothesis_iff_suzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded.trans
    suzukiCompletedFormationEnergyIncrementEventuallyBounded_iff_alignedGamma.symm

end

end GaloisForLFunctions.RHTower
