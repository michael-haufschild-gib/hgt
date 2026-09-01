import GaloisForLFunctions.HTGeometry.ScaleInnovationPhaseGauge
import GaloisForLFunctions.RHTower.SuzukiFormationInnovationHistory

/-!
# Suzuki formation innovation phase gauge

The literal completed Suzuki Abel current is lifted through the common recovery kernel after an
arbitrary independent sign choice at every scale.  Recovery sees every changed sign, whereas
formation variance, local production, and its conditioned aligned-Gamma readout see exactly the
same positive receiver state.  This is the literal local-gauge quotient predicted by the universal
scale-innovation law.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Suzuki history after an arbitrary scale-local reflection of its completed Abel current. -/
def suzukiCompletedFormationPhaseGaugeHistory (epsilon : ℕ → ℝ) : ℕ → ℝ :=
  scaleInnovationHistory (suzukiCompletedFormationInnovationHistory 2)
    (scaleInnovationGaugeCurrent epsilon
      (fun N => suzukiTransitionCoreCompletedAbelSource (N + 1)))

/-- Positive local production read from a phase-gauged Suzuki history. -/
def suzukiCompletedFormationPhaseGaugeEnergy
    (epsilon : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) *
    (anchoredCesaroHighPass
      (suzukiCompletedFormationPhaseGaugeHistory epsilon) N) ^ 2

/-- Gauge-lifted Suzuki history retains every pointwise signed Abel innovation. -/
theorem suzukiCompletedFormationPhaseGaugeHistory_current
    (epsilon : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroHighPass
        (suzukiCompletedFormationPhaseGaugeHistory epsilon) N =
      epsilon N * suzukiTransitionCoreCompletedAbelSource (N + 1) := by
  exact scaleInnovationGaugeCurrent_recovery _ _ _ hN

/-- Every local Suzuki phase gauge has the canonical one-step positive production. -/
theorem suzukiCompletedFormationPhaseGaugeEnergy_eq_innovationEnergy
    (epsilon : ℕ → ℝ) (hphase : ∀ k, (epsilon k) ^ 2 = 1)
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCompletedFormationPhaseGaugeEnergy epsilon N =
      suzukiCompletedFormationInnovationEnergy N := by
  rw [suzukiCompletedFormationPhaseGaugeEnergy,
    suzukiCompletedFormationPhaseGaugeHistory_current epsilon hN,
    suzukiCompletedFormationInnovationEnergy,
    suzukiCompletedFormationInnovationHistory_current hN,
    mul_pow, hphase]
  ring

/-- The literal completed Abel current action is the completed Suzuki formation energy. -/
theorem suzukiCompletedAbelSource_action_eq_formationEnergy
    {N : ℕ} (hN : 2 ≤ N) :
    scaleInnovationAction
        (fun k => suzukiTransitionCoreCompletedAbelSource (k + 1)) N =
      suzukiCompletedFormationEnergy N := by
  induction N, hN using Nat.le_induction with
  | base =>
      unfold scaleInnovationAction suzukiCompletedFormationEnergy
        completedScaleDirichletEnergy scaleDirichletEnergy
      norm_num
  | succ N hN ih =>
      have ha := scaleInnovationAction_succ_sub
        (fun k => suzukiTransitionCoreCompletedAbelSource (k + 1)) hN
      have he := suzukiCompletedFormationEnergy_succ_sub hN
      rw [ih] at ha
      linarith

/-- Accumulated variance of every local phase lift is the canonical Suzuki action. -/
theorem suzukiCompletedFormationPhaseGaugeHistory_variance
    (epsilon : ℕ → ℝ) (hphase : ∀ k, (epsilon k) ^ 2 = 1)
    {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance
        (suzukiCompletedFormationPhaseGaugeHistory epsilon) N =
      suzukiCompletedFormationEnergy N := by
  rw [suzukiCompletedFormationPhaseGaugeHistory,
    scaleInnovationHistory_variance_eq_action _ _ hN,
    scaleInnovationAction_gauge_invariant epsilon _ hphase,
    suzukiCompletedAbelSource_action_eq_formationEnergy hN]

/-- Conditioned aligned-Gamma energy reads the same local production on every phase-gauge orbit. -/
theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_phaseGaugeEnergy
    (epsilon : ℕ → ℝ) (hphase : ∀ k, (epsilon k) ^ 2 = 1)
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) =
      (suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) /
          unitRieszCoherentPrimeOutgoingCharge (N + 1) ^ 2) *
        (((N + 2 : ℕ) : ℝ) / (N + 1 : ℕ)) *
        suzukiCompletedFormationPhaseGaugeEnergy epsilon N := by
  rw [suzukiCompletedFormationPhaseGaugeEnergy_eq_innovationEnergy epsilon hphase hN]
  exact suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_innovationEnergy
    hN hcharge

/-- A nonzero literal Abel current witnesses strict local-gauge nonfaithfulness of positive action. -/
theorem suzukiCompletedFormationSingleFlip_history_ne
    {m : ℕ} (hm : 2 ≤ m)
    (hsource : suzukiTransitionCoreCompletedAbelSource (m + 1) ≠ 0) :
    suzukiCompletedFormationPhaseGaugeHistory (scaleInnovationSingleFlip m) ≠
      scaleInnovationHistory (suzukiCompletedFormationInnovationHistory 2)
        (fun N => suzukiTransitionCoreCompletedAbelSource (N + 1)) := by
  exact scaleInnovationSingleFlip_history_ne _ _ hm hsource

/-- Zero-argument literal Suzuki certificate: every admissible local phase lift preserves local
production, accumulated variance, and conditioned aligned-Gamma energy while nonzero one-site
innovations still distinguish the recovered histories. -/
theorem suzukiFormationInnovationPhaseGauge_certificate :
    (∀ (epsilon : ℕ → ℝ) (N : ℕ), 2 ≤ N →
      anchoredCesaroHighPass
          (suzukiCompletedFormationPhaseGaugeHistory epsilon) N =
        epsilon N * suzukiTransitionCoreCompletedAbelSource (N + 1)) ∧
    (∀ (epsilon : ℕ → ℝ), (∀ k, (epsilon k) ^ 2 = 1) →
      ∀ N : ℕ, 2 ≤ N →
      suzukiCompletedFormationPhaseGaugeEnergy epsilon N =
        suzukiCompletedFormationInnovationEnergy N ∧
      anchoredCesaroVariance
          (suzukiCompletedFormationPhaseGaugeHistory epsilon) N =
        suzukiCompletedFormationEnergy N) ∧
    (∀ N : ℕ, 2 ≤ N →
      scaleInnovationAction
          (fun k => suzukiTransitionCoreCompletedAbelSource (k + 1)) N =
        suzukiCompletedFormationEnergy N) ∧
    (∀ (epsilon : ℕ → ℝ), (∀ k, (epsilon k) ^ 2 = 1) →
      ∀ N : ℕ, 2 ≤ N →
      unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0 →
      suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) =
        (suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) /
            unitRieszCoherentPrimeOutgoingCharge (N + 1) ^ 2) *
          (((N + 2 : ℕ) : ℝ) / (N + 1 : ℕ)) *
          suzukiCompletedFormationPhaseGaugeEnergy epsilon N) ∧
    (∀ m : ℕ, 2 ≤ m →
      suzukiTransitionCoreCompletedAbelSource (m + 1) ≠ 0 →
      suzukiCompletedFormationPhaseGaugeHistory (scaleInnovationSingleFlip m) ≠
        scaleInnovationHistory (suzukiCompletedFormationInnovationHistory 2)
          (fun N => suzukiTransitionCoreCompletedAbelSource (N + 1))) := by
  exact ⟨suzukiCompletedFormationPhaseGaugeHistory_current,
    fun epsilon hphase N hN =>
      ⟨suzukiCompletedFormationPhaseGaugeEnergy_eq_innovationEnergy epsilon hphase hN,
        suzukiCompletedFormationPhaseGaugeHistory_variance epsilon hphase hN⟩,
    fun _ hN => suzukiCompletedAbelSource_action_eq_formationEnergy hN,
    fun epsilon hphase N hN hcharge =>
      suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_phaseGaugeEnergy
        epsilon hphase hN hcharge,
    fun _ hm hsource => suzukiCompletedFormationSingleFlip_history_ne hm hsource⟩

end

end GaloisForLFunctions.RHTower
