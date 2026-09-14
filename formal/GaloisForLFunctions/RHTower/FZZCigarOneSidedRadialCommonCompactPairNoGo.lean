import GaloisForLFunctions.RHTower.FZZCigarOneSidedRadialReflectionSelector

/-!
# One-sided FZZ conjugate-pair common-compact classification

One common complex compact response, with no reality or phase restriction, cancels both reflected
one-sided receivers exactly at zero momentum. This kills every nonzero-momentum branch that fits
one source response to a conjugate pair. Orientation-sensitive cancellation instead forces an
exact conjugate-odd compact-response law.
-/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- One source-fixed complex compact response cannot cancel a nontrivial reflected pair. -/
theorem fzzOneSidedRadial_commonConjugatePairCancellation_imp_zeroMomentum
    {radialCoupling radialScale momentum : ℝ} {compactResponse : ℂ}
    (hplus : deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) momentum + compactResponse = 0)
    (hminus : deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) (-momentum) + compactResponse = 0) :
    momentum = 0 := by
  have heq : deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) momentum =
      deriv (fzzMarkedRadialReplicaResponse
        radialCoupling radialScale) (-momentum) := by
    linear_combination hplus - hminus
  have hre := congrArg Complex.re heq
  rw [fzzMarkedRadialReplicaResponse_momentum_deriv_neg_re] at hre
  have hzero : (deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) momentum).re = 0 := by
    linarith
  exact (fzzMarkedRadialReplicaResponse_momentum_deriv_re_eq_zero_iff
    radialCoupling radialScale momentum).1 hzero

/-- Strong positive survivor: responses cancelling two orientations must be conjugate-odd. -/
theorem fzzOneSidedRadial_cancellingCompactResponses_neg_eq_neg_conj
    {radialCoupling radialScale momentum : ℝ} {positiveResponse negativeResponse : ℂ}
    (hplus : deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) momentum + positiveResponse = 0)
    (hminus : deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) (-momentum) + negativeResponse = 0) :
    negativeResponse = -conj positiveResponse := by
  have hplusConj := congrArg conj hplus
  simp only [map_add, map_zero] at hplusConj
  rw [fzzMarkedRadialReplicaResponse_momentum_deriv_neg_eq_neg_conj] at hminus
  calc
    negativeResponse = conj (deriv (fzzMarkedRadialReplicaResponse
        radialCoupling radialScale) momentum) := by
      linear_combination hminus
    _ = -conj positiveResponse := by
      linear_combination hplusConj

/-- Target-independent response fixed by cancellation at reflection-symmetric vacuum momentum. -/
def fzzOneSidedRadialVacuumAnchoredCompactResponse
    (radialCoupling radialScale : ℝ) : ℂ :=
  -deriv (fzzMarkedRadialReplicaResponse radialCoupling radialScale) 0

/-- Vacuum-anchored response cancels both reflected receivers exactly at zero momentum. -/
theorem fzzOneSidedRadialVacuumAnchoredConjugatePairCancellation_iff
    (radialCoupling radialScale momentum : ℝ) :
    (deriv (fzzMarkedRadialReplicaResponse
        radialCoupling radialScale) momentum +
          fzzOneSidedRadialVacuumAnchoredCompactResponse
            radialCoupling radialScale = 0 ∧
      deriv (fzzMarkedRadialReplicaResponse
        radialCoupling radialScale) (-momentum) +
          fzzOneSidedRadialVacuumAnchoredCompactResponse
            radialCoupling radialScale = 0) ↔
      momentum = 0 := by
  constructor
  · intro h
    exact fzzOneSidedRadial_commonConjugatePairCancellation_imp_zeroMomentum h.1 h.2
  · rintro rfl
    simp [fzzOneSidedRadialVacuumAnchoredCompactResponse]

/-- One common response cancels both reflected receivers exactly at zero momentum. -/
theorem exists_fzzOneSidedRadial_commonConjugatePairCancellation_iff
    (radialCoupling radialScale momentum : ℝ) :
    (∃ compactResponse : ℂ,
      deriv (fzzMarkedRadialReplicaResponse
          radialCoupling radialScale) momentum + compactResponse = 0 ∧
        deriv (fzzMarkedRadialReplicaResponse
          radialCoupling radialScale) (-momentum) + compactResponse = 0) ↔
      momentum = 0 := by
  constructor
  · rintro ⟨compactResponse, hplus, hminus⟩
    exact fzzOneSidedRadial_commonConjugatePairCancellation_imp_zeroMomentum hplus hminus
  · intro hmomentum
    refine ⟨fzzOneSidedRadialVacuumAnchoredCompactResponse
      radialCoupling radialScale, ?_⟩
    exact (fzzOneSidedRadialVacuumAnchoredConjugatePairCancellation_iff
      radialCoupling radialScale momentum).2 hmomentum

/-- Nonzero-momentum common-compact conjugate-pair route class. -/
def FZZOneSidedRadialNonzeroCommonCompactPairRouteKilled : Prop :=
  ∀ radialCoupling radialScale momentum : ℝ, momentum ≠ 0 →
    ∀ compactResponse : ℂ,
      ¬ (deriv (fzzMarkedRadialReplicaResponse
          radialCoupling radialScale) momentum + compactResponse = 0 ∧
        deriv (fzzMarkedRadialReplicaResponse
          radialCoupling radialScale) (-momentum) + compactResponse = 0)

/-- **FZZ-P route kill.** No source-fixed complex compact response fits a nonzero reflected pair. -/
theorem fzzOneSidedRadialNonzeroCommonCompactPairRouteKilled :
    FZZOneSidedRadialNonzeroCommonCompactPairRouteKilled := by
  intro radialCoupling radialScale momentum hmomentum compactResponse hpair
  exact hmomentum
    (fzzOneSidedRadial_commonConjugatePairCancellation_imp_zeroMomentum hpair.1 hpair.2)

end

end GaloisForLFunctions.RHTower
