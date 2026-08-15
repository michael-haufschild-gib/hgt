import GaloisForLFunctions.RHTower.FrankensteinCCMRoutePApertureTailFluxBridge
import GaloisForLFunctions.RHTower.CCMGuinandWeilPrimeEntryThirdJetConnection

open Matrix Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive change of density from the CCM prime-entry third jet to P-G189 tail flux. -/
def frankensteinRoutePTailFluxThirdJetDressing (n : ℕ) : ℝ :=
  Real.exp (-Real.log n / 2) * Real.log n / 64

theorem frankensteinRoutePTailFluxThirdJetDressing_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < frankensteinRoutePTailFluxThirdJetDressing n := by
  rw [frankensteinRoutePTailFluxThirdJetDressing]
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  positivity

/-- Exact atomwise coefficient seam: P-G189 flux is a positive dressing of the actual CCM
prime-entry third-jet scale. -/
theorem routePPrimeGammaApertureDefectFluxWeight_eq_dressing_mul_thirdJetScale
    {n : ℕ} (hn : 2 ≤ n) :
    routePPrimeGammaApertureDefectFluxWeight n =
      frankensteinRoutePTailFluxThirdJetDressing n *
        ccmGuinandWeilPrimeEntryThirdJetScale n := by
  rw [← criticalMellinAtomWeight_mul_tailFluxGreenProfile hn,
    ccmRoutePApertureTailFluxGreenLogProfile_log hn,
    frankensteinRoutePTailFluxThirdJetDressing,
    ccmGuinandWeilPrimeEntryThirdJetScale]
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  field_simp [hlog]
  ring

theorem routePPrimitiveBurnolApertureDefectFlux_eq_dressing_mul_thirdJetScale
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveBurnolApertureDefectFlux pe =
      frankensteinRoutePTailFluxThirdJetDressing
          (xiGammaEulerValuationNat pe) *
        ccmGuinandWeilPrimeEntryThirdJetScale
          (xiGammaEulerValuationNat pe) := by
  have hn : 2 ≤ xiGammaEulerValuationNat pe := by
    rw [xiGammaEulerValuationNat]
    exact pe.1.property.two_le.trans (Nat.le_pow (by omega))
  rw [← routePPrimeGammaApertureDefectFluxWeight_valuation]
  exact routePPrimeGammaApertureDefectFluxWeight_eq_dressing_mul_thirdJetScale hn

/-- Finite P-G189 flux carried in the universal transverse CCM third-jet direction. -/
def frankensteinRoutePTailFluxCCMThirdJet
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ∑ pe ∈ S, routePPrimitiveBurnolApertureDefectFlux pe •
    ccmGuinandWeilPrimeEntryUniversalThirdJet N

theorem frankensteinRoutePTailFluxCCMThirdJet_eq_rate_smul
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    frankensteinRoutePTailFluxCCMThirdJet S N =
      (∑ pe ∈ S, routePPrimitiveBurnolApertureDefectFlux pe) •
        ccmGuinandWeilPrimeEntryUniversalThirdJet N := by
  rw [frankensteinRoutePTailFluxCCMThirdJet, Finset.sum_smul]

/-- Coefficient-faithful identification with the literal CCM prime-entry third jets. Prime and
depth labels remain visible through `xiGammaEulerValuationNat`. -/
theorem frankensteinRoutePTailFluxCCMThirdJet_eq_dressed_primeEntryThirdJets
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    frankensteinRoutePTailFluxCCMThirdJet S N =
      ∑ pe ∈ S,
        frankensteinRoutePTailFluxThirdJetDressing
            (xiGammaEulerValuationNat pe) •
          ccmGuinandWeilPrimeEntryCenteredMatrixJet3
            (xiGammaEulerValuationNat pe) N := by
  rw [frankensteinRoutePTailFluxCCMThirdJet]
  apply Finset.sum_congr rfl
  intro pe hpe
  have hn : 1 < xiGammaEulerValuationNat pe := by
    rw [xiGammaEulerValuationNat]
    exact pe.1.property.one_lt.trans_le (Nat.le_pow (by omega))
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_eq_scale_smul hn,
    smul_smul,
    ← routePPrimitiveBurnolApertureDefectFlux_eq_dressing_mul_thirdJetScale]

/-- Exact centered quadratic law. P-G189's square-root current activates precisely the first
clock-moment direction which the CCM first and second jets cannot see. -/
theorem frankensteinRoutePTailFluxCCMThirdJet_quadratic_of_sum_eq_zero
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    dotProduct v (frankensteinRoutePTailFluxCCMThirdJet S N *ᵥ v) =
      2 * Real.pi ^ 2 *
        (∑ pe ∈ S, routePPrimitiveBurnolApertureDefectFlux pe) *
          (∑ i, ccmPublishedCenteredClock N i * v i) ^ 2 := by
  rw [frankensteinRoutePTailFluxCCMThirdJet_eq_rate_smul,
    Matrix.smul_mulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum,
    ccmGuinandWeilPrimeEntryUniversalThirdJet_quadratic_of_sum_eq_zero N v hv]
  ring

theorem frankensteinRoutePTailFluxCCMThirdJet_quadratic_nonneg_of_sum_eq_zero
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    0 ≤ dotProduct v (frankensteinRoutePTailFluxCCMThirdJet S N *ᵥ v) := by
  rw [frankensteinRoutePTailFluxCCMThirdJet_quadratic_of_sum_eq_zero S N v hv]
  have hrate : 0 ≤ ∑ pe ∈ S, routePPrimitiveBurnolApertureDefectFlux pe :=
    Finset.sum_nonneg fun pe hpe =>
      (routePPrimitiveBurnolApertureDefectFlux_pos pe).le
  positivity

theorem frankensteinRoutePTailFluxCCMThirdJet_quadratic_pos_of_sum_eq_zero
    {S : Finset (Nat.Primes × ℕ)} (hS : S.Nonempty) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0)
    (hmoment : (∑ i, ccmPublishedCenteredClock N i * v i) ≠ 0) :
    0 < dotProduct v (frankensteinRoutePTailFluxCCMThirdJet S N *ᵥ v) := by
  rw [frankensteinRoutePTailFluxCCMThirdJet_quadratic_of_sum_eq_zero S N v hv]
  have hrate : 0 < ∑ pe ∈ S, routePPrimitiveBurnolApertureDefectFlux pe :=
    Finset.sum_pos
      (fun pe hpe => routePPrimitiveBurnolApertureDefectFlux_pos pe) hS
  positivity

/-- Literal finite P-G188 tail channel before taking its first aperture variation. -/
def frankensteinRoutePTailCCMTransverseConnection
    (c : ℝ) (S : Finset (Nat.Primes × ℕ)) (kappa : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ∑ pe ∈ S, routePPrimitiveBurnolApertureTailDefectEnergy c pe kappa •
    ccmGuinandWeilPrimeEntryUniversalThirdJet N

/-- The literal distributed P-G188 tail connection differentiates entrywise to the
coefficient-faithful transverse CCM third-jet connection. -/
theorem hasDerivWithinAt_frankensteinRoutePTailCCMTransverseConnection_zero_apply
    (S : Finset (Nat.Primes × ℕ)) (kappa : ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    HasDerivWithinAt
      (fun c : ℝ =>
        frankensteinRoutePTailCCMTransverseConnection c S kappa N i j)
      (frankensteinRoutePTailFluxCCMThirdJet S N i j) (Set.Ici 0) 0 := by
  have hsum : HasDerivWithinAt
      (fun c : ℝ =>
        ∑ pe ∈ S, routePPrimitiveBurnolApertureTailDefectEnergy c pe kappa)
      (∑ pe ∈ S, routePPrimitiveBurnolApertureDefectFlux pe) (Set.Ici 0) 0 := by
    apply HasDerivWithinAt.sum
    intro pe hpe
    exact hasDerivWithinAt_routePPrimitiveBurnolApertureTailDefectEnergy_zero pe kappa
  have hmul := hsum.mul_const
    (ccmGuinandWeilPrimeEntryUniversalThirdJet N i j)
  simpa [frankensteinRoutePTailCCMTransverseConnection,
    frankensteinRoutePTailFluxCCMThirdJet, Matrix.smul_apply,
    Finset.sum_mul] using hmul

end

end RHTower
