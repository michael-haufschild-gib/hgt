import GaloisForLFunctions.RHTower.CCMActualHeadMatchedWallLightQuadraticJet
import GaloisForLFunctions.RHTower.CCMGuinandWeilPrimeEntryWallFieldWeld

/-!
# Matched wall-light quadratic jet as a dressed CCM third-jet connection

The quadratic center jet forced by matched polar orientation is exactly a positive, source-defined
dressing of the corpus CCM/Suzuki prime-entry third-jet scale. Prime and valuation-depth labels
remain visible, and finite packets inherit the universal centered square law.
-/

open Matrix
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Forced change of jet grade from the cubic prime-entry scale to matched wall-light contact. -/
def ccmActualHeadMatchedWallLightThirdJetDressing (n : ℕ) : ℝ :=
  Real.pi / 8 * Real.log n ^ (4 : ℕ) * ccmActualHeadMatchedOrientedFirstMoment n

theorem ccmActualHeadMatchedWallLightThirdJetDressing_nonneg (n : ℕ) :
    0 ≤ ccmActualHeadMatchedWallLightThirdJetDressing n := by
  unfold ccmActualHeadMatchedWallLightThirdJetDressing
  have hpi : 0 ≤ Real.pi / 8 := div_nonneg Real.pi_pos.le (by norm_num)
  exact mul_nonneg (mul_nonneg hpi (by positivity))
    (ccmActualHeadMatchedOrientedFirstMoment_nonneg n)

theorem ccmActualHeadMatchedWallLightThirdJetDressing_primePower_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < ccmActualHeadMatchedWallLightThirdJetDressing
      (xiGammaEulerValuationNat (p, e)) := by
  unfold ccmActualHeadMatchedWallLightThirdJetDressing
  have hlog : 0 < Real.log (xiGammaEulerValuationNat (p, e) : ℝ) :=
    Real.log_pos (by exact_mod_cast (one_lt_xiGammaEulerValuationNat p e))
  have hmoment := ccmActualHeadMatchedOrientedFirstMoment_primePower_pos p e
  positivity

/-- Atomwise coefficient seam: quadratic wall-light contact is a positive dressing of the actual
CCM prime-entry third-jet scale. -/
theorem ccmActualHeadMatchedWallLightOrientedQuadraticJet_eq_dressing_mul_thirdJetScale
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMatchedWallLightOrientedQuadraticJet p e =
      ccmActualHeadMatchedWallLightThirdJetDressing
          (xiGammaEulerValuationNat (p, e)) *
        ccmGuinandWeilPrimeEntryThirdJetScale
          (xiGammaEulerValuationNat (p, e)) := by
  let n := xiGammaEulerValuationNat (p, e)
  have hn : 1 < n := one_lt_xiGammaEulerValuationNat p e
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  rw [ccmActualHeadMatchedWallLightOrientedQuadraticJet,
    ccmActualHeadMatchedWallLightThirdJetDressing,
    ccmGuinandWeilPrimeEntryThirdJetScale]
  field_simp [hlog]
  ring

/-- Finite label-faithful connection carried by matched wall-light quadratic jets. -/
def ccmActualHeadMatchedWallLightThirdJetConnection
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ∑ pe ∈ S,
    ccmActualHeadMatchedWallLightOrientedQuadraticJet pe.1 pe.2 •
      ccmGuinandWeilPrimeEntryUniversalThirdJet N

theorem ccmActualHeadMatchedWallLightThirdJetConnection_eq_rate_smul
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    ccmActualHeadMatchedWallLightThirdJetConnection S N =
      (∑ pe ∈ S,
        ccmActualHeadMatchedWallLightOrientedQuadraticJet pe.1 pe.2) •
        ccmGuinandWeilPrimeEntryUniversalThirdJet N := by
  rw [ccmActualHeadMatchedWallLightThirdJetConnection, Finset.sum_smul]

/-- Coefficient-faithful identification with the literal CCM prime-entry third jets. -/
theorem ccmActualHeadMatchedWallLightThirdJetConnection_eq_dressed_primeEntryThirdJets
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    ccmActualHeadMatchedWallLightThirdJetConnection S N =
      ∑ pe ∈ S,
        ccmActualHeadMatchedWallLightThirdJetDressing
            (xiGammaEulerValuationNat pe) •
          ccmGuinandWeilPrimeEntryCenteredMatrixJet3
            (xiGammaEulerValuationNat pe) N := by
  rw [ccmActualHeadMatchedWallLightThirdJetConnection]
  apply Finset.sum_congr rfl
  intro pe hpe
  have hn : 1 < xiGammaEulerValuationNat pe := by
    exact one_lt_xiGammaEulerValuationNat pe.1 pe.2
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_eq_scale_smul hn,
    smul_smul,
    ← ccmActualHeadMatchedWallLightOrientedQuadraticJet_eq_dressing_mul_thirdJetScale]

/-- Exact centered square law for every finite matched wall-light packet. -/
theorem ccmActualHeadMatchedWallLightThirdJetConnection_quadratic_of_sum_eq_zero
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    dotProduct v (ccmActualHeadMatchedWallLightThirdJetConnection S N *ᵥ v) =
      2 * Real.pi ^ (2 : ℕ) *
        (∑ pe ∈ S,
          ccmActualHeadMatchedWallLightOrientedQuadraticJet pe.1 pe.2) *
          (∑ i, ccmPublishedCenteredClock N i * v i) ^ (2 : ℕ) := by
  rw [ccmActualHeadMatchedWallLightThirdJetConnection_eq_rate_smul,
    Matrix.smul_mulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  have hfactor :
      (∑ x, v x *
        ((∑ pe ∈ S,
          ccmActualHeadMatchedWallLightOrientedQuadraticJet pe.1 pe.2) *
            (ccmGuinandWeilPrimeEntryUniversalThirdJet N *ᵥ v) x)) =
        (∑ pe ∈ S,
          ccmActualHeadMatchedWallLightOrientedQuadraticJet pe.1 pe.2) *
          dotProduct v
            (ccmGuinandWeilPrimeEntryUniversalThirdJet N *ᵥ v) := by
    simp only [dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hfactor,
    ccmGuinandWeilPrimeEntryUniversalThirdJet_quadratic_of_sum_eq_zero N v hv]
  ring

/-- Every finite matched wall-light third-jet connection is PSD on the zero-sum sector. -/
theorem ccmActualHeadMatchedWallLightThirdJetConnection_quadratic_nonneg_of_sum_eq_zero
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    0 ≤ dotProduct v
      (ccmActualHeadMatchedWallLightThirdJetConnection S N *ᵥ v) := by
  rw [ccmActualHeadMatchedWallLightThirdJetConnection_quadratic_of_sum_eq_zero S N v hv]
  have hrate : 0 ≤ ∑ pe ∈ S,
      ccmActualHeadMatchedWallLightOrientedQuadraticJet pe.1 pe.2 :=
    Finset.sum_nonneg fun pe hpe =>
      (ccmActualHeadMatchedWallLightOrientedQuadraticJet_pos pe.1 pe.2).le
  positivity

/-- A nonempty packet is strictly positive on every visible first-clock direction. -/
theorem ccmActualHeadMatchedWallLightThirdJetConnection_quadratic_pos_of_sum_eq_zero
    {S : Finset (Nat.Primes × ℕ)} (hS : S.Nonempty) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0)
    (hmoment : (∑ i, ccmPublishedCenteredClock N i * v i) ≠ 0) :
    0 < dotProduct v
      (ccmActualHeadMatchedWallLightThirdJetConnection S N *ᵥ v) := by
  rw [ccmActualHeadMatchedWallLightThirdJetConnection_quadratic_of_sum_eq_zero S N v hv]
  obtain ⟨pe, hpe⟩ := hS
  have hrate : 0 < ∑ pe ∈ S,
      ccmActualHeadMatchedWallLightOrientedQuadraticJet pe.1 pe.2 := by
    have hlt : (∑ _pe ∈ S, (0 : ℝ)) < ∑ pe ∈ S,
        ccmActualHeadMatchedWallLightOrientedQuadraticJet pe.1 pe.2 := by
      apply Finset.sum_lt_sum
      · intro x hx
        exact (ccmActualHeadMatchedWallLightOrientedQuadraticJet_pos x.1 x.2).le
      · exact ⟨pe, hpe,
          ccmActualHeadMatchedWallLightOrientedQuadraticJet_pos pe.1 pe.2⟩
    simpa using hlt
  positivity

end RHTower
