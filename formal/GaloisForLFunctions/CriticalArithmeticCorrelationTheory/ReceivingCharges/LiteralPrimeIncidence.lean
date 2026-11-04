import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralUpwardRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.SameSourcePrimeTowers
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PeriodicProfiles
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.AffineIncidences
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.OffsetCollisionMass
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeMoments

/-!
# Exact unit and tower splitting of literal incidences

Periodic unit residues and same-source prime towers give exact formulas
for both original offset signs before finite summation.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset ArithmeticFunction
open GaloisForLFunctions
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence
  CriticalScaleArithmeticRigidity ArithmeticCouplingTheory

/-- Positive literal incidence splits exactly into a periodic unit residue and its own prime tower. -/
theorem positive_literal_incidence_split {G : ℕ → ℝ} {M p k h n : ℕ}
    (hG : Function.Periodic G M) (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
    (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (vonMangoldt k / (k : ℝ)) * positiveLiteralUpwardKernel φ c N k h n * G (k * n + h) *
        ((if p ∣ k * n + h then (1 : ℝ) else 0) - 1 / p) =
      unitMangoldtWeight p k * positiveLiteralUpwardKernel φ c N k h n *
        (G (k * (n % M) + h) * centeredResidue p (multiplierResidue p k (p - h)) n) -
      (if p ∣ k then (vonMangoldt k / (k : ℝ)) *
        positiveLiteralUpwardKernel φ c N k h n * G (k * n + h) / p else 0) := by
  by_cases hpk : p.Coprime k
  · have hnd : ¬p ∣ k := hp.coprime_iff_not_dvd.mp hpk
    rw [unitMangoldtWeight, if_pos hpk, if_neg hnd,
      unit_positive_incidence hpk hhp.le n, periodic_positive_sample hG k h n]
    ring
  · have hd : p ∣ k := by simpa only [hp.coprime_iff_not_dvd, not_not] using hpk
    have hnd := same_source_positive_nondivisibility hd hh hhp
    rw [unitMangoldtWeight, if_neg hpk, if_pos hd, if_neg hnd]
    ring

/-- Genuine negative offsets retain the same exact unit/tower decomposition. -/
theorem negative_literal_incidence_split {G : ℕ → ℝ} {M p k h n : ℕ}
    (hM : 0 < M) (hG : Function.Periodic G M) (hp : p.Prime)
    (hk : 1 ≤ k) (hh : 0 < h) (hhp : h < p) (hhkn : h ≤ k * n)
    (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (vonMangoldt k / (k : ℝ)) * negativeLiteralUpwardKernel φ c N k h n * G (k * n - h) *
        ((if p ∣ k * n - h then (1 : ℝ) else 0) - 1 / p) =
      unitMangoldtWeight p k * negativeLiteralUpwardKernel φ c N k h n *
        (negativePeriodicProfile G M k h (n % M) * centeredResidue p (multiplierResidue p k h) n) -
      (if p ∣ k then (vonMangoldt k / (k : ℝ)) *
        negativeLiteralUpwardKernel φ c N k h n * G (k * n - h) / p else 0) := by
  by_cases hpk : p.Coprime k
  · have hnd : ¬p ∣ k := hp.coprime_iff_not_dvd.mp hpk
    rw [unitMangoldtWeight, if_pos hpk, if_neg hnd,
      unit_negative_incidence hpk hhkn, periodic_negative_sample hM hG hk hhkn]
    ring
  · have hd : p ∣ k := by simpa only [hp.coprime_iff_not_dvd, not_not] using hpk
    have hnd := same_source_negative_nondivisibility hd hh hhp hhkn
    rw [unitMangoldtWeight, if_neg hpk, if_pos hd, if_neg hnd]
    ring

/-- A finite profile row commutes exactly with coherent prime-band expansion. -/
theorem finite_prime_band_row {α : Type*} (I : Finset α) (w : α → ℝ)
    (T : α → ℕ) (P : Finset ℕ) (G : ℕ → ℝ) (s : ℝ) :
    (∑ i ∈ I, w i * G (T i) * incidencePacket P (fun _ => s) (T i)) =
      s * ∑ p ∈ P, ∑ i ∈ I,
        w i * G (T i) * ((if p ∣ T i then (1 : ℝ) else 0) - 1 / p) := by
  simp only [incidencePacket, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  exact sum_congr rfl fun i _ => by ring

#print axioms positive_literal_incidence_split
#print axioms negative_literal_incidence_split
#print axioms finite_prime_band_row

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
