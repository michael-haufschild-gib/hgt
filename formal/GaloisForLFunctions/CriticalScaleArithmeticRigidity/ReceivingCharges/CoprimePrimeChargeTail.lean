import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceProductEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedConductorDilationRows
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeMoments
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeDilationRow

/-!
# Exact transport of the receiving tail to a coprime fibre

The completed tail obeys the same product rule as the prime generator.
Its two terms are the prime tail multiplied by the receiving mode and
the prime input multiplied by the fixed mode's own tail. The latter tail
has a horizon-independent pointwise square bound.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticIntersectionTheory SelectiveMultiscaleArithmeticPositivity

/-- The unfinished upward row of one normalized conductor mode. -/
def normalizedModeDilationTail (m Y n : ℕ) : ℝ :=
  normalizedPrimeModeSource m n - ∑ k ∈ Icc 1 Y, Λ k / k *
    (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n)

theorem completedPrimeDilationTail_eq_source_sub_head (Q Y n : ℕ) (a : ℕ → ℝ) :
    completedPrimeDilationTail Q a Y n = arithmeticPrimeGenerator Q a n -
      ∑ k ∈ Icc 1 Y, Λ k / k *
        (normalizedConductorPacket Q a (k * n) - normalizedConductorPacket Q a n) := by
  rw [completedPrimeDilationTail, arithmeticPrimeGenerator_eq_jet]

/-- The completed receiving tail has an exact coprime product decomposition at every horizon. -/
theorem completedPrimeDilationTail_fibreCharge {m : ℕ} (hm : 0 < m)
    (Q Y n : ℕ) (t : ℝ) :
    completedPrimeDilationTail (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) Y n =
      normalizedRamanujanMode m n *
        completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) Y n +
      incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n *
        normalizedModeDilationTail m Y n := by
  let P := fibrePrimes m Q
  let b : ℕ → ℝ := fun _ => t / fibreScale m Q
  let F := incidencePacket P b
  let e := normalizedRamanujanMode m
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (mem_fibrePrimes.mp hp).2.1
  have hinv : ∀ p ∈ P, ∀ j, e (p * j) = e j := fun p hp j =>
    normalizedRamanujanMode_coprime_mul hm (coprime_of_mem_fibrePrimes hp).symm j
  have hedge (k : ℕ) : Λ k / k * (e (k * n) * F (k * n) - e n * F n) =
      e n * (Λ k / k * (F (k * n) - F n)) +
        F n * (Λ k / k * (e (k * n) - e n)) := by
    calc
      _ = (Λ k * (e (k * n) * F (k * n) - e n * F n)) / k := by ring
      _ = _ := by rw [incidence_product_jump hP b e hinv]; ring
  rw [completedPrimeDilationTail_eq_source_sub_head,
    completedPrimeDilationTail_eq_source_sub_head, arithmeticPrimeGenerator_fibre hm]
  simp only [normalizedConductorPacket_fibreCharge_incidence hm,
    normalizedConductorPacket_restricted_fibreCharge]
  change e n * arithmeticPrimeGenerator Q (fibreRestrict m (fibreCharge m Q t)) n +
      normalizedPrimeModeSource m n * F n -
      (∑ k ∈ Icc 1 Y, Λ k / k * (e (k * n) * F (k * n) - e n * F n)) = _
  rw [show (∑ k ∈ Icc 1 Y, Λ k / k * (e (k * n) * F (k * n) - e n * F n)) =
      e n * (∑ k ∈ Icc 1 Y, Λ k / k * (F (k * n) - F n)) +
        F n * (∑ k ∈ Icc 1 Y, Λ k / k * (e (k * n) - e n)) by
    simp only [hedge, sum_add_distrib, ← mul_sum]]
  change _ = e n * (arithmeticPrimeGenerator Q (fibreRestrict m (fibreCharge m Q t)) n -
      ∑ k ∈ Icc 1 Y, Λ k / k * (F (k * n) - F n)) +
        F n * (normalizedPrimeModeSource m n -
          ∑ k ∈ Icc 1 Y, Λ k / k * (e (k * n) - e n))
  ring

/-- Subtraction of the global harmonic pole leaves the transported tail unchanged. -/
theorem completedPrimeDilationTail_harmonicFibreCharge {m Q : ℕ}
    (hm : 0 < m) (hQ : 1 ≤ Q) (N Y n : ℕ) (t : ℝ) :
    completedPrimeDilationTail (m * Q) (harmonicFibreChargeCoefficients m Q N t) Y n =
      normalizedRamanujanMode m n *
        completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) Y n +
      incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n *
        normalizedModeDilationTail m Y n := by
  rw [harmonicFibreChargeCoefficients,
    completedPrimeDilationTail_harmonicCentered (Nat.mul_pos hm hQ),
    completedPrimeDilationTail_fibreCharge hm]

/-- The square bound for a fixed mode's incomplete upward generator. -/
theorem normalizedMode_upward_head_sq_le {m : ℕ} (hm : 0 < m) (Y n : ℕ) :
    (∑ k ∈ Icc 1 Y, Λ k / k *
      (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n)) ^ 2 ≤
        primeActivityMass m * ((m : ℝ) * (Real.log m + tameDifferent m)) := by
  let a : ℕ → ℝ := fun d => if d = m then 1 else 0
  have hpacket (j : ℕ) : normalizedConductorPacket m a j = normalizedRamanujanMode m j := by
    simp only [normalizedConductorPacket, a, ite_mul, one_mul, zero_mul,
      sum_ite_eq', if_pos (mem_Icc.mpr ⟨hm, le_rfl⟩)]
  have h := primeHead_value_sq_le m a (Icc 1 Y) n
  simp only [hpacket] at h
  exact h.trans (mul_le_mul_of_nonneg_left (normalizedMode_upward_square_le hm Y n)
    (primeActivityMass_nonneg m))

/-- A fixed mode's own receiving tail is bounded independently of cutoff and row. -/
theorem normalizedModeDilationTail_sq_le {m : ℕ} (hm : 0 < m) (Y n : ℕ) :
    normalizedModeDilationTail m Y n ^ 2 ≤
      2 * sourceBound m ^ 2 +
        2 * primeActivityMass m * ((m : ℝ) * (Real.log m + tameDifferent m)) := by
  have hS := sq_source_le hm n
  have hH := normalizedMode_upward_head_sq_le hm Y n
  have hsum := sq_nonneg (normalizedPrimeModeSource m n +
    ∑ k ∈ Icc 1 Y, Λ k / k *
      (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n))
  unfold normalizedModeDilationTail
  nlinarith only [hS, hH, hsum]

#print axioms completedPrimeDilationTail_fibreCharge
#print axioms completedPrimeDilationTail_harmonicFibreCharge
#print axioms normalizedModeDilationTail_sq_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
