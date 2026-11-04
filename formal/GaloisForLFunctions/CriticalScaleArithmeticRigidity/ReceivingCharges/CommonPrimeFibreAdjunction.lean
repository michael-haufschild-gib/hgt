import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibrePackets

/-!
# Vanishing adjunction of simultaneous receiving charges

One common prime exclusion preserves the sharp prime witness identity.
Each fixed base conductor contributes a fixed multiplier, and finite sums
retain a bound proportional to the reciprocal common prime Mertens mass.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticIntersectionTheory SelectiveMultiscaleArithmeticPositivity

/-- A common prime restriction preserves the fixed-conductor adjunction bound. -/
theorem primeAdjunctionMass_commonPrimeFibre_le {M m Q : ℕ}
    (hM : 0 < M) (hm : 0 < m) (hmM : m ∣ M) (t : ℝ) (hB : 0 < fibreScale M Q) :
    primeAdjunctionMass (M * Q)
      (primeFibreIncidenceCoefficients (fibrePrimes M Q) m (fun _ => t / fibreScale M Q)) ≤
        (2 * (Real.log m + tameDifferent m) + 1) * (t ^ 2 / fibreScale M Q) := by
  have hP : ∀ p ∈ fibrePrimes M Q, 0 < p ∧ m * p ≤ M * Q := by
    intro p hp
    exact ⟨(mem_fibrePrimes.mp hp).2.1.pos,
      Nat.mul_le_mul (Nat.le_of_dvd hM hmM) (mem_Icc.mp (mem_fibrePrimes.mp hp).1).2⟩
  rw [primeAdjunctionMass, sum_primeFibreIncidenceCoefficients hm (fibrePrimes M Q)
    (fun _ => t / fibreScale M Q) hP (fun c x => (Real.log c + tameDifferent c) * x ^ 2)
    (fun _ => by simp only [zero_pow two_ne_zero, mul_zero])]
  have hw : 0 ≤ Real.log m + tameDifferent m :=
    add_nonneg (Real.log_natCast_nonneg m) (tameDifferent_nonneg m)
  have hterm (p : ℕ) (hp : p ∈ fibrePrimes M Q) :
      (Real.log (m * p : ℕ) + tameDifferent (m * p)) *
        (t / fibreScale M Q * primePoleWitness p) ^ 2 ≤
      (2 * (Real.log m + tameDifferent m) + 1) *
        (t / fibreScale M Q) ^ 2 * (Real.log p / p) := by
    have hpP := (mem_fibrePrimes.mp hp).2.1
    have hmp : m.Coprime p := Nat.coprime_comm.mp
      (hpP.coprime_iff_not_dvd.mpr (fun h => (mem_fibrePrimes.mp hp).2.2 (h.trans hmM)))
    have he : (Real.log (m * p : ℕ) + tameDifferent (m * p)) *
        (t / fibreScale M Q * primePoleWitness p) ^ 2 =
      ((Real.log m + tameDifferent m) * (t / fibreScale M Q) ^ 2) * primePoleWitness p ^ 2 +
        (t / fibreScale M Q) ^ 2 * (Real.log p / p) := by
      rw [adjunctionWeight_mul_of_coprime hm hpP.pos hmp, mul_pow,
        ← adjunctionWeight_mul_witness_sq hpP]
      ring
    rw [he]
    exact (add_le_add
      (mul_le_mul_of_nonneg_left (witness_sq_le hpP) (mul_nonneg hw (sq_nonneg _)))
      le_rfl).trans_eq (by ring)
  refine (sum_le_sum hterm).trans_eq ?_
  rw [← mul_sum]
  change (2 * (Real.log m + tameDifferent m) + 1) *
    (t / fibreScale M Q) ^ 2 * fibreScale M Q = _
  field_simp [hB.ne']

/-- A finite coefficient sum costs at most its number of summands in adjunction square. -/
theorem commonFibre_adjunction_sum_le {ι : Type*} (S : Finset ι) (a : ι → ℕ → ℝ) (R : ℕ) :
    primeAdjunctionMass R (fun c => ∑ i ∈ S, a i c) ≤
      (S.card : ℝ) * ∑ i ∈ S, primeAdjunctionMass R (a i) := by
  have hpoint (c : ℕ) : (∑ i ∈ S, a i c) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, a i c ^ 2 := by
    simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using
      sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => a i c)
  simp only [primeAdjunctionMass]
  calc
    _ ≤ ∑ c ∈ Icc 1 R, (Real.log c + tameDifferent c) *
        ((S.card : ℝ) * ∑ i ∈ S, a i c ^ 2) :=
      sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hpoint c)
        (add_nonneg (Real.log_natCast_nonneg c) (tameDifferent_nonneg c))
    _ = _ := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      exact sum_congr rfl fun c _ => by ring

/-- The prescribed finite receiving vector has an explicit vanishing adjunction cost. -/
theorem commonPrimeFibre_adjunction_le {M Q : ℕ} (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M)
    (N : ℕ) (t : ℕ → ℝ) (hB : 0 < fibreScale M Q) :
    primeAdjunctionMass (M * Q) (commonPrimeFibreCoefficients S M Q N t) ≤
      (S.card : ℝ) *
        (∑ m ∈ S, (2 * (Real.log m + tameDifferent m) + 1) * t m ^ 2) / fibreScale M Q := by
  rw [commonPrimeFibreCoefficients, primeAdjunctionMass_harmonicCentered]
  refine (commonFibre_adjunction_sum_le S _ (M * Q)).trans ?_
  have h := mul_le_mul_of_nonneg_left
    (sum_le_sum fun m hm => primeAdjunctionMass_commonPrimeFibre_le hM
      (hS m hm).1 (hS m hm).2 (t m) hB) (Nat.cast_nonneg S.card)
  exact h.trans_eq (by simp only [div_eq_mul_inv, sum_mul, mul_assoc])

/-- Simultaneous exact receiving coordinates survive adjunction tending to zero. -/
theorem tendsto_commonPrimeFibre_adjunction {M : ℕ} (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (t : ℕ → ℝ)
    {a : ℕ} (ha : 0 < a) (d : ℕ) :
    Tendsto (fun X : ℕ => primeAdjunctionMass (M * X ^ a)
      (commonPrimeFibreCoefficients S M (X ^ a) (X ^ d) t)) atTop (𝓝 0) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hB := (fibreScale_tendsto_atTop hM).comp hXa
  have hlim := hB.const_div_atTop ((S.card : ℝ) *
    (∑ m ∈ S, (2 * (Real.log m + tameDifferent m) + 1) * t m ^ 2))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hB.eventually (eventually_gt_atTop 0)] with X hb
  rw [Real.norm_eq_abs, abs_of_nonneg (primeAdjunctionMass_nonneg _ _)]
  exact commonPrimeFibre_adjunction_le hM S hS (X ^ d) t hb

#print axioms primeAdjunctionMass_commonPrimeFibre_le
#print axioms commonPrimeFibre_adjunction_le
#print axioms tendsto_commonPrimeFibre_adjunction

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
