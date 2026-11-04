import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibrePackets
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeScales

/-!
# Moments of finite simultaneous receiving vectors

The finite base-mode sum is bounded independently of the prime cutoff.
Factoring out its common incidence packet preserves the reciprocal-prime
moment gain before and after exact harmonic centering.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

/-- A fixed bound for the finite receiving-mode combination. -/
def commonPrimeFibreModeBound (S : Finset ℕ) (t : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, |t m| * modeBound m

theorem commonPrimeFibreModeBound_nonneg (S : Finset ℕ) (t : ℕ → ℝ) :
    0 ≤ commonPrimeFibreModeBound S t := by
  unfold commonPrimeFibreModeBound modeBound
  positivity

/-- The common prime profile factors out of the entire receiving vector. -/
theorem commonPrimeFibreProfile_factor (S : Finset ℕ) (M Q : ℕ) (t : ℕ → ℝ) (n : ℕ) :
    commonPrimeFibreProfile S M Q t n =
      (∑ m ∈ S, t m * normalizedRamanujanMode m n) *
        incidencePacket (fibrePrimes M Q) (fun _ => 1 / fibreScale M Q) n := by
  rw [commonPrimeFibreProfile, sum_mul]
  apply sum_congr rfl
  intro m _
  simp only [incidencePacket_const_eq_count]
  ring

/-- The finite mode factor is bounded by the sum of its individual period bounds. -/
theorem abs_commonPrimeFibre_mode_le (S : Finset ℕ)
    (hS : ∀ m ∈ S, 0 < m) (t : ℕ → ℝ) (n : ℕ) :
    |∑ m ∈ S, t m * normalizedRamanujanMode m n| ≤ commonPrimeFibreModeBound S t := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro m hm
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_le_periodSum (hS m hm) (normalizedRamanujanMode_periodic (hS m hm)) n)
    (abs_nonneg _)

/-- One finite receiving-vector constant multiplies the scalar incidence moment. -/
def commonPrimeFibreMoment (S : Finset ℕ) (M Q : ℕ) (t : ℕ → ℝ) : ℝ :=
  commonPrimeFibreModeBound S t ^ 2 * (1 / fibreScale M Q) ^ 2 *
    (4 * (∑ p ∈ fibrePrimes M Q, 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ fibrePrimes M Q, 1 / (p : ℝ))

theorem commonPrimeFibreMoment_nonneg (S : Finset ℕ) (M Q : ℕ) (t : ℕ → ℝ) :
    0 ≤ commonPrimeFibreMoment S M Q t := by
  unfold commonPrimeFibreMoment
  positivity

/-- Both finite-horizon moments retain the scalar reciprocal-prime bound. -/
theorem commonPrimeFibre_raw_moments (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m)
    (M Q N : ℕ) (t : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, commonPrimeFibreProfile S M Q t n ^ 2) ≤
        (N : ℝ) * commonPrimeFibreMoment S M Q t ∧
    (∑ n ∈ Icc 1 N, commonPrimeFibreProfile S M Q t n ^ 2 / (n : ℝ)) ≤
        harmonicMass N * commonPrimeFibreMoment S M Q t := by
  have hP : ∀ p ∈ fibrePrimes M Q, p.Prime := fun p hp => (mem_fibrePrimes.mp hp).2.1
  have hpoint (n : ℕ) : commonPrimeFibreProfile S M Q t n ^ 2 ≤
      commonPrimeFibreModeBound S t ^ 2 *
        incidencePacket (fibrePrimes M Q) (fun _ => 1 / fibreScale M Q) n ^ 2 := by
    rw [commonPrimeFibreProfile_factor, mul_pow]
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_commonPrimeFibre_mode_le S hS t n) 2
    rw [sq_abs] at h
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
  constructor
  · calc
      _ ≤ commonPrimeFibreModeBound S t ^ 2 * ∑ n ∈ Icc 1 N,
          incidencePacket (fibrePrimes M Q) (fun _ => 1 / fibreScale M Q) n ^ 2 := by
        rw [mul_sum]
        exact sum_le_sum fun n _ => hpoint n
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (incidencePacket_const_ordinary_square_le hP (1 / fibreScale M Q) N)
        (sq_nonneg _)).trans_eq (by unfold commonPrimeFibreMoment; ring)
  · calc
      _ ≤ commonPrimeFibreModeBound S t ^ 2 * ∑ n ∈ Icc 1 N,
          incidencePacket (fibrePrimes M Q) (fun _ => 1 / fibreScale M Q) n ^ 2 / (n : ℝ) := by
        rw [mul_sum]
        exact sum_le_sum fun n _ =>
          (div_le_div_of_nonneg_right (hpoint n) (Nat.cast_nonneg n)).trans_eq (by ring)
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (incidencePacket_const_harmonic_square_le hP (1 / fibreScale M Q) N)
        (sq_nonneg _)).trans_eq (by unfold commonPrimeFibreMoment; ring)

/-- Exact global centering preserves the moment gain for the whole receiving vector. -/
theorem commonPrimeFibre_centered_moments {M Q N : ℕ}
    (hM : 0 < M) (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (t : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, normalizedConductorPacket (M * Q)
      (commonPrimeFibreCoefficients S M Q N t) n ^ 2) ≤
        4 * (N : ℝ) * commonPrimeFibreMoment S M Q t ∧
    (∑ n ∈ Icc 1 N, normalizedConductorPacket (M * Q)
      (commonPrimeFibreCoefficients S M Q N t) n ^ 2 / (n : ℝ)) ≤
        harmonicMass N * commonPrimeFibreMoment S M Q t := by
  have hzero := commonPrimeFibre_neutral hM hQ hN S t
  simp only [SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile, div_div,
    Real.mul_self_sqrt (Nat.cast_nonneg _), commonPrimeFibre_packet_formula hM hQ S hS] at hzero
  simp only [commonPrimeFibre_packet_formula hM hQ S hS]
  exact harmonic_centered_two_moments hN (commonPrimeFibreProfile S M Q t) _ _ hzero
    (commonPrimeFibre_raw_moments S (fun m hm => (hS m hm).1) M Q N t).1
    (commonPrimeFibre_raw_moments S (fun m hm => (hS m hm).1) M Q N t).2

/-- Every fixed finite receiving vector absorbs the critical sublogarithmic moment costs. -/
theorem tendsto_commonPrimeFibreMoment_cost {M : ℕ} (hM : 0 < M)
    (S : Finset ℕ) (t : ℕ → ℝ) {a d : ℕ} (ha : 0 < a) (had : a ≤ d)
    {r : ℝ} (hr : r < 1) :
    Tendsto (fun X : ℕ => Real.log (X ^ d : ℕ) ^ r * (Real.log (X ^ d : ℕ) + 1) *
      commonPrimeFibreMoment S M (X ^ a) t) atTop (𝓝 0) := by
  have h := (tendsto_fibreIncidencePolynomialMoment_cost hM ha had (1 : ℝ) hr).const_mul
    (commonPrimeFibreModeBound S t ^ 2)
  simp only [mul_zero] at h
  convert h using 1
  funext X
  unfold commonPrimeFibreMoment
  ring

#print axioms commonPrimeFibre_raw_moments
#print axioms commonPrimeFibre_centered_moments
#print axioms tendsto_commonPrimeFibreMoment_cost

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
