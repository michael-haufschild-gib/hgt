import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeMoments
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.FibreChargesSurviveVanishingEnergy

/-!
# Ordinary and harmonic moments in fixed receiving fibres

A coherent fibre is a bounded Ramanujan mode times a prime-divisor count
minus its complete-period mean. Its ordinary and harmonic squares have
the same reciprocal-prime moment cost as the scalar receiving packet.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity
open _root_.RHTower.Sieve

/-- Every positive conductor has a positive period bound, already detected at residue zero. -/
theorem modeBound_pos {m : ℕ} (hm : 0 < m) : 0 < modeBound m := by
  have hphi : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hzero : 0 < normalizedRamanujanMode m 0 := by
    rw [normalizedRamanujanMode_eq_coefficient hm,
      BezoutValuationIncidence.ramanujanLagCoefficient_of_dvd (dvd_zero m)]
    exact div_pos hphi (Real.sqrt_pos.mpr hphi)
  exact (lt_of_lt_of_le hzero (le_abs_self _)).trans_le
    (single_le_sum (fun j _ => abs_nonneg (normalizedRamanujanMode m j)) (mem_range.mpr hm))

/-- A coherent incidence packet is a centered prime-divisor count. -/
theorem incidencePacket_const_eq_count (P : Finset ℕ) (s : ℝ) (n : ℕ) :
    incidencePacket P (fun _ => s) n =
      s * (primeDivisorCount P n - ∑ p ∈ P, 1 / (p : ℝ)) := by
  simp only [incidencePacket, primeDivisorCount, mul_sub, mul_sum, sum_sub_distrib]

/-- The complete-period centering also has a small ordinary square. -/
theorem incidencePacket_const_ordinary_square_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, incidencePacket P (fun _ => s) n ^ 2) ≤
      s ^ 2 * (N : ℝ) *
        (4 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + 2 * ∑ p ∈ P, 1 / (p : ℝ)) := by
  simp only [incidencePacket_const_eq_count, mul_pow, ← mul_sum]
  have hcount : (∑ n ∈ Icc 1 N,
      (primeDivisorCount P n - ∑ p ∈ P, 1 / (p : ℝ)) ^ 2) ≤
      (N : ℝ) * (4 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + 2 * ∑ p ∈ P, 1 / (p : ℝ)) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N,
          (2 * primeDivisorCount P n ^ 2 + 2 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2) := by
        apply sum_le_sum
        intro n _
        nlinarith only [sq_nonneg (primeDivisorCount P n + ∑ p ∈ P, 1 / (p : ℝ))]
      _ = 2 * (∑ n ∈ Icc 1 N, primeDivisorCount P n ^ 2) +
          (N : ℝ) * (2 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2) := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc,
          Nat.add_sub_cancel, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        have h := primeDivisorCount_second_moment_le hP N
        linarith only [h]
  exact (mul_le_mul_of_nonneg_left hcount (sq_nonneg s)).trans_eq (by ring)

/-- Harmonic square obeys the identical reciprocal-prime moment bound. -/
theorem incidencePacket_const_harmonic_square_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, incidencePacket P (fun _ => s) n ^ 2 / (n : ℝ)) ≤
      s ^ 2 * harmonicMass N *
        (4 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + 2 * ∑ p ∈ P, 1 / (p : ℝ)) := by
  simp only [incidencePacket_const_eq_count, mul_pow, mul_div_assoc, ← mul_sum]
  have hcount : (∑ n ∈ Icc 1 N,
      (primeDivisorCount P n - ∑ p ∈ P, 1 / (p : ℝ)) ^ 2 / (n : ℝ)) ≤
      harmonicMass N * (4 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + 2 * ∑ p ∈ P, 1 / (p : ℝ)) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N,
          (2 * primeDivisorCount P n ^ 2 + 2 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2) / (n : ℝ) := by
        apply sum_le_sum
        intro n _
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        nlinarith only [sq_nonneg (primeDivisorCount P n + ∑ p ∈ P, 1 / (p : ℝ))]
      _ = 2 * (∑ n ∈ Icc 1 N, primeDivisorCount P n ^ 2 / (n : ℝ)) +
          2 * harmonicMass N * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 := by
        simp only [add_div, mul_div_assoc, sum_add_distrib, ← mul_sum]
        rw [harmonicMass, mul_assoc, sum_mul]
        congr 1
        congr 1
        exact sum_congr rfl fun n _ => by ring
      _ ≤ _ := by
        have h := primeDivisorCount_harmonic_second_moment_le hP N
        linarith only [h]
  exact (mul_le_mul_of_nonneg_left hcount (sq_nonneg s)).trans_eq (by ring)

/-- Removing the primes dividing the receiving conductor restricts the incidence sum exactly. -/
theorem normalizedConductorPacket_restricted_fibreCharge (m Q : ℕ) (t : ℝ) (n : ℕ) :
    normalizedConductorPacket Q (fibreRestrict m (fibreCharge m Q t)) n =
      incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n := by
  rw [normalizedConductorPacket, sum_fibreRestrict]
  apply sum_congr rfl
  intro p hp
  rw [fibreCharge, mul_assoc, primePoleWitness_mul_mode (mem_fibrePrimes.mp hp).2.1]

/-- The literal coherent conductor fibre is the bounded mode times its incidence packet. -/
theorem normalizedConductorPacket_fibreCharge_incidence {m : ℕ} (hm : 0 < m)
    (Q : ℕ) (t : ℝ) (n : ℕ) :
    normalizedConductorPacket (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) n =
      normalizedRamanujanMode m n *
        incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n := by
  rw [normalizedConductorPacket_fibre hm, normalizedConductorPacket_restricted_fibreCharge]

/-- The single finite moment cost for a fixed coherent fibre. -/
def fibreChargeMoment (m Q : ℕ) (t : ℝ) : ℝ :=
  modeBound m ^ 2 * (t / fibreScale m Q) ^ 2 *
    (4 * (∑ p ∈ fibrePrimes m Q, 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ fibrePrimes m Q, 1 / (p : ℝ))

theorem fibreChargeMoment_nonneg (m Q : ℕ) (t : ℝ) : 0 ≤ fibreChargeMoment m Q t := by
  unfold fibreChargeMoment
  positivity

/-- Both raw moments retain the reciprocal-prime gain after multiplication by a fixed conductor. -/
theorem fibreCharge_raw_moments {m : ℕ} (hm : 0 < m) (Q N : ℕ) (t : ℝ) :
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) n ^ 2) ≤
        (N : ℝ) * fibreChargeMoment m Q t ∧
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) n ^ 2 / (n : ℝ)) ≤
        harmonicMass N * fibreChargeMoment m Q t := by
  have hP : ∀ p ∈ fibrePrimes m Q, p.Prime := fun p hp => (mem_fibrePrimes.mp hp).2.1
  have hpoint (n : ℕ) :
      normalizedConductorPacket (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) n ^ 2 ≤
        modeBound m ^ 2 * incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n ^ 2 := by
    rw [normalizedConductorPacket_fibreCharge_incidence hm, mul_pow]
    exact mul_le_mul_of_nonneg_right (sq_mode_le hm n) (sq_nonneg _)
  constructor
  · calc
      _ ≤ modeBound m ^ 2 * ∑ n ∈ Icc 1 N,
          incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n ^ 2 := by
        rw [mul_sum]
        exact sum_le_sum fun n _ => hpoint n
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (incidencePacket_const_ordinary_square_le hP (t / fibreScale m Q) N)
        (sq_nonneg _)).trans_eq (by unfold fibreChargeMoment; ring)
  · calc
      _ ≤ modeBound m ^ 2 * ∑ n ∈ Icc 1 N,
          incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n ^ 2 / (n : ℝ) := by
        rw [mul_sum]
        exact sum_le_sum fun n _ =>
          (div_le_div_of_nonneg_right (hpoint n) (Nat.cast_nonneg n)).trans_eq (by ring)
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (incidencePacket_const_harmonic_square_le hP (t / fibreScale m Q) N)
        (sq_nonneg _)).trans_eq (by unfold fibreChargeMoment; ring)

/-- Harmonic centering preserves harmonic square and costs at most four in ordinary square. -/
theorem harmonic_centered_two_moments {N : ℕ} (hN : 1 ≤ N) (F : ℕ → ℝ) (μ V : ℝ)
    (hzero : ∑ n ∈ Icc 1 N, (F n - μ) / (n : ℝ) = 0)
    (hO : (∑ n ∈ Icc 1 N, F n ^ 2) ≤ (N : ℝ) * V)
    (hH : (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) ≤ harmonicMass N * V) :
    (∑ n ∈ Icc 1 N, (F n - μ) ^ 2) ≤ 4 * (N : ℝ) * V ∧
    (∑ n ∈ Icc 1 N, (F n - μ) ^ 2 / (n : ℝ)) ≤ harmonicMass N * V := by
  have hmean : (∑ n ∈ Icc 1 N, F n / (n : ℝ)) = μ * harmonicMass N := by
    have he : (∑ n ∈ Icc 1 N, (F n - μ) / (n : ℝ)) =
        (∑ n ∈ Icc 1 N, F n / (n : ℝ)) - μ * harmonicMass N := by
      simp only [harmonicMass, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [he] at hzero
    exact sub_eq_zero.mp hzero
  have hvar : (∑ n ∈ Icc 1 N, (F n - μ) ^ 2 / (n : ℝ)) =
      (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) - μ ^ 2 * harmonicMass N := by
    calc
      _ = (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) -
          2 * μ * (∑ n ∈ Icc 1 N, F n / (n : ℝ)) + μ ^ 2 * harmonicMass N := by
        simp only [harmonicMass, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [hmean]; ring
  have hnonneg : 0 ≤ ∑ n ∈ Icc 1 N, (F n - μ) ^ 2 / (n : ℝ) :=
    sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hμ : μ ^ 2 ≤ V := by
    have hh : μ ^ 2 * harmonicMass N ≤ V * harmonicMass N := by
      rw [hvar] at hnonneg
      nlinarith only [hnonneg, hH]
    exact (mul_le_mul_iff_left₀ (harmonicMass_pos hN)).mp (by
      simpa only [mul_comm] using hh)
  constructor
  · calc
      _ ≤ ∑ n ∈ Icc 1 N, (2 * F n ^ 2 + 2 * μ ^ 2) := by
        apply sum_le_sum
        intro n _
        nlinarith only [sq_nonneg (F n + μ)]
      _ = 2 * (∑ n ∈ Icc 1 N, F n ^ 2) + (N : ℝ) * (2 * μ ^ 2) := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc,
          Nat.add_sub_cancel, nsmul_eq_mul]
        ring
      _ ≤ 2 * ((N : ℝ) * V) + (N : ℝ) * (2 * V) :=
        add_le_add (mul_le_mul_of_nonneg_left hO zero_le_two)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμ zero_le_two) (Nat.cast_nonneg N))
      _ = _ := by ring
  · rw [hvar]
    exact (sub_le_self _ (mul_nonneg (sq_nonneg μ) (harmonicMass_pos hN).le)).trans hH

/-- Literal harmonic-pole-neutral coherent coefficients on the fibre of `m`. -/
def harmonicFibreChargeCoefficients (m Q N : ℕ) (t : ℝ) : ℕ → ℝ :=
  harmonicCenteredCoefficients (m * Q) N (fibreCoefficients m Q (fibreCharge m Q t))

/-- Global pole removal leaves both fibre moments small. -/
theorem harmonicFibreCharge_moments {m Q N : ℕ} (hm : 0 < m) (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    (t : ℝ) :
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t) n ^ 2) ≤
        4 * (N : ℝ) * fibreChargeMoment m Q t ∧
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t) n ^ 2 / (n : ℝ)) ≤
        harmonicMass N * fibreChargeMoment m Q t := by
  let a := fibreCoefficients m Q (fibreCharge m Q t)
  let μ := harmonicSum N (conductorHorizonProfile (m * Q) a) / harmonicMass N
  have hmQ : 1 ≤ m * Q := Nat.mul_pos hm hQ
  have he (n : ℕ) : normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t) n =
      normalizedConductorPacket (m * Q) a n - μ := by
    rw [harmonicFibreChargeCoefficients, harmonicCenteredCoefficients,
      normalizedConductorPacket_addConstantConductor hmQ]
    rfl
  have hz : ∑ n ∈ Icc 1 N, (normalizedConductorPacket (m * Q) a n - μ) / (n : ℝ) = 0 := by
    have h := harmonicSum_centeredCoefficients hmQ hN a
    have hz' : ∑ n ∈ Icc 1 N,
        normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t) n / (n : ℝ) = 0 := by
      simpa only [harmonicFibreChargeCoefficients, a,
        SelectiveMultiscaleArithmeticPositivity.harmonicSum,
        conductorHorizonProfile, div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)] using h
    simpa only [he] using hz'
  simp only [he]
  exact harmonic_centered_two_moments hN (normalizedConductorPacket (m * Q) a) μ
    (fibreChargeMoment m Q t) hz (fibreCharge_raw_moments hm Q N t).1
    (fibreCharge_raw_moments hm Q N t).2

#print axioms incidencePacket_const_harmonic_square_le
#print axioms normalizedConductorPacket_fibreCharge_incidence
#print axioms fibreCharge_raw_moments
#print axioms harmonicFibreCharge_moments

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
