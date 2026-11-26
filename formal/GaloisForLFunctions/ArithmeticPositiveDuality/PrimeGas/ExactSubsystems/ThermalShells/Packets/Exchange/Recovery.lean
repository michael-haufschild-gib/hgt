import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange.Gibbs

/-! # Recovering prime collision probability from exchange measurements -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange

open Finset Real

def probability (S : Finset Nat.Primes) (b : ℝ) (p : Nat.Primes) := atom b p/singleZ S b

def collision (S : Finset Nat.Primes) (b : ℝ) := ∑ p ∈ S,probability S b p^2

def fraction (S : Finset Nat.Primes) (squares : Bool) (b : ℝ) := sectorZ S squares b/singleZ S b^2

def share (S H : Finset Nat.Primes) (b : ℝ) := markedZ S H b/singleZ S b

theorem collision_eq (S : Finset Nat.Primes) (b : ℝ) :
    collision S b = singleZ S (2*b)/singleZ S b^2 := by
  simp only [collision,probability,div_pow,← sum_div,← doubled_atom,singleZ]

theorem share_eq (S H : Finset Nat.Primes) (b : ℝ) :
    share S H b = ∑ p ∈ S,probability S b p*hit H p := by
  simp only [share,markedZ,firstMoment,probability,div_mul_eq_mul_div₀,sum_div]

/-- The difference of physical sector partitions, relative to the labeled partition, is
exactly the probability of a repeated prime in two independent draws. -/
theorem collision_from_partitions (S : Finset Nat.Primes) (b : ℝ) :
    fraction S true b - fraction S false b = collision S b := by
  rw [fraction,fraction,← sub_div,(partition_traces S b).2,collision_eq]

theorem partition_fractions {S : Finset Nat.Primes} (hs : S.Nonempty) (b : ℝ) :
    2*fraction S true b = 1+collision S b ∧ 2*fraction S false b = 1-collision S b := by
  have add : fraction S true b+fraction S false b=1 := by
    rw [fraction,fraction,← add_div,(partition_traces S b).1,div_self (pow_ne_zero _ (singleZ_pos hs b).ne')]
  have sub := collision_from_partitions S b
  constructor <;> linarith only [add,sub]

private theorem weighted_fraction (S H : Finset Nat.Primes) (squares : Bool) (b : ℝ) :
    fraction S squares b*sectorMean S H squares b = moment S H squares b/singleZ S b^2 := by
  rw [fraction,div_mul_eq_mul_div₀,weighted_mean]

/-- The sector mixture recovers the labeled mean. Its signed counterpart reads the
marked prime at doubled damping, weighted by the collision probability. -/
theorem marked_readings {S : Finset Nat.Primes} (hs : S.Nonempty) (H : Finset Nat.Primes) (b : ℝ) :
    (1-collision S b)*sectorMean S H false b + (1+collision S b)*sectorMean S H true b = 4*share S H b ∧
    (1+collision S b)*sectorMean S H true b - (1-collision S b)*sectorMean S H false b =
      4*collision S b*share S H (2*b) := by
  have h := partition_fractions hs b
  have t := moment_traces S H b
  have z := (singleZ_pos hs b).ne'
  have z₂ := (singleZ_pos hs (2*b)).ne'
  rw [← h.1,← h.2]
  constructor
  · rw [mul_assoc,mul_assoc,weighted_fraction,weighted_fraction,← mul_add,← add_div,
      add_comm (moment S H false b),t.1,share]
    field_simp [z]
    ring
  · rw [mul_assoc,mul_assoc,weighted_fraction,weighted_fraction,← mul_sub,← sub_div,t.2,share,collision_eq]
    field_simp [z,z₂]
    ring

/-- Unequal sector means identify collision probability from three occupation readings. -/
theorem collision_from_means {S : Finset Nat.Primes} (hs : S.Nonempty) (H : Finset Nat.Primes) (b : ℝ)
    (hne : sectorMean S H false b ≠ sectorMean S H true b) :
    collision S b = (sectorMean S H false b + sectorMean S H true b-4*share S H b)/
      (sectorMean S H false b-sectorMean S H true b) := by
  apply (eq_div_iff (sub_ne_zero.mpr hne)).mpr
  linear_combination -(marked_readings hs H b).1

#print axioms collision_from_partitions
#print axioms partition_fractions
#print axioms marked_readings
#print axioms collision_from_means

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange
