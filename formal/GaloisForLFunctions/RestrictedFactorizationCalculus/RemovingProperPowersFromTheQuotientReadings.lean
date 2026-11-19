import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RestrictedFactorizationCalculus.CenteringThePrimePowerReadingsAtTheirQuotientFloors

/-!
# Ordinary primes at the quotient endpoints

Transposing the deleted proper prime powers gives smaller unweighted
Möbius prefixes, all with the original frozen cutoff. The cofactor
floor and the integer smooth main term are preserved exactly.
-/

noncomputable section

open Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

open RoughReading

/-- Chebyshev weight of the ordinary primes strictly above the fixed cutoff. -/
def ordinaryPrimeReading (y t : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE t).filter (y<·),Real.log p

/-- The ordinary-prime reading centered at its exact quotient floor. -/
def centeredOrdinaryPrimeRemainder (y X : ℕ) : ℝ :=
  ∑ m ∈ freeSet y (X/y),row y m*
    (ordinaryPrimeReading y (X/m)-(y:ℝ)*(⌊((X:ℝ)/y)/m⌋:ℝ))

/-- The Mangoldt kernel on surviving proper powers. -/
def roughProperPowerWeight (y d : ℕ) : ℝ :=
  if 1<d ∧ y<d ∧ ¬ d.Prime ∧ IsFree (banned y) d then vonMangoldt d else 0

private theorem split_reading (y t : ℕ) :
    roughPrimePowerReading y t-ordinaryPrimeReading y t=
      ∑ d ∈ Icc 1 t,roughProperPowerWeight y d := by
  have seteq : (Nat.primesLE t).filter (y<·)=(Icc 1 t).filter (fun d => d.Prime ∧ y<d) := by
    ext d
    simp only [mem_filter,Nat.mem_primesLE,mem_Icc]
    exact ⟨fun ⟨⟨dt,hp⟩,dy⟩ => ⟨⟨hp.pos,dt⟩,hp,dy⟩,fun ⟨hi,hp,dy⟩ => ⟨⟨hi.2,hp⟩,dy⟩⟩
  rw [roughPrimePowerReading,freeSet,ordinaryPrimeReading,seteq,sum_filter,sum_filter,←sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  by_cases hp : d.Prime
  · have good : IsFree (banned y) d ↔ y<d := by
      simpa only [banned,Set.mem_setOf_eq,not_le] using isFree_prime (banned y) hp
    simp [roughProperPowerWeight,hp,good,vonMangoldt_apply_prime hp]
  by_cases good : IsFree (banned y) d
  · by_cases one : d=1
    · subst d; simp [roughProperPowerWeight]
    have pos := (mem_Icc.mp hd).1
    have minp : d.minFac ∈ d.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime one,Nat.minFac_dvd _,good.1⟩
    have high : y<d := (lt_of_not_ge (good.2 _ minp)).trans_le (Nat.le_of_dvd pos (Nat.minFac_dvd _))
    simp [roughProperPowerWeight,hp,good,high,show 1<d by omega]
  · simp [roughProperPowerWeight,hp,good]

/-- The difference of the two centered readings is an exact sum of
smaller frozen rows indexed by the omitted proper powers. -/
theorem proper_powers_as_smaller_frozen_rows {y : ℕ} (hy : 0<y) (X : ℕ) :
    centeredPrimePowerRemainder y X-centeredOrdinaryPrimeRemainder y X=
      ∑ d ∈ Icc 1 X,roughProperPowerWeight y d*coprimeMoebiusSum (primorial y) (X/d) := by
  let F := fun m d : ℕ => row y m*roughProperPowerWeight y d
  have each (m : ℕ) : row y m*
      (roughPrimePowerReading y (X/m)-(y:ℝ)*(⌊((X:ℝ)/y)/m⌋:ℝ))-
      row y m*(ordinaryPrimeReading y (X/m)-(y:ℝ)*(⌊((X:ℝ)/y)/m⌋:ℝ))=
      ∑ d ∈ Icc 1 (X/m),F m d := by
    rw [←mul_sub,sub_sub_sub_cancel_right,split_reading,mul_sum]
  have extend : (∑ m ∈ freeSet y (X/y),∑ d ∈ Icc 1 (X/m),F m d)=
      ∑ m ∈ Icc 1 X,∑ d ∈ Icc 1 (X/m),F m d := by
    apply sum_subset ((filter_subset ..).trans (Icc_subset_Icc_right (Nat.div_le_self ..)))
    intro m hm outside
    have mp := (mem_Icc.mp hm).1
    by_cases past : X/y < m
    · have product := (Nat.div_lt_iff_lt_mul hy).mp past
      have bound : X/m<y := (Nat.div_lt_iff_lt_mul mp).mpr (by simpa only [Nat.mul_comm] using product)
      apply sum_eq_zero
      intro d hd
      simp [F,roughProperPowerWeight,show ¬y<d from (not_lt.mpr ((mem_Icc.mp hd).2.trans bound.le))]
    · have bad : ¬IsFree (banned y) m := fun h => outside (mem_filter.mpr ⟨mem_Icc.mpr
          ⟨mp,le_of_not_gt past⟩,h⟩)
      simp [F,row_value,bad]
  rw [centeredPrimePowerRemainder,centeredOrdinaryPrimeRemainder,←sum_sub_distrib,
    sum_congr rfl (fun m _ => each m),extend,RHTower.sum_hyperbola_swap_real X F]
  apply sum_congr rfl
  intro d _
  rw [coprimeMoebiusSum,mul_sum]
  apply sum_congr rfl
  intro m hm
  change row y m*roughProperPowerWeight y d=_
  rw [primorial_indicator_eq_deleted_mobius y m (mem_Icc.mp hm).1,mul_comm]

/-- Exact logarithmic identity with the ordinary-prime reading, the
full smooth population, and the delayed proper-power correction. -/
theorem exact_centered_ordinary_prime_reading {y : ℕ} (hy : 0<y) (X : ℕ) :
    (∑ n ∈ Icc 1 X,row y n*Real.log n)+centeredOrdinaryPrimeRemainder y X+
      (∑ d ∈ Icc 1 X,roughProperPowerWeight y d*coprimeMoebiusSum (primorial y) (X/d))=
      -(y:ℝ)*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)).card := by
  linarith only [proper_powers_as_smaller_frozen_rows hy X,exact_centered_prime_power_remainder hy X]

#print axioms exact_centered_ordinary_prime_reading
#print axioms proper_powers_as_smaller_frozen_rows

end GaloisForLFunctions.RestrictedFactorizationCalculus
