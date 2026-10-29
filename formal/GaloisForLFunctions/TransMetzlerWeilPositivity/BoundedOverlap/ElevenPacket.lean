import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.PrimeSquareTrial
import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.VariablePacketLimit
import GaloisForLFunctions.TransMetzlerWeilPositivity.ExplicitPlateauParameters

/-!
# The complete Weil energy of the eleven-square trial

The trial's three normalized Ramanujan coefficients have unit total mass.
Their arithmetic excitation is exactly `4 log 11 / 11`, while the two poles
and the archimedean center retain the squared mean `101² / 121²`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open RenormalizedArithmeticPotentialTheory ArithmeticIntersectionTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-- The three conductors in the prime-square trial at eleven. -/
def elevenPacketConductors : Finset ℕ := {1, 11, 121}

/-- Coefficients in the orthonormal Ramanujan convention. -/
def elevenPacketCoefficient (m : ℕ) : ℝ :=
  if m = 1 then 101 / 121 else
  if m = 11 then (-20 / 121) * Real.sqrt 10 else
  if m = 121 then (2 / 121) * Real.sqrt 110 else 0

theorem elevenPacketConductors_pos : ∀ m ∈ elevenPacketConductors, 0 < m := by
  intro m hm
  simp only [elevenPacketConductors, mem_insert, mem_singleton] at hm
  rcases hm with rfl | rfl | rfl <;> norm_num

/-- The finite packet is the literal unit-sign trial in pole coordinates. -/
theorem elevenPacketProfile_eq {n : ℕ} (hn : 0 < n) :
    ramanujanPacketProfile elevenPacketConductors elevenPacketCoefficient n =
      primeSquareTrial 11 n / Real.sqrt n := by
  have hex := primeSquareTrial_ramanujan (by norm_num : Nat.Prime 11) hn
  have hs10 : Real.sqrt (10 : ℝ) ≠ 0 := by positivity
  have hs110 : Real.sqrt (110 : ℝ) ≠ 0 := by positivity
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have ht11 : Nat.totient 11 = 10 := by
    simpa using Nat.totient_prime (by norm_num : Nat.Prime 11)
  have ht121 : Nat.totient 121 = 110 := by
    simpa using Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 11) 1
  norm_num only [Nat.cast_ofNat] at hex
  simp only [ramanujanPacketProfile, elevenPacketConductors, sum_insert
    (by norm_num : (1 : ℕ) ∉ ({11, 121} : Finset ℕ)), sum_insert
    (by norm_num : (11 : ℕ) ∉ ({121} : Finset ℕ)), sum_singleton,
    elevenPacketCoefficient, ramanujanPoleProfile]
  rw [normalizedRamanujanMode_eq_coefficient (by norm_num : 0 < (1 : ℕ)),
    normalizedRamanujanMode_eq_coefficient (by norm_num : 0 < (11 : ℕ)),
    normalizedRamanujanMode_eq_coefficient (by norm_num : 0 < (121 : ℕ)), hex]
  norm_num [ht11, ht121]
  field_simp [hs10, hs110, hsn]
  ring

/-- The trial has unit limiting logarithmic mass. -/
theorem elevenPacketCoefficient_mass :
    (∑ m ∈ elevenPacketConductors, elevenPacketCoefficient m ^ 2) = 1 := by
  norm_num [elevenPacketConductors, elevenPacketCoefficient, mul_pow, Real.sq_sqrt]

/-- The nonconstant arithmetic excitation cancels against the first flipped-prime term. -/
theorem elevenPacket_energy (φ : ℝ → ℝ) (c : ℝ) :
    (∑ m ∈ elevenPacketConductors,
      elevenPacketCoefficient m ^ 2 * completeWeilAdjunctionEnergy φ c m) =
      completeWeilSelfFinitePart φ c + 4 * Real.log 11 / 11 +
        completeWeilPoleShift φ c * (101 / 121 : ℝ) ^ 2 := by
  have htd11 : tameDifferent 11 = Real.log 11 / 10 := by
    have h := tameDifferent_prime_pow (p := 11) (k := 1) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have htd121 : tameDifferent 121 = Real.log 11 / 10 := by
    have h := tameDifferent_prime_pow (p := 11) (k := 2) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hlog121 : Real.log (121 : ℝ) = 2 * Real.log 11 := by
    rw [show (121 : ℝ) = 11 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  norm_num [elevenPacketConductors, elevenPacketCoefficient,
    completeWeilAdjunctionEnergy, ramanujanAdjunctionEnergy, htd11, htd121,
    show tameDifferent 1 = 0 by simp [tameDifferent], hlog121, mul_pow, Real.sq_sqrt]
  ring

/-- The actual atomic test agrees with its three-conductor packet. -/
theorem elevenPacketTest_eq (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    ramanujanPacketTest φ c elevenPacketConductors elevenPacketCoefficient N =
      atomicTest N (fun n => primeSquareTrial 11 n / Real.sqrt n) (atomDilate φ (c / N)) := by
  funext u
  unfold ramanujanPacketTest atomicTest
  apply sum_congr rfl
  intro n hn
  rw [elevenPacketProfile_eq (mem_Icc.mp hn).1]

/-- The complete untwisted energy limit retains Gamma, both poles, and every prime power. -/
theorem tendsto_elevenTrial_weil :
    Tendsto (fun N : ℕ =>
      weilQuad (atomicTest N (fun n => primeSquareTrial 11 n / Real.sqrt n)
        (atomDilate transMetzlerProfile ((99 / 100) / N))) /
          (((99 / 100) / N) * Real.log N)) atTop
      (𝓝 ((∫ u, transMetzlerProfile u ^ 2) *
        (completeWeilSelfFinitePart transMetzlerProfile (99 / 100) + 4 * Real.log 11 / 11 +
          completeWeilPoleShift transMetzlerProfile (99 / 100) * (101 / 121 : ℝ) ^ 2))) := by
  have h := tendsto_ramanujanPacketTest_weil_variable contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos
    (r := fun _ => 99 / 100) tendsto_const_nhds
    (by norm_num : (0 : ℝ) < 99 / 100) (by norm_num : (99 / 100 : ℝ) < 1)
    (H := fun N => N) tendsto_id
    elevenPacketConductors elevenPacketConductors_pos elevenPacketCoefficient
  simpa only [elevenPacketTest_eq, elevenPacket_energy] using h

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.tendsto_elevenTrial_weil
