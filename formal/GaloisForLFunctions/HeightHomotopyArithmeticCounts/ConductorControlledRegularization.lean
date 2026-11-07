import GaloisForLFunctions.HeightHomotopyArithmeticCounts.TorsionChordSeparation
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.FiniteRadiusTorsionEnergy

/-!
# Conductor-controlled torsion regularization

The finite-radius error is uniformly bounded by the conductors and the exact
number of distinct primitive torsion pairs. The bound applies to arbitrary
signed finite pairings and retains the separate divergent diagonal.
-/

noncomputable section
open Finset Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory

private theorem card_primitiveRoots_nat (n : ℕ) : (primitiveRoots n ℂ).card = Nat.totient n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Complex.isPrimitiveRoot_exp n hn.ne').card_primitiveRoots

/-- On one torsion orbit the radial coefficient counts all ordered distinct pairs. -/
theorem torsionPairCount_self (n : ℕ) :
    torsionPairCount n n = Nat.totient n * (Nat.totient n - 1) := by
  unfold torsionPairCount
  rw [sum_congr rfl (fun z hz => card_erase_of_mem hz)]
  simp only [sum_const, nsmul_eq_mul, card_primitiveRoots_nat]

/-- Different primitive orders have disjoint point sets. -/
theorem torsionPairCount_of_ne (m n : ℕ) (hmn : m ≠ n) :
    torsionPairCount m n = Nat.totient m * Nat.totient n := by
  have hnot (z : ℂ) (hz : z ∈ primitiveRoots m ℂ) : z ∉ primitiveRoots n ℂ := by
    intro hnz
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst m
      simp at hz
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      simp at hnz
    exact hmn (((mem_primitiveRoots hm).mp hz).unique ((mem_primitiveRoots hn).mp hnz))
  unfold torsionPairCount
  rw [sum_congr rfl (fun z hz => congrArg Finset.card (erase_eq_of_notMem (hnot z hz)))]
  simp only [sum_const, nsmul_eq_mul, card_primitiveRoots_nat]

#print axioms torsionPairCount_self
#print axioms torsionPairCount_of_ne

/-- The inverse-chord cost is bounded by the conductors and the actual pair count. -/
theorem torsionInverseChordCost_le (m n : ℕ) :
    torsionInverseChordCost m n ≤ (torsionPairCount m n : ℝ)*((m*n:ℕ):ℝ)^2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [torsionInverseChordCost, torsionPairCount]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [torsionInverseChordCost, torsionPairCount]
  calc
    torsionInverseChordCost m n ≤
        ∑ z ∈ primitiveRoots m ℂ, ∑ _w ∈ (primitiveRoots n ℂ).erase z,
          ((m*n:ℕ):ℝ)^2 := by
      apply sum_le_sum
      intro z hz
      apply sum_le_sum
      intro w hw
      have hwroot := mem_of_mem_erase hw
      have hwunit := norm_of_mem_primitiveRoots hwroot
      have hunit : ‖z*conj w‖=1 := by
        rw [norm_mul, norm_conj, norm_of_mem_primitiveRoots hz, hwunit, one_mul]
      have hne : z*conj w≠1 := by
        intro h
        have hd := norm_one_sub_mul_conj (ζ := z) hwunit
        rw [h, sub_self, norm_zero] at hd
        exact (ne_of_mem_erase hw) (sub_eq_zero.mp (norm_eq_zero.mp hd.symm)).symm
      have hzpow := ((mem_primitiveRoots hm).mp hz).pow_eq_one
      have hwpow := ((mem_primitiveRoots hn).mp hwroot).pow_eq_one
      have hwc : (conj w)^n=1 := by rw [← map_pow, hwpow, map_one]
      have hp : (z*conj w)^(m*n)=1 := by
        rw [mul_pow, pow_mul, hzpow, one_pow, one_mul,
          Nat.mul_comm m n, pow_mul, hwc, one_pow]
      simpa only [norm_one_sub_mul_conj hwunit] using
        inverse_chord_le_conductor_sq (m*n) (Nat.mul_pos hm hn) (z*conj w) hunit hne hp
    _ = (torsionPairCount m n : ℝ)*((m*n:ℕ):ℝ)^2 := by
      simp only [torsionPairCount, Nat.cast_sum, sum_const, nsmul_eq_mul, sum_mul]

/-- The finite-radius remainder admits a uniform arithmetic majorant. -/
theorem torsionRadialError_conductor_bound (r : Set.Ioo (0:ℝ) 1) (m n : ℕ) :
    torsionRadialError r m n ≤
      (1-(r:ℝ))^2/(2*r)*((torsionPairCount m n:ℝ)*((m*n:ℕ):ℝ)^2) := by
  exact (torsionRadialError_bounds r r.property.1 m n).2.trans
    (mul_le_mul_of_nonneg_left (torsionInverseChordCost_le m n)
      (div_nonneg (sq_nonneg _) (mul_pos (by norm_num) r.property.1).le))

/-- A signed torsion pairing has an error bound expressed entirely in arithmetic data. -/
theorem finite_radius_conductor_certificate (r : Set.Ioo (0:ℝ) 1)
    (S : Finset ℕ) (a : ℕ → ℕ → ℝ) :
    |∑ m ∈ S, ∑ n ∈ S, a m n *
      (puncturedTorsionEnergy r m n + (torsionPairCount m n:ℝ)*Real.log r/2 +
        orbitIntersection m n)| ≤
      (1-(r:ℝ))^2/(2*r)*
        ∑ m ∈ S, ∑ n ∈ S, |a m n|*((torsionPairCount m n:ℝ)*((m*n:ℕ):ℝ)^2) := by
  refine (finite_radius_signed_pairing_bound r S a).trans ?_
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (sq_nonneg _) (mul_pos (by norm_num) r.property.1).le)
  exact sum_le_sum fun m hm => sum_le_sum fun n hn =>
    mul_le_mul_of_nonneg_left (torsionInverseChordCost_le m n) (abs_nonneg _)

#print axioms torsionInverseChordCost_le
#print axioms torsionRadialError_conductor_bound
#print axioms finite_radius_conductor_certificate

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
