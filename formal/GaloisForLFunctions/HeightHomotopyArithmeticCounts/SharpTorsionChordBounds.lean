import GaloisForLFunctions.HeightHomotopyArithmeticCounts.TorsionChordEnergy
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.FiniteRadiusTorsionEnergy

/-!
# Sharp conductor bounds for primitive torsion chords

Ratios of distinct torsion points of orders `m,n` are nontrivial roots of
unity of order dividing `lcm(m,n)`. Each row embeds in that full root set.
The exact full-root energy therefore bounds the punctured orbit cost by
`min(φ(m),φ(n)) (lcm(m,n)²-1)/12`.
-/

noncomputable section
open Finset Complex Polynomial
open scoped ComplexConjugate
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory

/-- Zero extension at coincident points permits transposing the punctured sum. -/
private theorem torsionInverseChordCost_full (m n : ℕ) :
    torsionInverseChordCost m n =
      ∑ z ∈ primitiveRoots m ℂ, ∑ w ∈ primitiveRoots n ℂ, 1/‖z-w‖^2 := by
  apply sum_congr rfl
  intro z _hz
  apply sum_subset (erase_subset _ _)
  intro w hw hnot
  have he : w=z := by
    by_contra hne
    exact hnot (mem_erase.mpr ⟨hne, hw⟩)
  simp [he]

/-- The inverse-chord cost is symmetric in the two primitive orbits. -/
theorem torsionInverseChordCost_comm (m n : ℕ) :
    torsionInverseChordCost m n = torsionInverseChordCost n m := by
  rw [torsionInverseChordCost_full, torsionInverseChordCost_full, sum_comm]
  apply sum_congr rfl
  intro z _hz
  apply sum_congr rfl
  intro w _hw
  rw [norm_sub_rev]

private theorem torsionInverseChordCost_le_full_root (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    torsionInverseChordCost m n ≤ (Nat.totient m:ℝ)*unityChordEnergy (Nat.lcm m n) := by
  have hL := Nat.lcm_pos hm hn
  have hrow (z : ℂ) (hz : z ∈ primitiveRoots m ℂ) :
      (∑ w ∈ (primitiveRoots n ℂ).erase z, 1/‖z-w‖^2) ≤ unityChordEnergy (Nat.lcm m n) := by
    have hzne : z≠0 := norm_ne_zero_iff.mp (by rw [norm_of_mem_primitiveRoots hz]; norm_num)
    have hinj : Function.Injective (fun w : ℂ => z*conj w) := by
      intro v w h
      exact star_injective (mul_left_cancel₀ hzne h)
    have hmem (w : ℂ) (hw : w ∈ (primitiveRoots n ℂ).erase z) :
        z*conj w ∈ (nthRootsFinset (Nat.lcm m n) (1:ℂ)).erase 1 := by
      have hwroot := mem_of_mem_erase hw
      refine mem_erase.mpr ⟨?_, (mem_nthRootsFinset hL 1).mpr ?_⟩
      · intro h
        have hd := norm_one_sub_mul_conj (ζ := z) (norm_of_mem_primitiveRoots hwroot)
        rw [h, sub_self, norm_zero] at hd
        exact (ne_of_mem_erase hw) (sub_eq_zero.mp (norm_eq_zero.mp hd.symm)).symm
      · have hzpow := ((mem_primitiveRoots hm).mp hz).pow_eq_one
        have hwpow := ((mem_primitiveRoots hn).mp hwroot).pow_eq_one
        have hwc : (conj w)^n=1 := by rw [← map_pow, hwpow, map_one]
        have hzL : z^(Nat.lcm m n)=1 := by
          obtain ⟨k, hk⟩ := Nat.dvd_lcm_left m n
          rw [hk, pow_mul, hzpow, one_pow]
        have hwL : (conj w)^(Nat.lcm m n)=1 := by
          obtain ⟨k, hk⟩ := Nat.dvd_lcm_right m n
          rw [hk, pow_mul, hwc, one_pow]
        rw [mul_pow, hzL, hwL, one_mul]
    calc
      (∑ w ∈ (primitiveRoots n ℂ).erase z, 1/‖z-w‖^2) =
          ∑ w ∈ (primitiveRoots n ℂ).erase z, 1/‖1-z*conj w‖^2 := by
        apply sum_congr rfl
        intro w hw
        rw [norm_one_sub_mul_conj (norm_of_mem_primitiveRoots (mem_of_mem_erase hw))]
      _ = ∑ u ∈ ((primitiveRoots n ℂ).erase z).image (fun w => z*conj w), 1/‖1-u‖^2 :=
        (sum_image hinj.injOn).symm
      _ ≤ unityChordEnergy (Nat.lcm m n) := by
        unfold unityChordEnergy
        apply sum_le_sum_of_subset_of_nonneg
        · intro u hu
          obtain ⟨w, hw, rfl⟩ := mem_image.mp hu
          exact hmem w hw
        · intro u _hu _hnot
          exact div_nonneg zero_le_one (sq_nonneg _)
  calc torsionInverseChordCost m n ≤
      ∑ _z ∈ primitiveRoots m ℂ, unityChordEnergy (Nat.lcm m n) :=
        sum_le_sum hrow
    _ = (Nat.totient m:ℝ)*unityChordEnergy (Nat.lcm m n) := by
      simp only [sum_const, nsmul_eq_mul,
        (Complex.isPrimitiveRoot_exp m hm.ne').card_primitiveRoots]

/-- The full-root energy replaces pairwise separation by an exact conductor cost. -/
theorem torsionInverseChordCost_sharp (m n : ℕ) :
    torsionInverseChordCost m n ≤
      ((min (Nat.totient m) (Nat.totient n):ℕ):ℝ)*(((Nat.lcm m n:ℕ):ℝ)^2-1)/12 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [torsionInverseChordCost]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [torsionInverseChordCost]
  have hleft := torsionInverseChordCost_le_full_root m n hm hn
  have hright := torsionInverseChordCost_le_full_root n m hn hm
  rw [torsionInverseChordCost_comm n m, Nat.lcm_comm n m] at hright
  rw [unityChordEnergy_of_pos _ (Nat.lcm_pos hm hn)] at hleft hright
  rcases le_total (Nat.totient m) (Nat.totient n) with h | h
  · rw [min_eq_left h]
    simpa only [mul_div_assoc] using hleft
  · rw [min_eq_right h]
    simpa only [mul_div_assoc] using hright

/-- The self-orbit remainder has a cubic conductor cost before normalization. -/
theorem torsionRadialError_self_sharp (r : ℝ) (hr : 0<r) (n : ℕ) :
    torsionRadialError r n n ≤
      (1-r)^2*(Nat.totient n:ℝ)*((n:ℝ)^2-1)/(24*r) := by
  have hc := torsionInverseChordCost_sharp n n
  simp only [Nat.lcm_self, min_self] at hc
  calc torsionRadialError r n n ≤ (1-r)^2/(2*r)*torsionInverseChordCost n n :=
      (torsionRadialError_bounds r hr n n).2
    _ ≤ (1-r)^2/(2*r)*((Nat.totient n:ℝ)*((n:ℝ)^2-1)/12) :=
      mul_le_mul_of_nonneg_left hc (div_nonneg (sq_nonneg _) (by positivity))
    _ = (1-r)^2*(Nat.totient n:ℝ)*((n:ℝ)^2-1)/(24*r) := by ring

#print axioms torsionInverseChordCost_sharp
#print axioms torsionRadialError_self_sharp
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
