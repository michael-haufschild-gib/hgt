import GaloisForLFunctions.HeightHomotopyArithmeticCounts.RadialLogarithmicKernel
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# Torsion energy at a finite radius

Removing coincident pairs isolates the exact self-energy. The remaining radial
correction consists of a universal logarithmic term and a nonnegative quadratic
error, controlled by the inverse squared distances of distinct torsion points.
-/

noncomputable section
open Finset Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory

/-- The Abel energy with coincident torsion points removed. -/
def puncturedTorsionEnergy (r : ℝ) (m n : ℕ) : ℝ :=
  ∑ z ∈ primitiveRoots m ℂ, ∑ w ∈ (primitiveRoots n ℂ).erase z,
    -Real.log ‖1 - (r:ℂ)*(z*conj w)‖

/-- Ordered pairs of distinct points in the two torsion orbits. -/
def torsionPairCount (m n : ℕ) : ℕ :=
  ∑ z ∈ primitiveRoots m ℂ, ((primitiveRoots n ℂ).erase z).card

/-- The finite geometric cost of the radial error. -/
def torsionInverseChordCost (m n : ℕ) : ℝ :=
  ∑ z ∈ primitiveRoots m ℂ, ∑ w ∈ (primitiveRoots n ℂ).erase z,
    1 / ‖z-w‖^2

/-- The exact remainder after the universal radial term is removed. -/
def torsionRadialError (r : ℝ) (m n : ℕ) : ℝ :=
  ∑ z ∈ primitiveRoots m ℂ, ∑ w ∈ (primitiveRoots n ℂ).erase z,
    radialChordError r (‖z-w‖^2)

private theorem torsion_pair_log (r : ℝ) (hr : 0 < r) {m n : ℕ} {z w : ℂ}
    (hz : z ∈ primitiveRoots m ℂ) (hw : w ∈ (primitiveRoots n ℂ).erase z) :
    -Real.log ‖1-(r:ℂ)*(z*conj w)‖ + Real.log r/2 + Real.log ‖z-w‖ =
      -radialChordError r (‖z-w‖^2) := by
  have hwunit := norm_of_mem_primitiveRoots (mem_of_mem_erase hw)
  have hunit : ‖z*conj w‖ = 1 := by
    rw [norm_mul, norm_conj, norm_of_mem_primitiveRoots hz, hwunit, one_mul]
  have hne : z*conj w ≠ 1 := by
    intro h
    have hd := norm_one_sub_mul_conj (ζ := z) hwunit
    rw [h, sub_self, norm_zero] at hd
    exact (ne_of_mem_erase hw) (sub_eq_zero.mp (norm_eq_zero.mp hd.symm)).symm
  simpa only [norm_one_sub_mul_conj hwunit] using radial_log_chord r hr (z*conj w) hunit hne

private theorem orbitIntersection_eq_punctured (m n : ℕ) :
    orbitIntersection m n =
      ∑ z ∈ primitiveRoots m ℂ, ∑ w ∈ (primitiveRoots n ℂ).erase z, Real.log ‖z-w‖ := by
  apply sum_congr rfl
  intro z hz
  symm
  apply sum_subset (erase_subset _ _)
  intro w hw hn
  have he : w=z := by
    by_contra hne
    exact hn (mem_erase.mpr ⟨hne, hw⟩)
  simp only [he, sub_self, norm_zero, Real.log_zero]

/-- Exact finite-radius decomposition, valid for every positive radius. -/
theorem puncturedTorsionEnergy_decomposition (r : ℝ) (hr : 0 < r) (m n : ℕ) :
    puncturedTorsionEnergy r m n + (torsionPairCount m n : ℝ)*Real.log r/2 =
      -orbitIntersection m n - torsionRadialError r m n := by
  have h := sum_congr rfl fun z (hz : z ∈ primitiveRoots m ℂ) =>
    sum_congr rfl fun w (hw : w ∈ (primitiveRoots n ℂ).erase z) => torsion_pair_log r hr hz hw
  simp only [sum_add_distrib, sum_neg_distrib] at h
  have hcount : (∑ z ∈ primitiveRoots m ℂ,
      ∑ _w ∈ (primitiveRoots n ℂ).erase z, Real.log r/2) =
        (torsionPairCount m n : ℝ)*Real.log r/2 := by
    simp only [sum_const, nsmul_eq_mul, torsionPairCount, Nat.cast_sum, sum_mul,
      sum_div, mul_div_assoc]
  rw [hcount, ← orbitIntersection_eq_punctured] at h
  simp only [puncturedTorsionEnergy, torsionRadialError, sum_neg_distrib]
  linarith only [h]

/-- The residual error is quadratic in the distance of the radius from one. -/
theorem torsionRadialError_bounds (r : ℝ) (hr : 0 < r) (m n : ℕ) :
    0 ≤ torsionRadialError r m n ∧
      torsionRadialError r m n ≤ (1-r)^2/(2*r)*torsionInverseChordCost m n := by
  have hd (z : ℂ) (w : ℂ) (hw : w ∈ (primitiveRoots n ℂ).erase z) : 0 < ‖z-w‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (ne_of_mem_erase hw).symm))
  constructor
  · exact sum_nonneg fun z hz => sum_nonneg fun w hw => (radialChordError_bounds r _ hr (hd z w hw)).1
  · unfold torsionRadialError torsionInverseChordCost
    rw [mul_sum]
    apply sum_le_sum
    intro z hz
    rw [mul_sum]
    apply sum_le_sum
    intro w hw
    calc radialChordError r (‖z-w‖^2) ≤ (1-r)^2/(2*r*‖z-w‖^2) :=
        (radialChordError_bounds r _ hr (hd z w hw)).2
      _ = (1-r)^2/(2*r)*(1/‖z-w‖^2) := by ring

/-- The coincident pairs contribute precisely the totient-weighted self-energy. -/
theorem torsionEnergy_finite_radius (r : ℝ) (hr : 0 < r) (n : ℕ) :
    torsionEnergy r n n + (Nat.totient n : ℝ)*Real.log |1-r| +
      (torsionPairCount n n : ℝ)*Real.log r/2 =
        -orbitIntersection n n - torsionRadialError r n n := by
  rw [torsionEnergy_self_add_log]
  exact puncturedTorsionEnergy_decomposition r hr n n

/-- Arithmetic certificate on the whole open unit-radius interval. -/
theorem torsion_finite_radius_certificate (r : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    torsionEnergy r n n + (Nat.totient n : ℝ)*Real.log (1-r) +
        (torsionPairCount n n : ℝ)*Real.log r/2 =
      -orbitIntersection n n - torsionRadialError r n n ∧
    0 ≤ torsionRadialError r n n ∧
      torsionRadialError r n n ≤
        (1-(r:ℝ))^2/(2*r)*torsionInverseChordCost n n := by
  refine ⟨?_, torsionRadialError_bounds r r.property.1 n n⟩
  simpa only [abs_of_pos (sub_pos.mpr r.property.2)] using
    torsionEnergy_finite_radius r r.property.1 n

#print axioms puncturedTorsionEnergy_decomposition
#print axioms torsionRadialError_bounds
#print axioms torsionEnergy_finite_radius
#print axioms torsion_finite_radius_certificate
/-- Finite-radius error control survives arbitrary signed arithmetic coefficients. -/
theorem abs_weighted_torsionRadialError_le (r : Set.Ioo (0 : ℝ) 1)
    (S : Finset ℕ) (a : ℕ → ℕ → ℝ) :
    |∑ m ∈ S, ∑ n ∈ S, a m n * torsionRadialError r m n| ≤
      (1-(r:ℝ))^2/(2*r) *
        ∑ m ∈ S, ∑ n ∈ S, |a m n| * torsionInverseChordCost m n := by
  calc
    |∑ m ∈ S, ∑ n ∈ S, a m n * torsionRadialError r m n| ≤
        ∑ m ∈ S, |∑ n ∈ S, a m n * torsionRadialError r m n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ S, ∑ n ∈ S, |a m n * torsionRadialError r m n| :=
      sum_le_sum fun m hm => Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1-(r:ℝ))^2/(2*r) *
        ∑ m ∈ S, ∑ n ∈ S, |a m n| * torsionInverseChordCost m n := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      have hb := torsionRadialError_bounds r r.property.1 m n
      rw [abs_mul, abs_of_nonneg hb.1]
      calc |a m n| * torsionRadialError r m n ≤
          |a m n| * ((1-(r:ℝ))^2/(2*r)*torsionInverseChordCost m n) :=
            mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)
        _ = (1-(r:ℝ))^2/(2*r) * (|a m n|*torsionInverseChordCost m n) := by ring

/-- A uniform finite-sum estimate for the regularized torsion pairing. -/
theorem finite_radius_signed_pairing_bound (r : Set.Ioo (0 : ℝ) 1)
    (S : Finset ℕ) (a : ℕ → ℕ → ℝ) :
    |∑ m ∈ S, ∑ n ∈ S, a m n *
      (puncturedTorsionEnergy r m n + (torsionPairCount m n : ℝ)*Real.log r/2 +
        orbitIntersection m n)| ≤
      (1-(r:ℝ))^2/(2*r) *
        ∑ m ∈ S, ∑ n ∈ S, |a m n|*torsionInverseChordCost m n := by
  have hterm (m n : ℕ) : puncturedTorsionEnergy r m n +
      (torsionPairCount m n : ℝ)*Real.log r/2 + orbitIntersection m n =
        -torsionRadialError r m n := by
    have h := puncturedTorsionEnergy_decomposition r r.property.1 m n
    linarith only [h]
  simp_rw [hterm, mul_neg, sum_neg_distrib]
  rw [abs_neg]
  exact abs_weighted_torsionRadialError_le r S a

#print axioms abs_weighted_torsionRadialError_le
#print axioms finite_radius_signed_pairing_bound

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
