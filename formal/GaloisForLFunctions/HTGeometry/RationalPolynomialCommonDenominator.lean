import Mathlib

open Polynomial
open scoped Classical

namespace GaloisForLFunctions.RHTower

/-- A finite family of rational polynomials admits one nonzero integer denominator. -/
theorem exists_common_integer_polynomial_scale {ι : Type*} [Fintype ι] (q : ι → ℚ[X]) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ A : ι → ℤ[X], ∀ i,
      (A i).map (Int.castRingHom ℚ) = (D : ℚ) • q i := by
  classical
  let A₀ : ι → ℤ[X] := fun i =>
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) (q i)
  choose b hbmem hbmap using fun i =>
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (q i)
  let D : ℤ := ∏ i : ι, b i
  have hb0 : ∀ i, b i ≠ 0 := fun i => nonZeroDivisors.ne_zero (hbmem i)
  have hD0 : D ≠ 0 := by
    change (∏ i : ι, b i) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact hb0 i
  let A : ι → ℤ[X] := fun i =>
    Polynomial.C (∏ j ∈ (Finset.univ : Finset ι).erase i, b j) * A₀ i
  refine ⟨D, hD0, A, fun i => ?_⟩
  have hprod : b i * ∏ j ∈ (Finset.univ : Finset ι).erase i, b j = D := by
    change b i * ∏ j ∈ (Finset.univ : Finset ι).erase i, b j = ∏ j : ι, b j
    exact Finset.mul_prod_erase (Finset.univ : Finset ι) b (Finset.mem_univ i)
  change (Polynomial.C (∏ j ∈ (Finset.univ : Finset ι).erase i, b j) * A₀ i).map
      (Int.castRingHom ℚ) = (D : ℚ) • q i
  have hbmap' : (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (q i)).map
      (Int.castRingHom ℚ) = (b i : ℚ) • q i := by
    rw [← algebraMap_int_eq]
    calc
      (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (q i)).map
          (algebraMap ℤ ℚ) = b i • q i := hbmap i
      _ = (b i : ℚ) • q i :=
        (Int.cast_smul_eq_zsmul ℚ (b i) (q i)).symm
  rw [Polynomial.map_mul, Polynomial.map_C, show A₀ i =
      IsLocalization.integerNormalization (nonZeroDivisors ℤ) (q i) from rfl, hbmap',
    Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  rw [← hprod]
  simp only [Int.coe_castRingHom]
  push_cast
  have hC : Polynomial.C (∏ j ∈ (Finset.univ : Finset ι).erase i, (b j : ℚ)) *
      Polynomial.C (b i : ℚ) =
        Polynomial.C ((b i : ℚ) * ∏ j ∈ (Finset.univ : Finset ι).erase i, (b j : ℚ)) := by
    rw [← Polynomial.C_mul]
    congr 1
    ring
  rw [← mul_assoc, hC]

end GaloisForLFunctions.RHTower
