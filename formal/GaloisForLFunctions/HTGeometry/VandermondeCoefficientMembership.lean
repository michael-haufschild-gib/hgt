import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Coefficients of a module-valued polynomial that takes values in a submodule

A polynomial with coefficients in a vector space is determined by its values at as many distinct
points as it has coefficients: the Vandermonde matrix of those points is invertible, so every
coefficient is an explicit linear combination of the values.  Hence a submodule containing enough
values contains every coefficient.

The graded form is the one used in practice: a finite sum indexed by objects carrying a degree is
a polynomial in the scale, and each homogeneous part lies in the submodule.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- **Vandermonde coefficient extraction.**  If a polynomial of degree below `n` with vector
coefficients takes values in a submodule at `n` distinct scalars, every coefficient lies in that
submodule. -/
theorem mem_of_forall_polynomial_value_mem {n : ℕ} (w : Fin n → V) (U : Submodule 𝕜 V)
    (x : Fin n → 𝕜) (hx : Function.Injective x)
    (hmem : ∀ i : Fin n, (∑ k : Fin n, x i ^ (k : ℕ) • w k) ∈ U) (k : Fin n) :
    w k ∈ U := by
  classical
  have hdet : IsUnit (Matrix.vandermonde x).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hx)
  have hinv : (Matrix.vandermonde x)⁻¹ * Matrix.vandermonde x = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have hstep : ∀ i : Fin n,
      ((Matrix.vandermonde x)⁻¹ k i) • (∑ j : Fin n, x i ^ (j : ℕ) • w j) =
        ∑ j : Fin n, ((Matrix.vandermonde x)⁻¹ k i * Matrix.vandermonde x i j) • w j := by
    intro i
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
  have hcol : ∀ j : Fin n,
      (∑ i : Fin n, ((Matrix.vandermonde x)⁻¹ k i * Matrix.vandermonde x i j) • w j) =
        ((1 : Matrix (Fin n) (Fin n) 𝕜) k j) • w j := by
    intro j
    rw [← Finset.sum_smul, ← hinv, Matrix.mul_apply]
  have key : (∑ i : Fin n, ((Matrix.vandermonde x)⁻¹ k i) •
      (∑ j : Fin n, x i ^ (j : ℕ) • w j)) = w k := by
    simp only [hstep]
    rw [Finset.sum_comm]
    simp only [hcol]
    rw [Finset.sum_eq_single k]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon
  rw [← key]
  exact Submodule.sum_mem U fun i _ => Submodule.smul_mem U _ (hmem i)

/-- **Graded form of Vandermonde coefficient extraction.**  A finite sum whose terms carry a
degree below `n` is a polynomial in the scale; if the scaled sum lies in a submodule at `n`
distinct scalars, every homogeneous part lies in that submodule. -/
theorem mem_of_forall_gradedSum_mem {α : Type*} [Fintype α] {n : ℕ} (U : Submodule 𝕜 V)
    (d : α → Fin n) (v : α → V) (x : Fin n → 𝕜) (hx : Function.Injective x)
    (hmem : ∀ i : Fin n, (∑ a : α, x i ^ ((d a : ℕ)) • v a) ∈ U) (k : Fin n) :
    (∑ a ∈ Finset.univ.filter fun a => d a = k, v a) ∈ U := by
  classical
  refine mem_of_forall_polynomial_value_mem
    (fun k => ∑ a ∈ Finset.univ.filter fun a => d a = k, v a) U x hx (fun i => ?_) k
  have hsum : (∑ k : Fin n, x i ^ (k : ℕ) •
      ∑ a ∈ Finset.univ.filter fun a => d a = k, v a) =
      ∑ a : α, x i ^ ((d a : ℕ)) • v a := by
    rw [← Finset.sum_fiberwise Finset.univ d fun a => x i ^ ((d a : ℕ)) • v a]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]
  rw [hsum]
  exact hmem i

end

end GaloisForLFunctions.HTGeometry
