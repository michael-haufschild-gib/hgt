import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreMap
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Differential automorphisms act on operators, and semilinear automorphisms are matrices

A ring homomorphism of differential rings commuting with the derivation transports differential
operators coefficientwise as a *ring* homomorphism: it commutes with left multiplication by `∂`
because the two coefficient recursions of `∂ · p` are built from the derivation alone.  A
differential automorphism of the coefficient field therefore acts on `K[∂;δ]`.

Independently, a `σ`-semilinear automorphism of a free module of finite rank is given by a matrix
which is invertible over the ring: the matrices of the automorphism and of its inverse satisfy the
two identities obtained from `T' ∘ T = id` and `T ∘ T' = id`, and the coefficient automorphism
carries one into the inverse of the other.

* `map_dpartial`, `map_mul'`, `mapRingHom`, `mapRingEquiv`;
* `exists_matrix_of_apply`, `isUnit_matrix_of_semilinear_equiv`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K L : Type*} [CommRing K] [Differential K] [CommRing L] [Differential L]

theorem map_zero' (f : K →+* L) : map f (0 : DiffOp K) = 0 := by
  ext n
  rw [coeff_map, coeff_zero, coeff_zero, map_zero]

theorem map_one' (f : K →+* L) : map f (1 : DiffOp K) = 1 := by
  rw [one_def, one_def, map_mono, f.map_one]

/-- A derivation-commuting homomorphism intertwines left multiplication by `∂`. -/
theorem map_dpartial (f : K →+* L) (hf : ∀ a : K, f (a′) = (f a)′) (p : DiffOp K) :
    map f (dpartial p) = dpartial (map f p) := by
  ext n
  cases n with
  | zero => rw [coeff_map, coeff_dpartial_zero, coeff_dpartial_zero, coeff_map, hf]
  | succ n =>
      rw [coeff_map, coeff_dpartial_succ, coeff_dpartial_succ, f.map_add, coeff_map, coeff_map, hf]

theorem map_dpartial_iterate (f : K →+* L) (hf : ∀ a : K, f (a′) = (f a)′) (n : ℕ)
    (p : DiffOp K) : map f (dpartial^[n] p) = dpartial^[n] (map f p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_dpartial f hf, ih]

/-- **A derivation-commuting homomorphism is multiplicative on operators.** -/
theorem map_mul' (f : K →+* L) (hf : ∀ a : K, f (a′) = (f a)′) (p q : DiffOp K) :
    map f (p * q) = map f p * map f q := by
  refine induction_linear (motive := fun p => map f (p * q) = map f p * map f q) p ?_ ?_ ?_
  · rw [zero_mul', map_zero', zero_mul']
  · intro p₁ p₂ h₁ h₂
    rw [add_mul', map_add, h₁, h₂, map_add, add_mul']
  · intro n a
    rw [mono_mul, map_smul, map_dpartial_iterate f hf, map_mono, mono_mul]

/-- The induced ring homomorphism of operator rings. -/
def mapRingHom (f : K →+* L) (hf : ∀ a : K, f (a′) = (f a)′) : DiffOp K →+* DiffOp L where
  toFun := map f
  map_one' := map_one' f
  map_mul' := map_mul' f hf
  map_zero' := map_zero' f
  map_add' := map_add f

@[simp] theorem mapRingHom_apply (f : K →+* L) (hf : ∀ a : K, f (a′) = (f a)′) (p : DiffOp K) :
    mapRingHom f hf p = map f p := rfl

theorem symm_deriv_comm {σ : K ≃+* K} (hσ : ∀ a : K, σ (a′) = (σ a)′) (a : K) :
    σ.symm (a′) = (σ.symm a)′ := by
  apply σ.injective
  rw [RingEquiv.apply_symm_apply, hσ, RingEquiv.apply_symm_apply]

/-- **A differential automorphism of the coefficients acts on the operator ring.** -/
def mapRingEquiv (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′) : DiffOp K ≃+* DiffOp K where
  toFun := map (σ : K →+* K)
  invFun := map (σ.symm : K →+* K)
  left_inv p := by
    ext n
    rw [coeff_map, coeff_map]
    exact σ.symm_apply_apply _
  right_inv p := by
    ext n
    rw [coeff_map, coeff_map]
    exact σ.apply_symm_apply _
  map_mul' := map_mul' (σ : K →+* K) hσ
  map_add' := map_add (σ : K →+* K)

@[simp] theorem mapRingEquiv_apply (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′) (p : DiffOp K) :
    mapRingEquiv σ hσ p = map (σ : K →+* K) p := rfl

end

end DiffOp

section Semilinear

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {r : ℕ}

theorem map_zero_of_add {S : M → M} (hadd : ∀ x y, S (x + y) = S x + S y) : S 0 = 0 := by
  have h : S 0 + S 0 = S 0 + 0 := by rw [← hadd, add_zero, add_zero]
  exact add_left_cancel h

/-- The matrix of a map in a basis; for a semilinear map this is its matrix. -/
theorem exists_matrix_of_apply (b : Module.Basis (Fin r) R M) (T : M → M) :
    ∃ A : Matrix (Fin r) (Fin r) R, ∀ i, T (b i) = ∑ j, A i j • b j :=
  ⟨fun i j => b.repr (T (b i)) j, fun i => (b.sum_repr (T (b i))).symm⟩

/-- A semilinear map carries a basis combination to the twisted combination of the images. -/
theorem apply_sum_smul_of_semilinear {τ : R ≃+* R} {S : M → M}
    (hadd : ∀ x y, S (x + y) = S x + S y) (hsmul : ∀ (a : R) (x : M), S (a • x) = τ a • S x)
    (b : Module.Basis (Fin r) R M) (s : Finset (Fin r)) (g : Fin r → R) :
    S (∑ j ∈ s, g j • b j) = ∑ j ∈ s, τ (g j) • S (b j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, map_zero_of_add hadd]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih]

/-- The composition identity for the two matrices of a semilinear pair. -/
theorem sum_mul_matrix_of_semilinear_comp {τ : R ≃+* R} (b : Module.Basis (Fin r) R M)
    (S S' : M → M) (B B' : Matrix (Fin r) (Fin r) R)
    (hadd : ∀ x y, S' (x + y) = S' x + S' y) (hsmul : ∀ (a : R) (x : M), S' (a • x) = τ a • S' x)
    (hB : ∀ i, S (b i) = ∑ j, B i j • b j) (hB' : ∀ i, S' (b i) = ∑ j, B' i j • b j)
    (hinv : ∀ x, S' (S x) = x) (i k : Fin r) :
    ∑ j, τ (B i j) * B' j k = if i = k then 1 else 0 := by
  classical
  have hexp : S' (S (b i)) = ∑ j, ∑ l, (τ (B i j) * B' j l) • b l := by
    rw [hB, apply_sum_smul_of_semilinear hadd hsmul b Finset.univ (B i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hB', Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
  have hrepr := congrArg (fun x => b.repr x k) hexp
  rw [hinv, b.repr_self_apply] at hrepr
  have hright : b.repr (∑ j, ∑ l, (τ (B i j) * B' j l) • b l) k
      = ∑ j, τ (B i j) * B' j k := by
    rw [map_sum]
    simp only [Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    simp only [Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, b.repr_self,
      Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
    · intro l _ hl
      rw [if_neg hl, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon
  rw [hright] at hrepr
  exact hrepr.symm

/-- **A semilinear automorphism of a finite free module has an invertible matrix.** -/
theorem isUnit_matrix_of_semilinear_equiv (σ : R ≃+* R) (b : Module.Basis (Fin r) R M)
    (T T' : M → M)
    (hTadd : ∀ x y, T (x + y) = T x + T y)
    (hTsmul : ∀ (a : R) (x : M), T (a • x) = σ a • T x)
    (hT'add : ∀ x y, T' (x + y) = T' x + T' y)
    (hT'smul : ∀ (a : R) (x : M), T' (a • x) = σ.symm a • T' x)
    (hTT' : ∀ x, T (T' x) = x) (hT'T : ∀ x, T' (T x) = x) :
    ∃ A A' : Matrix (Fin r) (Fin r) R,
      (∀ i, T (b i) = ∑ j, A i j • b j) ∧ (∀ i, T' (b i) = ∑ j, A' i j • b j) ∧
        A * A'.map (σ : R →+* R) = 1 ∧ A'.map (σ : R →+* R) * A = 1 := by
  classical
  obtain ⟨A, hA⟩ := exists_matrix_of_apply b T
  obtain ⟨A', hA'⟩ := exists_matrix_of_apply b T'
  refine ⟨A, A', hA, hA', ?_, ?_⟩
  · ext i k
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h := sum_mul_matrix_of_semilinear_comp (τ := σ.symm) b T T' A A' hT'add hT'smul hA hA'
      hT'T i k
    have hσ := congrArg (fun x : R => σ x) h
    rw [map_sum] at hσ
    have hleft : ∑ j, σ (σ.symm (A i j) * A' j k) = ∑ j, A i j * (A'.map (σ : R →+* R)) j k := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, RingEquiv.apply_symm_apply]
      rfl
    rw [hleft] at hσ
    rw [hσ]
    by_cases hik : i = k
    · rw [if_pos hik, map_one]
    · rw [if_neg hik, map_zero]
  · ext i k
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact sum_mul_matrix_of_semilinear_comp (τ := σ) b T' T A' A hTadd hTsmul hA' hA hTT' i k

end Semilinear

end GaloisForLFunctions.HTGeometry
