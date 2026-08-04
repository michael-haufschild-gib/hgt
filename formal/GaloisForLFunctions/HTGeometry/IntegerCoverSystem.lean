import GaloisForLFunctions.HTGeometry.TorusCohomologyColimit
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Towers of tori from integer matrices

A vector with integer coordinates lies in the period lattice of period one, so a functorial family
of integer matrices between coordinate spaces is a directed system of tori: the associated linear
maps carry the period lattice into the period lattice, and they compose because the matrices do.
This is the form in which a filtration by lattices produces a tower of tori, once bases have been
chosen.

* `integerVector_mem_periodLattice` : an integer vector lies in the period lattice.
* `IntegerCoverSystem` : a functorial family of integer matrices.
* `torusCoverSystemOfMatrices` : the tower of tori it defines.
-/

set_option maxSynthPendingDepth 3

namespace GaloisForLFunctions.HTGeometry

section IntegerVectors

variable {𝕜 : Type u} [RCLike 𝕜] {r : ℕ}

/-- **A vector with integer coordinates lies in the period lattice of period one.** -/
theorem integerVector_mem_periodLattice (m : Fin r → ℤ) :
    (fun a => ((m a : ℤ) : 𝕜)) ∈ periodLattice (1 : 𝕜) r := by
  classical
  have hsum : (fun a => ((m a : ℤ) : 𝕜)) =
      ∑ b : Fin r, (m b) • ((1 : 𝕜) • (Pi.single b (1 : 𝕜) : Fin r → 𝕜)) := by
    funext a
    rw [Finset.sum_apply, Finset.sum_eq_single a]
    · simp [Pi.single_eq_same, zsmul_eq_mul]
    · intro b _ hb
      simp [Pi.single_eq_of_ne (Ne.symm hb)]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [hsum]
  refine sum_mem fun b _ => ?_
  exact zsmul_mem (periodVector_mem_periodLattice (1 : 𝕜) b) _

end IntegerVectors

section Matrices

variable {ι : Type v} [Preorder ι]

/-- **A functorial family of integer matrices** between coordinate spaces. -/
structure IntegerCoverSystem (ι : Type v) [Preorder ι] where
  /-- The dimension of the coordinate space attached to an index. -/
  dim : ι → ℕ
  /-- The matrix attached to a relation. -/
  mat : ∀ i j, i ≤ j → Matrix (Fin (dim i)) (Fin (dim j)) ℤ
  /-- The matrix of a reflexive relation is the identity. -/
  mat_self : ∀ (i : ι) (h : i ≤ i), mat i i h = 1
  /-- The matrices compose. -/
  mat_trans : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k),
    (mat i j hij) * (mat j k hjk) = mat i k (hij.trans hjk)

variable {𝕜 : Type u} [RCLike 𝕜] (M : IntegerCoverSystem ι)

/-- The linear map of coordinate spaces attached to an integer matrix. -/
noncomputable def matrixCover (𝕜 : Type u) [RCLike 𝕜] {a b : ℕ}
    (m : Matrix (Fin a) (Fin b) ℤ) : (Fin b → 𝕜) →L[𝕜] (Fin a → 𝕜) :=
  ContinuousLinearMap.pi fun i =>
    ∑ j : Fin b, ((m i j : ℤ) : 𝕜) • ContinuousLinearMap.proj j

@[simp]
theorem matrixCover_apply {a b : ℕ} (m : Matrix (Fin a) (Fin b) ℤ) (x : Fin b → 𝕜) (i : Fin a) :
    matrixCover 𝕜 m x i = ∑ j : Fin b, ((m i j : ℤ) : 𝕜) * x j := by
  show (∑ j : Fin b, ((m i j : ℤ) : 𝕜) • ContinuousLinearMap.proj (R := 𝕜) j) x = _
  rw [sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- **The tower of tori defined by a functorial family of integer matrices**, with period one. -/
noncomputable def torusCoverSystemOfMatrices : TorusCoverSystem 𝕜 (1 : 𝕜) ι where
  dim := M.dim
  map i j h := matrixCover 𝕜 (M.mat i j h)
  map_lattice := by
    classical
    intro i j h l
    have hval : matrixCover 𝕜 (M.mat i j h)
        ((1 : 𝕜) • (Pi.single l (1 : 𝕜) : Fin (M.dim j) → 𝕜)) =
        fun a => (((M.mat i j h) a l : ℤ) : 𝕜) := by
      funext a
      rw [matrixCover_apply, Finset.sum_eq_single l]
      · show ((M.mat i j h) a l : 𝕜) * ((1 : 𝕜) • (Pi.single l (1 : 𝕜) : Fin (M.dim j) → 𝕜)) l = _
        rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, mul_one]
      · intro c _ hc
        show ((M.mat i j h) a c : 𝕜) *
          ((1 : 𝕜) • (Pi.single l (1 : 𝕜) : Fin (M.dim j) → 𝕜)) c = 0
        rw [Pi.smul_apply, Pi.single_eq_of_ne hc, smul_zero, mul_zero]
      · intro hc
        exact absurd (Finset.mem_univ l) hc
    rw [hval]
    exact integerVector_mem_periodLattice _
  map_self := by
    intro i h
    refine ContinuousLinearMap.ext fun x => ?_
    funext a
    rw [matrixCover_apply, M.mat_self i h]
    rw [Finset.sum_eq_single a]
    · show ((1 : Matrix (Fin (M.dim i)) (Fin (M.dim i)) ℤ) a a : 𝕜) * x a = x a
      rw [Matrix.one_apply_eq]
      norm_num
    · intro c _ hc
      show ((1 : Matrix (Fin (M.dim i)) (Fin (M.dim i)) ℤ) a c : 𝕜) * x c = 0
      rw [Matrix.one_apply_ne (Ne.symm hc)]
      norm_num
    · intro hc
      exact absurd (Finset.mem_univ a) hc
  map_trans := by
    intro i j k hij hjk
    refine ContinuousLinearMap.ext fun x => ?_
    funext a
    rw [← M.mat_trans i j k hij hjk]
    show matrixCover 𝕜 (M.mat i j hij) (matrixCover 𝕜 (M.mat j k hjk) x) a = _
    simp only [matrixCover_apply, Matrix.mul_apply, Finset.mul_sum]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring

end Matrices

end GaloisForLFunctions.HTGeometry
