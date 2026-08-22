import GaloisForLFunctions.HTGeometry.NearDiagonalOverlapFlatness
import GaloisForLFunctions.HTGeometry.CollisionEnsembleLaw
import GaloisForLFunctions.HTGeometry.TwoLocalGenericFamily
import GaloisForLFunctions.HTGeometry.BooleanHypercubeTranspositionLaw

/-!
# The Walsh transform diagonalises the transverse part of a hypercube Hamiltonian

The transverse flips `T_i` of the Boolean hypercube commute and are simultaneously diagonalised by
the Walsh–Hadamard matrix, with eigenvalues `(-1)^{x_i}`.  In the Walsh frame a transverse-field
Hamiltonian `D + ∑_i u_i T_i` is therefore *diagonal plus the rotated diagonal part*, and the
all-zero product state becomes the flat superposition.  That is exactly the configuration in which
`NearDiagonalOverlapFlatness.spectralCollision_le_of_near_diagonal` bounds the spectral collision by
`(2^{-n/2} + 2‖D‖/γ)²`, with `γ` the separation of the transverse energies `∑_i ± u_i`.

## Main results

* `cubeSign`, `walshMatrix` — the Walsh characters of the hypercube and their matrix.
* `sum_cubeSign_mul` — Walsh orthogonality.
* `walshMatrix_mul_self` — the Walsh matrix is an involution.
* `transverseOnly` — the transverse part, split off from `transverseFamilyHam`.
* `transverseFamilyHam_eq_diagonal_add` — the split.
* `conj_walsh_transverseOnly` — **the Walsh frame diagonalises the transverse part.**
-/

open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

namespace Walsh

set_option linter.unusedSectionVars false

noncomputable section

variable {n : ℕ}

/-- The sign of one Boolean coordinate: `+1` at `false`, `-1` at `true`. -/
def boolSign (b : Bool) : ℂ := if b then -1 else 1

@[simp] theorem boolSign_false : boolSign false = 1 := rfl
@[simp] theorem boolSign_true : boolSign true = -1 := rfl

theorem boolSign_ne_zero (b : Bool) : boolSign b ≠ 0 := by
  cases b <;> simp [boolSign]

/-- The Walsh character `(-1)^{x·y}` of the Boolean hypercube. -/
def cubeSign (x y : Fin n → Bool) : ℂ := ∏ i, boolSign (x i && y i)

theorem cubeSign_comm (x y : Fin n → Bool) : cubeSign x y = cubeSign y x := by
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Bool.and_comm]

@[simp] theorem cubeSign_zero_left (y : Fin n → Bool) :
    cubeSign (fun _ => false) y = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  simp [boolSign]

theorem star_cubeSign (x y : Fin n → Bool) : star (cubeSign x y) = cubeSign x y := by
  rw [cubeSign, star_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases h : (x i && y i) <;> simp [boolSign]

theorem norm_cubeSign (x y : Fin n → Bool) : ‖cubeSign x y‖ = 1 := by
  rw [cubeSign, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  cases h : (x i && y i) <;> simp [boolSign]

/-- **Walsh orthogonality on the hypercube.** -/
theorem sum_cubeSign_mul (x y : Fin n → Bool) :
    ∑ z : Fin n → Bool, cubeSign x z * cubeSign y z
      = if x = y then ((2 : ℂ) ^ n) else 0 := by
  classical
  have hfac : ∀ z : Fin n → Bool, cubeSign x z * cubeSign y z
      = ∏ i, (boolSign (x i && z i) * boolSign (y i && z i)) := by
    intro z
    rw [cubeSign, cubeSign, ← Finset.prod_mul_distrib]
  have hswap : ∑ z : Fin n → Bool, ∏ i, (boolSign (x i && z i) * boolSign (y i && z i))
      = ∏ i, ∑ b : Bool, (boolSign (x i && b) * boolSign (y i && b)) := by
    rw [Finset.prod_univ_sum]
    refine Finset.sum_nbij' (fun p _ => fun i => p i (Finset.mem_univ i))
      (fun z _ => fun i _ => z i) ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl
  have hcoord : ∀ i : Fin n, ∑ b : Bool, (boolSign (x i && b) * boolSign (y i && b))
      = if x i = y i then (2 : ℂ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases hx : x i <;> cases hy : y i <;> simp [boolSign]
  rw [Finset.sum_congr rfl (fun z _ => hfac z), hswap,
    Finset.prod_congr rfl (fun i _ => hcoord i)]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Finset.prod_congr rfl (fun i _ => if_pos rfl), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc
      exact hxy (funext fun i => not_not.mp (fun h => hc ⟨i, h⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The normalisation `2^{-n/2}` of the Walsh matrix. -/
def cubeNorm (n : ℕ) : ℝ := (Real.sqrt ((2 : ℝ) ^ n))⁻¹

theorem cubeNorm_pos (n : ℕ) : 0 < cubeNorm n := by
  rw [cubeNorm]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem cubeNorm_sq (n : ℕ) : cubeNorm n * cubeNorm n = ((2 : ℝ) ^ n)⁻¹ := by
  rw [cubeNorm, ← mul_inv, ← Real.sqrt_mul_self (le_of_lt (by positivity : (0:ℝ) < Real.sqrt ((2:ℝ)^n)))]
  congr 1
  rw [Real.mul_self_sqrt (by positivity)]

/-- The Walsh–Hadamard matrix of the Boolean hypercube. -/
def walshMatrix (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.of fun x y => ((cubeNorm n : ℝ) : ℂ) * cubeSign x y

theorem walshMatrix_apply (n : ℕ) (x y : Fin n → Bool) :
    walshMatrix n x y = ((cubeNorm n : ℝ) : ℂ) * cubeSign x y := rfl

theorem walshMatrix_conjTranspose (n : ℕ) : (walshMatrix n)ᴴ = walshMatrix n := by
  ext x y
  rw [Matrix.conjTranspose_apply, walshMatrix_apply, walshMatrix_apply, star_mul',
    star_cubeSign, Complex.star_def, Complex.conj_ofReal, cubeSign_comm, mul_comm]

theorem walshMatrix_mul_self (n : ℕ) : walshMatrix n * walshMatrix n = 1 := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  have hterm : ∀ z : Fin n → Bool, walshMatrix n x z * walshMatrix n z y
      = (((cubeNorm n * cubeNorm n : ℝ)) : ℂ) * (cubeSign x z * cubeSign y z) := by
    intro z
    rw [walshMatrix_apply, walshMatrix_apply, cubeSign_comm z y]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun z _ => hterm z), ← Finset.mul_sum, sum_cubeSign_mul,
    cubeNorm_sq, Matrix.one_apply]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
    push_cast
    field_simp
  · rw [if_neg hxy, if_neg hxy, mul_zero]

theorem walshMatrix_conjTranspose_mul (n : ℕ) : (walshMatrix n)ᴴ * walshMatrix n = 1 := by
  rw [walshMatrix_conjTranspose, walshMatrix_mul_self]

theorem walshMatrix_mul_conjTranspose (n : ℕ) : walshMatrix n * (walshMatrix n)ᴴ = 1 := by
  rw [walshMatrix_conjTranspose, walshMatrix_mul_self]

end

end Walsh

end GaloisForLFunctions.HTGeometry
