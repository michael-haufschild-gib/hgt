import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

open Matrix

/-!
# Plücker coordinates of `3 × 3` matrices

For `M ∈ Mat₃(R)` the bottom row `botRow M` and the Plücker vector `plk M = row₁ × row₂` of the bottom
`2 × 3` block are invariant under left multiplication by upper unipotent matrices (`botRow_unip_mul`,
`plk_unip_mul`). They satisfy the Plücker relation `botRow M · plk M = 0` (`botRow_dot_plk`), and
`det M = row₀ · plk M` (`det_eq_row0_dot_plk`). Under right multiplication `botRow (Mg) = botRow M · g`
and `plk (Mg) = plk M · (adj g)ᵀ` (`botRow_mul`, `plk_mul`).

Conversely the pair determines the left unipotent coset among determinant-one matrices over any
commutative ring (`exists_unip_of_plucker_det_one`), and among invertible matrices of equal determinant
over a field (`exists_unip_of_plucker`). For `R = ℤ` this is the injectivity half of the parametrisation
of `U(ℤ)\SL₃(ℤ)` by coprime pairs `(A₁,B₁,C₁), (A₂,B₂,C₂)` with `A₁C₂ + B₁B₂ + C₁A₂ = 0`
(Bump–Friedberg–Goldfeld), which organises the Poincaré series and Kloosterman sums of `SL₃(ℤ)`.
-/

namespace GaloisForLFunctions.RHTower.GL3

section Plucker
variable {R : Type*} [CommRing R]

/-- The bottom row `(M₂₀, M₂₁, M₂₂)`. -/
def botRow (M : Matrix (Fin 3) (Fin 3) R) : Fin 3 → R := ![M 2 0, M 2 1, M 2 2]

/-- The Plücker vector of the bottom two rows: the cross product `row₁ × row₂`. -/
def plk (M : Matrix (Fin 3) (Fin 3) R) : Fin 3 → R :=
  ![M 1 1 * M 2 2 - M 1 2 * M 2 1, M 1 2 * M 2 0 - M 1 0 * M 2 2, M 1 0 * M 2 1 - M 1 1 * M 2 0]

theorem plk_eq_cross (M : Matrix (Fin 3) (Fin 3) R) : plk M = crossProduct (M 1) (M 2) := by
  ext i; fin_cases i <;> simp [plk, crossProduct]

/-- **Plücker relation.** The bottom row is orthogonal to the bottom Plücker vector. -/
theorem botRow_dot_plk (M : Matrix (Fin 3) (Fin 3) R) : botRow M ⬝ᵥ plk M = 0 := by
  simp [botRow, plk, dotProduct, Fin.sum_univ_three]; ring

/-- The upper unipotent matrix `n(a₁,a₂,a₃)` over `R`. -/
def unip (a1 a2 a3 : R) : Matrix (Fin 3) (Fin 3) R := !![1, a2, a3; 0, 1, a1; 0, 0, 1]

theorem botRow_unip_mul (a1 a2 a3 : R) (M : Matrix (Fin 3) (Fin 3) R) :
    botRow (unip a1 a2 a3 * M) = botRow M := by
  ext i; fin_cases i <;> simp [botRow, unip, Matrix.mul_apply, Fin.sum_univ_three]

theorem plk_unip_mul (a1 a2 a3 : R) (M : Matrix (Fin 3) (Fin 3) R) :
    plk (unip a1 a2 a3 * M) = plk M := by
  ext i; fin_cases i <;> simp [plk, unip, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- Right multiplication: the bottom row transforms by `g`. -/
theorem botRow_mul (M g : Matrix (Fin 3) (Fin 3) R) : botRow (M * g) = botRow M ᵥ* g := by
  ext i; fin_cases i <;> simp [botRow, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_three]

/-- Right multiplication: the Plücker vector transforms by the transposed adjugate. -/
theorem plk_mul (M g : Matrix (Fin 3) (Fin 3) R) : plk (M * g) = plk M ᵥ* (adjugate g)ᵀ := by
  ext i; fin_cases i <;>
    simp [plk, Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_three, adjugate_fin_three] <;> ring

/-- The determinant as the pairing of the top row with the Plücker vector. -/
theorem det_eq_row0_dot_plk (M : Matrix (Fin 3) (Fin 3) R) :
    M.det = M 0 ⬝ᵥ plk M := by
  rw [det_fin_three]; simp [plk, dotProduct, Fin.sum_univ_three]; ring

end Plucker

section Uniqueness
variable {K : Type*} [Field K]

/-- **Plücker data determine the left unipotent coset.** Two invertible matrices with the same
determinant, bottom row and bottom Plücker vector differ by a left upper unipotent factor. -/
theorem exists_unip_of_plucker {M M' : Matrix (Fin 3) (Fin 3) K} (hdet : M'.det = M.det)
    (hM : M.det ≠ 0) (hb : botRow M' = botRow M) (hp : plk M' = plk M) :
    ∃ a1 a2 a3 : K, M' = unip a1 a2 a3 * M := by
  have hU : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  set N := M' * M⁻¹ with hNdef
  have hNM : N * M = M' := by rw [hNdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul M hU, Matrix.mul_one]
  have hinj : Function.Injective fun v : Fin 3 → K => v ᵥ* M :=
    vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det M).2 hU)
  have row : ∀ i j, M' i j = N i 0 * M 0 j + N i 1 * M 1 j + N i 2 * M 2 j := by
    intro i j; rw [← hNM]; simp [Matrix.mul_apply, Fin.sum_univ_three]
  -- bottom row of `N`
  have hb2 : ∀ j, M' 2 j = M 2 j := by
    intro j; have h1 := congrFun hb j; fin_cases j <;> simpa [botRow] using h1
  have hbot : N 2 = ![0, 0, 1] := by
    apply hinj
    ext j
    have h := (row 2 j).symm.trans (hb2 j)
    simp only [vecMul, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination h
  have n20 : N 2 0 = 0 := by simpa using congrFun hbot 0
  have n21 : N 2 1 = 0 := by simpa using congrFun hbot 1
  have n22 : N 2 2 = 1 := by simpa using congrFun hbot 2
  -- middle row via the Plücker vector
  have p0 := congrFun hp 0
  have p1 := congrFun hp 1
  have p2 := congrFun hp 2
  simp only [plk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at p0 p1 p2
  simp only [hb2, row 1 0, row 1 1, row 1 2] at p0 p1 p2
  have hdetM : M.det = M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 +
      M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0 := det_fin_three M
  have e10 : N 1 0 * M.det = 0 := by
    rw [hdetM]; linear_combination (-(M 1 0)) * p0 + (-(M 1 1)) * p1 + (-(M 1 2)) * p2
  have e11 : (N 1 1 - 1) * M.det = 0 := by
    rw [hdetM]; linear_combination (M 0 0) * p0 + (M 0 1) * p1 + (M 0 2) * p2
  have n10 : N 1 0 = 0 := by rcases mul_eq_zero.1 e10 with h | h; exact h; exact absurd h hM
  have n11 : N 1 1 = 1 := by
    rcases mul_eq_zero.1 e11 with h | h; exact sub_eq_zero.1 h; exact absurd h hM
  -- top-left entry from the determinant
  have hdetN : N.det = 1 := by
    have := congrArg Matrix.det hNM
    rw [Matrix.det_mul, hdet] at this
    exact mul_right_cancel₀ hM (by rw [this, one_mul])
  have n00 : N 0 0 = 1 := by
    rw [det_fin_three, n20, n21, n22, n10, n11] at hdetN; linear_combination hdetN
  refine ⟨N 1 2, N 0 1, N 0 2, ?_⟩
  rw [← hNM]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unip, n00, n10, n11, n20, n21, n22]

end Uniqueness

section UniquenessRing
variable {R : Type*} [CommRing R]

/-- **Plücker data determine the left `U(R)`-coset in `SL₃(R)`.** Over any commutative ring, two
determinant-one matrices with the same bottom row and bottom Plücker vector satisfy
`M' = n(a₁,a₂,a₃) · M` with `aᵢ ∈ R`; for `R = ℤ` this is the injectivity of
`U(ℤ)\SL₃(ℤ) → (bottom row, Plücker vector)`. -/
theorem exists_unip_of_plucker_det_one {M M' : Matrix (Fin 3) (Fin 3) R} (hM : M.det = 1)
    (hM' : M'.det = 1) (hb : botRow M' = botRow M) (hp : plk M' = plk M) :
    ∃ a1 a2 a3 : R, M' = unip a1 a2 a3 * M := by
  set N := M' * adjugate M with hNdef
  have hNM : N * M = M' := by
    rw [hNdef, Matrix.mul_assoc, adjugate_mul, hM, one_smul, Matrix.mul_one]
  have hU : IsUnit M.det := by rw [hM]; exact isUnit_one
  have hinj : Function.Injective fun v : Fin 3 → R => v ᵥ* M :=
    vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det M).2 hU)
  have row : ∀ i j, M' i j = N i 0 * M 0 j + N i 1 * M 1 j + N i 2 * M 2 j := by
    intro i j; rw [← hNM]; simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hb2 : ∀ j, M' 2 j = M 2 j := by
    intro j; have h1 := congrFun hb j; fin_cases j <;> simpa [botRow] using h1
  have hbot : N 2 = ![0, 0, 1] := by
    apply hinj
    ext j
    have h := (row 2 j).symm.trans (hb2 j)
    simp only [vecMul, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination h
  have n20 : N 2 0 = 0 := by simpa using congrFun hbot 0
  have n21 : N 2 1 = 0 := by simpa using congrFun hbot 1
  have n22 : N 2 2 = 1 := by simpa using congrFun hbot 2
  have p0 := congrFun hp 0
  have p1 := congrFun hp 1
  have p2 := congrFun hp 2
  simp only [plk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at p0 p1 p2
  simp only [hb2, row 1 0, row 1 1, row 1 2] at p0 p1 p2
  have hdetM := det_fin_three M
  rw [hM] at hdetM
  have n10 : N 1 0 = 0 := by
    linear_combination (N 1 0) * hdetM + (-(M 1 0)) * p0 + (-(M 1 1)) * p1 + (-(M 1 2)) * p2
  have n11 : N 1 1 = 1 := by
    linear_combination (N 1 1 - 1) * hdetM + (M 0 0) * p0 + (M 0 1) * p1 + (M 0 2) * p2
  have hdetN : N.det = 1 := by
    have := congrArg Matrix.det hNM
    rw [Matrix.det_mul, hM, hM', mul_one] at this
    exact this
  have n00 : N 0 0 = 1 := by
    rw [det_fin_three, n20, n21, n22, n10, n11] at hdetN; linear_combination hdetN
  refine ⟨N 1 2, N 0 1, N 0 2, ?_⟩
  rw [← hNM]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unip, n00, n10, n11, n20, n21, n22]

end UniquenessRing

end GaloisForLFunctions.RHTower.GL3
