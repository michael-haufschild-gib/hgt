import GaloisForLFunctions.RHTower.GL3PluckerParam
import Mathlib.Data.Rat.Cast.Lemmas

open Matrix

/-!
# The Coxeter cell of `w₃` in `SL₃(ℤ)`

The Bruhat cell of the 3-cycle `w₃ = [[0,1,0],[0,0,1],[1,0,0]]` consists of the matrices whose
bottom-left entry `A = M₂₀` is nonzero and whose bottom `(0,1)`-minor `plk₂` vanishes (`InW3Cell`).
For `M ∈ SL₃(ℤ)` in this cell the remaining Plücker coordinate `D = plk₁ = M₁₂M₂₀ − M₁₀M₂₂` is
nonzero (`plk1_ne_zero`), `p₀ = plk₀` and `D` are coprime (`cell_coprime`, from `det = M₀₀p₀ + M₀₁D`),
and `D ∣ A` (`plk1_dvd`, from the Plücker relation `Ap₀ + BD = 0`). These are the degenerate
moduli of the `w₃` Kloosterman sums.

`w3_bruhat` gives the explicit Bruhat decomposition over `ℚ`:
`M = n(M₁₀/A, (M₀₂A − M₀₀C)/D, M₀₀/A) · diag(1/D, D/A, A) · w₃ · n(0, B/A, C/A)`.
The left and right unipotent parameters are the Kloosterman phases.
-/

namespace GaloisForLFunctions.RHTower.GL3

/-- The 3-cycle Weyl element `w₃ = [[0,1,0],[0,0,1],[1,0,0]]`. -/
def w3 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- The Coxeter cell of `w₃` in Plücker terms: bottom-left entry nonzero and vanishing minor on the
first two columns of the bottom two rows. -/
def InW3Cell (M : Matrix (Fin 3) (Fin 3) ℤ) : Prop := M 2 0 ≠ 0 ∧ plk M 2 = 0

section Cell
variable {M : Matrix (Fin 3) (Fin 3) ℤ} (hM : M.det = 1) (hc : InW3Cell M)
include hM hc

/-- In the `w₃`-cell the middle Plücker coordinate `D = M₁₂M₂₀ − M₁₀M₂₂` is nonzero. -/
theorem plk1_ne_zero : plk M 1 ≠ 0 := by
  intro h1
  have hrel := botRow_dot_plk M
  obtain ⟨hA, h2⟩ := hc
  simp only [dotProduct, Fin.sum_univ_three, botRow, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h1, h2, mul_zero, add_zero] at hrel
  have hp0 : plk M 0 = 0 := by
    rcases mul_eq_zero.1 hrel with h | h
    · exact absurd h hA
    · exact h
  have hdet := det_eq_row0_dot_plk M
  rw [hM] at hdet
  simp only [dotProduct, Fin.sum_univ_three, hp0, h1, h2, mul_zero, add_zero] at hdet
  exact one_ne_zero hdet

omit hM in
/-- The Plücker relation in the cell: `A · p₀ + B · D = 0`. -/
theorem cell_rel : M 2 0 * plk M 0 + M 2 1 * plk M 1 = 0 := by
  have hrel := botRow_dot_plk M
  simp only [dotProduct, Fin.sum_univ_three, botRow, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hc.2, mul_zero, add_zero] at hrel
  exact hrel

/-- The determinant in the cell: `M₀₀ p₀ + M₀₁ D = 1`. -/
theorem cell_det : M 0 0 * plk M 0 + M 0 1 * plk M 1 = 1 := by
  have hdet := det_eq_row0_dot_plk M
  rw [hM] at hdet
  simp only [dotProduct, Fin.sum_univ_three, hc.2, mul_zero, add_zero] at hdet
  exact hdet.symm

/-- `p₀` and `D` are coprime. -/
theorem cell_coprime : IsCoprime (plk M 0) (plk M 1) :=
  ⟨M 0 0, M 0 1, cell_det hM hc⟩

/-- **Divisibility in the Coxeter cell:** `D ∣ A`. -/
theorem plk1_dvd : plk M 1 ∣ M 2 0 := by
  have hcop := cell_coprime hM hc
  have hrel := cell_rel hc
  -- `D ∣ A p₀` and `gcd(p₀, D) = 1`
  have h1 : plk M 1 ∣ M 2 0 * plk M 0 := ⟨-(M 2 1), by linear_combination hrel⟩
  exact (IsCoprime.symm hcop).dvd_of_dvd_mul_right h1

/-- **Explicit Bruhat decomposition over `ℚ`.** In the `w₃`-cell, with `A = M₂₀`, `B = M₂₁`,
`C = M₂₂`, `D = plk₁`,
`M = n(M₁₀/A, (M₀₂A − M₀₀C)/D, M₀₀/A) · diag(1/D, D/A, A) · w₃ · n(0, B/A, C/A)`. -/
theorem w3_bruhat :
    (M.map (Int.castRingHom ℚ)) =
      unip ((M 1 0 : ℚ) / M 2 0) (((M 0 2 : ℚ) * M 2 0 - M 0 0 * M 2 2) / ((plk M 1 : ℤ) : ℚ))
          ((M 0 0 : ℚ) / M 2 0) *
        !![(1 : ℚ) / ((plk M 1 : ℤ) : ℚ), 0, 0; 0, ((plk M 1 : ℤ) : ℚ) / M 2 0, 0; 0, 0, (M 2 0 : ℚ)] * w3 *
        unip 0 ((M 2 1 : ℚ) / M 2 0) ((M 2 2 : ℚ) / M 2 0) := by
  have hA : (M 2 0 : ℚ) ≠ 0 := by exact_mod_cast hc.1
  have hD : ((plk M 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast plk1_ne_zero hM hc
  have h2 : ((M 1 0 * M 2 1 - M 1 1 * M 2 0 : ℤ) : ℚ) = 0 := by
    have := hc.2; simp only [plk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
    exact_mod_cast this
  have hDdef : ((plk M 1 : ℤ) : ℚ) = M 1 2 * M 2 0 - M 1 0 * M 2 2 := by
    simp [plk]
  have hdet : ((M 0 0 * plk M 0 + M 0 1 * plk M 1 : ℤ) : ℚ) = 1 := by
    exact_mod_cast cell_det hM hc
  have hrel : ((M 2 0 * plk M 0 + M 2 1 * plk M 1 : ℤ) : ℚ) = 0 := by
    exact_mod_cast cell_rel hc
  push_cast at h2 hdet hrel
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unip, w3, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  all_goals first
    | ring1
    | linear_combination -h2
    | linear_combination hDdef
    | linear_combination -hDdef
    | linear_combination h2
    | linear_combination (M 2 0 : ℚ) * hdet - (M 0 0 : ℚ) * hrel

end Cell

end GaloisForLFunctions.RHTower.GL3
