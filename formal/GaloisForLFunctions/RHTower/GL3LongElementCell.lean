import GaloisForLFunctions.RHTower.GL3CoxeterCell


/-!
# The long-element Bruhat cell of `SL₃(ℤ)` and its Kloosterman phases

The big cell consists of the matrices with `A = M₂₀ ≠ 0` and `D₂ = plk₂ = M₁₀M₂₁ − M₁₁M₂₀ ≠ 0`
(`InW0Cell`). Over `ℚ` it has the explicit Bruhat decomposition (`w0_bruhat`)
`M = n(M₁₀/A, (M₀₀B − M₀₁A)/D₂, M₀₀/A) · diag(1/D₂, −D₂/A, A) · w₀ · n(−plk₁/D₂, B/A, C/A)`,
where the `(0,2)` entry uses `det M = 1` together with the Plücker relation.

The simple-root coordinates of the two unipotent factors are the Kloosterman phases
`x₁ = M₁₀/A`, `x₂ = (M₀₀B − M₀₁A)/D₂`, `y₁ = −plk₁/D₂`, `y₂ = B/A`. Left and right multiplication by
`U(ℤ)` fix the moduli `A`, `D₂` and shift these phases by integers (`unip_mul_phases`,
`mul_unip_phases`). So `e(m₁x₁ + m₂x₂ + n₁y₁ + n₂y₂)` is a function on `U(ℤ)\cell/U(ℤ)`
(`w0Phase_unip_mul_unip`). Summing it over the double cosets with moduli `(A, D₂)` gives the
long-element Kloosterman sum of Bump–Friedberg–Goldfeld.
-/

open Matrix

namespace GaloisForLFunctions.RHTower.GL3

/-- The long Weyl element `w₀ = [[0,0,1],[0,1,0],[1,0,0]]`. -/
def w0 {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 3) R := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

/-- The big (long-element) Bruhat cell: bottom-left entry and bottom-left `2×2` minor nonzero. -/
def InW0Cell (M : Matrix (Fin 3) (Fin 3) ℤ) : Prop := M 2 0 ≠ 0 ∧ plk M 2 ≠ 0

section Cell
variable {M : Matrix (Fin 3) (Fin 3) ℤ}

/-- **Explicit Bruhat decomposition of the big cell over `ℚ`.** With `A = M₂₀`, `B = M₂₁`, `C = M₂₂`
and `D₂ = plk₂ = M₁₀M₂₁ − M₁₁M₂₀`,
`M = n(M₁₀/A, (M₀₀B − M₀₁A)/D₂, M₀₀/A) · diag(1/D₂, −D₂/A, A) · w₀ · n(−plk₁/D₂, B/A, C/A)`. -/
theorem w0_bruhat (hM : M.det = 1) (hc : InW0Cell M) :
    (M.map (Int.castRingHom ℚ)) =
      unip ((M 1 0 : ℚ) / M 2 0)
          (((M 0 0 : ℚ) * M 2 1 - M 0 1 * M 2 0) / ((plk M 2 : ℤ) : ℚ))
          ((M 0 0 : ℚ) / M 2 0) *
        !![(1 : ℚ) / ((plk M 2 : ℤ) : ℚ), 0, 0; 0, -((plk M 2 : ℤ) : ℚ) / M 2 0, 0;
          0, 0, (M 2 0 : ℚ)] * w0 *
        unip (-((plk M 1 : ℤ) : ℚ) / ((plk M 2 : ℤ) : ℚ)) ((M 2 1 : ℚ) / M 2 0)
          ((M 2 2 : ℚ) / M 2 0) := by
  have hA : (M 2 0 : ℚ) ≠ 0 := by exact_mod_cast hc.1
  have hD : ((plk M 2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hc.2
  have hD2 : ((plk M 2 : ℤ) : ℚ) = M 1 0 * M 2 1 - M 1 1 * M 2 0 := by simp [plk]
  have hD1 : ((plk M 1 : ℤ) : ℚ) = M 1 2 * M 2 0 - M 1 0 * M 2 2 := by simp [plk]
  have hD0 : ((plk M 0 : ℤ) : ℚ) = M 1 1 * M 2 2 - M 1 2 * M 2 1 := by simp [plk]
  have hdet : ((M 0 0 * plk M 0 + M 0 1 * plk M 1 + M 0 2 * plk M 2 : ℤ) : ℚ) = 1 := by
    have := det_eq_row0_dot_plk M
    rw [hM] at this
    simp only [dotProduct, Fin.sum_univ_three] at this
    exact_mod_cast this.symm
  have hrel : ((M 2 0 * plk M 0 + M 2 1 * plk M 1 + M 2 2 * plk M 2 : ℤ) : ℚ) = 0 := by
    have := botRow_dot_plk M
    simp only [dotProduct, Fin.sum_univ_three, botRow, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
    exact_mod_cast this
  push_cast at hdet
  rw [hD0, hD1, hD2] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unip, w0, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  all_goals (try simp only [hD1, hD2])
  all_goals first
    | ring1
    | linear_combination (M 2 0 : ℚ) * hdet

end Cell

/-! ### The Kloosterman phases of the big cell -/

/-- The numerator of the left `x₂`-phase: `M₀₀B − M₀₁A`. -/
def numX2 (M : Matrix (Fin 3) (Fin 3) ℤ) : ℤ := M 0 0 * M 2 1 - M 0 1 * M 2 0

/-- **Left `U(ℤ)`-translation** fixes the moduli `A`, `D₂` and `plk₁` and shifts the left phases by
integers: `M₁₀ ↦ M₁₀ + a₁A`, `M₀₀B − M₀₁A ↦ M₀₀B − M₀₁A + a₂D₂`. -/
theorem unip_mul_phases (a1 a2 a3 : ℤ) (M : Matrix (Fin 3) (Fin 3) ℤ) :
    (unip a1 a2 a3 * M) 2 0 = M 2 0 ∧ (unip a1 a2 a3 * M) 2 1 = M 2 1 ∧
      plk (unip a1 a2 a3 * M) = plk M ∧
      (unip a1 a2 a3 * M) 1 0 = M 1 0 + a1 * M 2 0 ∧
      numX2 (unip a1 a2 a3 * M) = numX2 M + a2 * plk M 2 := by
  refine ⟨?_, ?_, plk_unip_mul _ _ _ _, ?_, ?_⟩ <;>
    simp [unip, numX2, plk, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- **Right `U(ℤ)`-translation** fixes `A`, `D₂`, `M₁₀` and `M₀₀B − M₀₁A`, and shifts the right
phases by integers: `B ↦ B + b₂A`, `plk₁ ↦ plk₁ − b₁D₂`. -/
theorem mul_unip_phases (b1 b2 b3 : ℤ) (M : Matrix (Fin 3) (Fin 3) ℤ) :
    (M * unip b1 b2 b3) 2 0 = M 2 0 ∧ (M * unip b1 b2 b3) 1 0 = M 1 0 ∧
      plk (M * unip b1 b2 b3) 2 = plk M 2 ∧
      numX2 (M * unip b1 b2 b3) = numX2 M ∧
      (M * unip b1 b2 b3) 2 1 = M 2 1 + b2 * M 2 0 ∧
      plk (M * unip b1 b2 b3) 1 = plk M 1 - b1 * plk M 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [unip, numX2, plk, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The big-cell Kloosterman phase `m₁x₁ + m₂x₂ + n₁y₁ + n₂y₂` with
`x₁ = M₁₀/A`, `x₂ = (M₀₀B − M₀₁A)/D₂`, `y₁ = −plk₁/D₂`, `y₂ = B/A`. -/
noncomputable def w0Phase (m1 m2 n1 n2 : ℤ) (M : Matrix (Fin 3) (Fin 3) ℤ) : ℚ :=
  m1 * ((M 1 0 : ℚ) / M 2 0) + m2 * ((numX2 M : ℚ) / ((plk M 2 : ℤ) : ℚ)) +
    n1 * (-((plk M 1 : ℤ) : ℚ) / ((plk M 2 : ℤ) : ℚ)) + n2 * ((M 2 1 : ℚ) / M 2 0)

/-- **The phase is well defined on `U(ℤ)\cell/U(ℤ)` modulo `ℤ`.** -/
theorem w0Phase_unip_mul_unip (hc : InW0Cell M) (m1 m2 n1 n2 a1 a2 a3 b1 b2 b3 : ℤ) :
    w0Phase m1 m2 n1 n2 (unip a1 a2 a3 * M * unip b1 b2 b3) =
      w0Phase m1 m2 n1 n2 M + (m1 * a1 + m2 * a2 + n1 * b1 + n2 * b2 : ℤ) := by
  have hA : (M 2 0 : ℚ) ≠ 0 := by exact_mod_cast hc.1
  have hD : ((plk M 2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hc.2
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := mul_unip_phases b1 b2 b3 (unip a1 a2 a3 * M)
  obtain ⟨l1, l2, l3, l4, l5⟩ := unip_mul_phases a1 a2 a3 M
  simp only [w0Phase, r1, r2, r3, r4, r5, r6, l1, l2, l3, l4, l5]
  push_cast
  field_simp
  ring

end GaloisForLFunctions.RHTower.GL3
