import GaloisForLFunctions.HTGeometry.SimpleSpectrumEigenline

/-!
# Spectral blocks of a product grid

An operator diagonal in a product grid has, for each eigenvalue, a spectral projector whose diagonal
pattern is the indicator of a block of the grid.  For the blocks that occur in a `2 × 2` grid every
such pattern is decomposable, so a projector determines the local factor lines.

* a single grid point gives `δ_{i₀} ⊗ δ_{j₀}`;
* a whole row gives `δ_{i₀} ⊗ 1`, a whole column `1 ⊗ δ_{j₀}`;
* the whole grid gives `1 ⊗ 1`, which is scalar;
* the diagonal block of a `2 × 2` grid is not itself decomposable, but its centering — the
  projector minus half the identity — is `½ · s ⊗ s` with `s` the traceless sign vector.

Since a two-element block of a `2 × 2` grid is a row, a column, or a diagonal, these four patterns
exhaust the possibilities, and in every case `criticalHorizonSegreTensor_rigidity` fixes the local
factor lines.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {I J : Type*}

/-- The coordinate indicator of one index. -/
def indexIndicator [DecidableEq I] (i₀ : I) : I → K := fun i => if i = i₀ then 1 else 0

theorem indexIndicator_ne_zero [DecidableEq I] (i₀ : I) : (indexIndicator i₀ : I → K) ≠ 0 := by
  intro h
  have := congrFun h i₀
  simp [indexIndicator] at this

theorem one_ne_zero_fun [Nonempty I] : (fun _ : I => (1 : K)) ≠ 0 := by
  intro h
  have := congrFun h (Classical.arbitrary I)
  simp at this

/-! ### The decomposable block patterns -/

/-- A single grid point: the pattern of a rank-one product spectral projector. -/
theorem pointBlockPattern_eq_segreTensor [DecidableEq I] [DecidableEq J] (i₀ : I) (j₀ : J) :
    (fun i j => if i = i₀ ∧ j = j₀ then (1 : K) else 0 : Matrix I J K) =
      criticalHorizonSegreTensor (indexIndicator i₀) (indexIndicator j₀) := by
  funext i j
  by_cases hi : i = i₀ <;> by_cases hj : j = j₀ <;>
    simp [criticalHorizonSegreTensor, indexIndicator, hi, hj]

/-- A whole row. -/
theorem rowBlockPattern_eq_segreTensor [DecidableEq I] (i₀ : I) :
    (fun i _ => if i = i₀ then (1 : K) else 0 : Matrix I J K) =
      criticalHorizonSegreTensor (indexIndicator i₀) (fun _ => 1) := by
  funext i j
  by_cases hi : i = i₀ <;> simp [criticalHorizonSegreTensor, indexIndicator, hi]

/-- A whole column. -/
theorem columnBlockPattern_eq_segreTensor [DecidableEq J] (j₀ : J) :
    (fun _ j => if j = j₀ then (1 : K) else 0 : Matrix I J K) =
      criticalHorizonSegreTensor (fun _ => 1) (indexIndicator j₀) := by
  funext i j
  by_cases hj : j = j₀ <;> simp [criticalHorizonSegreTensor, indexIndicator, hj]

/-- The whole grid: the scalar pattern. -/
theorem fullBlockPattern_eq_segreTensor :
    (fun _ _ => (1 : K) : Matrix I J K) =
      criticalHorizonSegreTensor (fun _ => 1) (fun _ => 1) := by
  funext i j
  simp [criticalHorizonSegreTensor]

/-! ### The diagonal block of a `2 × 2` grid -/

/-- The traceless sign vector of a two-element index. -/
def checkerSign : Fin 2 → K := fun i => if i = 0 then 1 else -1

theorem sum_checkerSign : ∑ i, (checkerSign i : K) = 0 := by
  simp [checkerSign, Fin.sum_univ_two]

theorem checkerSign_ne_zero : (checkerSign : Fin 2 → K) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [checkerSign] at this

/-- The diagonal block of a `2 × 2` product grid. -/
def checkerBlockPattern : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => if i = j then 1 else 0

/-- **Centering makes the diagonal block decomposable.**  The diagonal projector of a `2 × 2`
product grid, minus half the scalar pattern, is `½ · s ⊗ s` for the traceless sign vector `s`. -/
theorem checkerBlockPattern_centered_eq_segreTensor (h2 : (2 : K) ≠ 0) :
    (checkerBlockPattern : Matrix (Fin 2) (Fin 2) K) -
        (2 : K)⁻¹ • criticalHorizonSegreTensor (fun _ => (1 : K)) (fun _ => (1 : K)) =
      (2 : K)⁻¹ • criticalHorizonSegreTensor checkerSign checkerSign := by
  have h2inv : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ h2]
  have hhalf : (1 : K) - (2 : K)⁻¹ = (2 : K)⁻¹ := by linear_combination -h2inv
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [checkerBlockPattern, criticalHorizonSegreTensor, checkerSign, hhalf]

/-! ### Classification of two-element blocks of a `2 × 2` grid -/

/-- A two-element block of the `2 × 2` grid is a row, a column, or a diagonal. -/
theorem twoElementBlock_cases {p q : Fin 2 × Fin 2} (hpq : p ≠ q) :
    (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ (p.2 = q.2 ∧ p.1 ≠ q.1) ∨ (p.1 ≠ q.1 ∧ p.2 ≠ q.2) := by
  revert hpq
  revert p q
  decide

/-! ### Rigidity of the local factor lines -/

/-- A point block fixes both local factor lines. -/
theorem pointBlock_factors_proportional [DecidableEq I] [DecidableEq J]
    {i₀ : I} {j₀ : J} {a : I → K} {b : J → K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : criticalHorizonSegreTensor a b =
      criticalHorizonSegreTensor (indexIndicator i₀) (indexIndicator j₀)) :
    (∃ α : K, α ≠ 0 ∧ a = α • indexIndicator i₀) ∧
      (∃ β : K, β ≠ 0 ∧ b = β • indexIndicator j₀) := by
  have h' : criticalHorizonSegreTensor a b =
      (1 : K) • criticalHorizonSegreTensor (indexIndicator i₀) (indexIndicator j₀) := by
    rw [one_smul]; exact h
  exact ⟨criticalHorizonSegreTensor_left_line ha hb h',
    criticalHorizonSegreTensor_right_line ha hb h'⟩

/-- A row block determines its local rank-one projector outright: the second factor is the constant
vector on both sides, so the first factors agree. -/
theorem rowBlock_left_cancel [Nonempty J] {a a' : I → K} (ha : a ≠ 0)
    (h : criticalHorizonSegreTensor a (fun _ : J => (1 : K)) =
      criticalHorizonSegreTensor a' (fun _ : J => (1 : K))) :
    a = a' :=
  criticalHorizonSegreTensor_left_cancel ha one_ne_zero_fun h

end GaloisForLFunctions.HTGeometry
