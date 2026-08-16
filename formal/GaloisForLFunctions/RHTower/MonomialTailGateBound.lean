import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# The monomial tail gate is exponentially weak in the degree

For a positive bulk supported in `(0, R]` the shifted Hankel block

`B d = [L (i + j + 1)]`,  `L k = ∑ i, mass i * x i ^ k`,

has its last diagonal entry equal to `L (2d + 1)`, and every coercivity constant of its quadratic
form is bounded by that entry.  Since every atom is at most `R`,

`L (2d + 1) ≤ R ^ (2d) * L 1`.

So any tail gate of the form `η < λ_min (B d)` forces `η < R ^ (2d) * L 1`: in the monomial
coefficient norm the admissible tail size decays exponentially in the degree.
-/

noncomputable section

namespace RHTower

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι]

/-- Shifted moment of a positive bulk. -/
def shiftedBulkMoment (mass x : ι → ℝ) (k : ℕ) : ℝ := ∑ i, mass i * x i ^ k

/-- The shifted Hankel block of a positive bulk. -/
def shiftedHankelBlock (mass x : ι → ℝ) (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => shiftedBulkMoment mass x ((i : ℕ) + (j : ℕ) + 1)

theorem shiftedHankelBlock_last (mass x : ι → ℝ) (d : ℕ) :
    shiftedHankelBlock mass x d (Fin.last d) (Fin.last d) =
      shiftedBulkMoment mass x (2 * d + 1) := by
  simp only [shiftedHankelBlock, Fin.val_last]
  congr 1
  ring

/-- Any coercivity constant of a quadratic form is bounded by every diagonal entry. -/
theorem coercivity_le_diagonal {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {m : ℝ}
    (hm : ∀ v : Fin n → ℝ, m * ∑ i, v i ^ 2 ≤ v ⬝ᵥ (B *ᵥ v)) (j : Fin n) :
    m ≤ B j j := by
  set e : Fin n → ℝ := Pi.single j 1 with he
  have hv := hm e
  have hnorm : (∑ i, e i ^ 2) = 1 := by
    simp [he, Pi.single_apply, Finset.sum_ite_eq']
  have hquad : e ⬝ᵥ (B *ᵥ e) = B j j := by
    simp [he, dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']
  rw [hnorm, hquad, mul_one] at hv
  exact hv

/-- On a bulk supported in `(0, R]`, the high shifted moment is exponentially small relative to the
first one. -/
theorem shiftedBulkMoment_le_pow (mass x : ι → ℝ) {R : ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (hx : ∀ i, 0 < x i) (hxR : ∀ i, x i ≤ R) (d : ℕ) :
    shiftedBulkMoment mass x (2 * d + 1) ≤ R ^ (2 * d) * shiftedBulkMoment mass x 1 := by
  rw [shiftedBulkMoment, shiftedBulkMoment, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hxpow : x i ^ (2 * d) ≤ R ^ (2 * d) :=
    pow_le_pow_left₀ (le_of_lt (hx i)) (hxR i) (2 * d)
  have hsplit : mass i * x i ^ (2 * d + 1) = (mass i * x i ^ 1) * x i ^ (2 * d) := by
    ring
  rw [hsplit]
  have hfac : 0 ≤ mass i * x i ^ 1 :=
    mul_nonneg (hmass i) (pow_nonneg (le_of_lt (hx i)) 1)
  calc (mass i * x i ^ 1) * x i ^ (2 * d) ≤ (mass i * x i ^ 1) * R ^ (2 * d) :=
        mul_le_mul_of_nonneg_left hxpow hfac
    _ = R ^ (2 * d) * (mass i * x i ^ 1) := by ring

/-- **Monomial tail gate bound.**  Any coercivity constant of the shifted Hankel block is at most
`R ^ (2d)` times the first shifted moment, so a tail gate `η < λ_min` forces an exponentially small
admissible tail. -/
theorem coercivity_shiftedHankelBlock_le (mass x : ι → ℝ) {R : ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (hx : ∀ i, 0 < x i) (hxR : ∀ i, x i ≤ R) (d : ℕ) {m : ℝ}
    (hm : ∀ v : Fin (d + 1) → ℝ,
      m * ∑ i, v i ^ 2 ≤ v ⬝ᵥ ((shiftedHankelBlock mass x d) *ᵥ v)) :
    m ≤ R ^ (2 * d) * shiftedBulkMoment mass x 1 := by
  have hdiag := coercivity_le_diagonal (shiftedHankelBlock mass x d) hm (Fin.last d)
  rw [shiftedHankelBlock_last] at hdiag
  exact le_trans hdiag (shiftedBulkMoment_le_pow mass x hmass hx hxR d)

/-- The gate is vacuous once the tail exceeds the exponentially decaying bound. -/
theorem not_coercivity_of_tail_ge (mass x : ι → ℝ) {R : ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (hx : ∀ i, 0 < x i) (hxR : ∀ i, x i ≤ R) (d : ℕ) {η : ℝ}
    (hη : R ^ (2 * d) * shiftedBulkMoment mass x 1 ≤ η) :
    ¬ ∃ m : ℝ, η < m ∧ ∀ v : Fin (d + 1) → ℝ,
      m * ∑ i, v i ^ 2 ≤ v ⬝ᵥ ((shiftedHankelBlock mass x d) *ᵥ v) := by
  rintro ⟨m, hlt, hm⟩
  have := coercivity_shiftedHankelBlock_le mass x hmass hx hxR d hm
  linarith

end RHTower
