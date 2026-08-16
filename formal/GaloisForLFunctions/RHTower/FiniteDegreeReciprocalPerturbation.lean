import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Finite-degree reciprocal tests are height-limited

A finite symmetric block whose quadratic form is coercive with constant `m` stays positive definite
under any symmetric perturbation whose entries are all at most `ε` in absolute value, provided
`card * ε < m`.

Applied to a shifted reciprocal Hankel block and the conjugate-pair perturbation

`P i j = μ (y ^ (i + j + r + 1) + conj y ^ (i + j + r + 1))`

of a nonreal atom `y` of weight `μ`, this shows that for every fixed degree there is a threshold
below which the block stays positive definite.  Fixed-degree positivity therefore cannot exclude
nonreal reciprocal atoms.
-/

noncomputable section

namespace RHTower

open scoped BigOperators Matrix

section Perturbation

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The quadratic form of a real matrix, bounded entrywise, is bounded by the entry bound times the
cardinality times the squared euclidean length. -/
theorem abs_dotProduct_mulVec_le (P : Matrix n n ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ i j, |P i j| ≤ ε) (x : n → ℝ) :
    |x ⬝ᵥ (P *ᵥ x)| ≤ ε * (Fintype.card n : ℝ) * ∑ i, x i ^ 2 := by
  have hexpand : x ⬝ᵥ (P *ᵥ x) = ∑ i, ∑ j, x i * P i j * x j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hstep : |∑ i, ∑ j, x i * P i j * x j| ≤ ε * (∑ i, |x i|) ^ 2 := by
    calc |∑ i, ∑ j, x i * P i j * x j| ≤ ∑ i, |∑ j, x i * P i j * x j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |x i * P i j * x j| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, ε * (|x i| * |x j|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          have h1 : |x i| * |P i j| * |x j| ≤ |x i| * ε * |x j| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hbound i j) (abs_nonneg (x i))) (abs_nonneg (x j))
          calc |x i| * |P i j| * |x j| ≤ |x i| * ε * |x j| := h1
            _ = ε * (|x i| * |x j|) := by ring
      _ = ε * (∑ i, |x i|) ^ 2 := by
          have hsq : (∑ i, |x i|) ^ 2 = ∑ i, ∑ j, |x i| * |x j| := by
            rw [sq, Finset.sum_mul_sum]
          rw [hsq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  have hcs : (∑ i, |x i|) ^ 2 ≤ (Fintype.card n : ℝ) * ∑ i, x i ^ 2 := by
    have hcheb := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset n)) (f := fun i => |x i|)
    simpa [sq_abs, Finset.card_univ] using hcheb
  rw [hexpand]
  calc |∑ i, ∑ j, x i * P i j * x j| ≤ ε * (∑ i, |x i|) ^ 2 := hstep
    _ ≤ ε * ((Fintype.card n : ℝ) * ∑ i, x i ^ 2) := by
        exact mul_le_mul_of_nonneg_left hcs hε
    _ = ε * (Fintype.card n : ℝ) * ∑ i, x i ^ 2 := by ring

omit [DecidableEq n] in
/-- A vector with a nonzero coordinate has positive squared euclidean length. -/
theorem sum_sq_pos_of_ne_zero {x : n → ℝ} (hx : x ≠ 0) : 0 < ∑ i, x i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  rw [← sq_abs]
  exact pow_pos (abs_pos.mpr hi) 2

/-- **Coercive perturbation stability.**  A symmetric block with coercivity constant `m` stays
positive definite under any symmetric perturbation with entries bounded by `ε`, provided
`card * ε < m`. -/
theorem posDef_add_of_coercive (B P : Matrix n n ℝ)
    (hB : B.IsHermitian) (hP : P.IsHermitian) {m ε : ℝ} (hε : 0 ≤ ε)
    (hm : ∀ x : n → ℝ, m * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (B *ᵥ x))
    (hbound : ∀ i j, |P i j| ≤ ε)
    (hlt : ε * (Fintype.card n : ℝ) < m) :
    (B + P).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hB.add hP) fun x hx => ?_
  have hsum : 0 < ∑ i, x i ^ 2 := sum_sq_pos_of_ne_zero hx
  have hsplit : star x ⬝ᵥ ((B + P) *ᵥ x) = x ⬝ᵥ (B *ᵥ x) + x ⬝ᵥ (P *ᵥ x) := by
    simp [Matrix.add_mulVec, dotProduct_add, star_trivial]
  have hbnd := abs_dotProduct_mulVec_le P hε hbound x
  have habs : -(ε * (Fintype.card n : ℝ) * ∑ i, x i ^ 2) ≤ x ⬝ᵥ (P *ᵥ x) :=
    neg_le_of_abs_le hbnd
  have hBcoer := hm x
  rw [hsplit]
  nlinarith [hBcoer, habs, hsum, hlt]

end Perturbation

section ReciprocalBlocks

variable {d : ℕ}

/-- The conjugate-pair perturbation of the `r`-shifted reciprocal Hankel block. -/
def conjugatePairPerturbation (μ : ℝ) (y : ℂ) (r d : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => μ * (2 * (y ^ ((i : ℕ) + (j : ℕ) + r + 1)).re)

theorem conjugatePairPerturbation_isHermitian (μ : ℝ) (y : ℂ) (r d : ℕ) :
    (conjugatePairPerturbation μ y r d).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [conjugatePairPerturbation, star_trivial]
  rw [show (j : ℕ) + (i : ℕ) = (i : ℕ) + (j : ℕ) from Nat.add_comm _ _]

/-- Entrywise bound for the conjugate-pair perturbation inside the unit reciprocal disc. -/
theorem abs_conjugatePairPerturbation_le {μ : ℝ} (hμ : 0 ≤ μ) {y : ℂ} (hy : ‖y‖ ≤ 1)
    (r d : ℕ) (i j : Fin (d + 1)) :
    |conjugatePairPerturbation μ y r d i j| ≤ 2 * μ * ‖y‖ := by
  have hk : 1 ≤ (i : ℕ) + (j : ℕ) + r + 1 := by omega
  have hre : |(y ^ ((i : ℕ) + (j : ℕ) + r + 1)).re| ≤ ‖y‖ ^ ((i : ℕ) + (j : ℕ) + r + 1) := by
    calc |(y ^ ((i : ℕ) + (j : ℕ) + r + 1)).re| ≤ ‖y ^ ((i : ℕ) + (j : ℕ) + r + 1)‖ :=
          Complex.abs_re_le_norm _
      _ = ‖y‖ ^ ((i : ℕ) + (j : ℕ) + r + 1) := by rw [norm_pow]
  have hpow : ‖y‖ ^ ((i : ℕ) + (j : ℕ) + r + 1) ≤ ‖y‖ := by
    calc ‖y‖ ^ ((i : ℕ) + (j : ℕ) + r + 1) ≤ ‖y‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg y) hy hk
      _ = ‖y‖ := pow_one _
  have hfinal : |(y ^ ((i : ℕ) + (j : ℕ) + r + 1)).re| ≤ ‖y‖ := le_trans hre hpow
  simp only [conjugatePairPerturbation, abs_mul, abs_two]
  rw [abs_of_nonneg hμ]
  nlinarith [hfinal, abs_nonneg (y ^ ((i : ℕ) + (j : ℕ) + r + 1)).re, norm_nonneg y]

/-- **Finite-degree blindness.**  For a fixed degree, a coercive shifted reciprocal Hankel block
stays positive definite after adding a sufficiently small nonreal conjugate pair. -/
theorem posDef_add_conjugatePairPerturbation
    (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hB : B.IsHermitian) {m μ : ℝ} (hμ : 0 ≤ μ)
    (hm : ∀ x : Fin (d + 1) → ℝ, m * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (B *ᵥ x))
    {y : ℂ} (hy : ‖y‖ ≤ 1) (r : ℕ)
    (hsmall : 2 * μ * ((d : ℝ) + 1) * ‖y‖ < m) :
    (B + conjugatePairPerturbation μ y r d).PosDef := by
  refine posDef_add_of_coercive B (conjugatePairPerturbation μ y r d) hB
    (conjugatePairPerturbation_isHermitian μ y r d)
    (by positivity) hm (abs_conjugatePairPerturbation_le hμ hy r d) ?_
  have hcard : (Fintype.card (Fin (d + 1)) : ℝ) = (d : ℝ) + 1 := by
    simp
  rw [hcard]
  nlinarith [hsmall]

end ReciprocalBlocks

end RHTower
