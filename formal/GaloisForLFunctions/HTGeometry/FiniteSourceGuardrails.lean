import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum

/-!
# Finite source-transfer guardrails

This file packages three elementary obstructions used by the Hankel and
boundary-source routes: distinct evaluation boundaries have distinct rank-one
kernels, arbitrary positive weighting transfers PSD exactly when each point
kernel is PSD, and moving a positive Hankel atom creates an indefinite tangent.
-/

open scoped BigOperators Matrix ComplexConjugate
open Polynomial

namespace HTGeometry

noncomputable section

/-- The degree-one polynomial vanishing at `a` remains visible at every distinct point `b`. -/
theorem eval_X_sub_C_self_other {a b : ℂ} (hab : a ≠ b) :
    (X - C a : Polynomial ℂ).eval a = 0 ∧
      (X - C a : Polynomial ℂ).eval b ≠ 0 := by
  constructor
  · simp
  · simpa [sub_ne_zero] using hab.symm

/-- Evaluation at distinct points has different kernels. -/
theorem eval_kernels_ne {a b : ℂ} (hab : a ≠ b) :
    {p : Polynomial ℂ | p.eval a = 0} ≠ {p : Polynomial ℂ | p.eval b = 0} := by
  intro h
  have ha : (X - C a : Polynomial ℂ) ∈ {p : Polynomial ℂ | p.eval a = 0} := by
    simp
  have hb : (X - C a : Polynomial ℂ) ∈ {p : Polynomial ℂ | p.eval b = 0} := by
    rw [← h]
    exact ha
  exact (eval_X_sub_C_self_other hab).2 hb

/-- Evaluation at distinct points is not related by scalar multiplication. -/
theorem eval_not_scalar_multiple {a b : ℂ} (hab : a ≠ b) :
    ¬ ∃ c : ℂ, (fun p : Polynomial ℂ => p.eval a) =
      fun p : Polynomial ℂ => c * p.eval b := by
  rintro ⟨c, h⟩
  have hp := congrFun h (X - C b)
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  simp at hp
  exact hne hp

/-- The rank-one Hermitian forms induced by evaluation at distinct points have different zero
sets. -/
theorem eval_normSq_zero_sets_ne {a b : ℂ} (hab : a ≠ b) :
    {p : Polynomial ℂ | Complex.normSq (p.eval a) = 0} ≠
      {p : Polynomial ℂ | Complex.normSq (p.eval b) = 0} := by
  simpa only [Complex.normSq_eq_zero] using eval_kernels_ne hab

/-- The pole boundary `-4` and first-trivial-zero boundary `-4/25` are distinct in all three
rank-one senses. -/
theorem pole_firstTrivialZero_boundary_nontransfer :
    {p : Polynomial ℂ | p.eval (-4) = 0} ≠
        {p : Polynomial ℂ | p.eval (-(4 / 25)) = 0} ∧
      (¬ ∃ c : ℂ, (fun p : Polynomial ℂ => p.eval (-4)) =
        fun p : Polynomial ℂ => c * p.eval (-(4 / 25))) ∧
      {p : Polynomial ℂ | Complex.normSq (p.eval (-4)) = 0} ≠
        {p : Polynomial ℂ | Complex.normSq (p.eval (-(4 / 25))) = 0} := by
  have hne : (-4 : ℂ) ≠ -(4 / 25) := by norm_num
  exact ⟨eval_kernels_ne hne, eval_not_scalar_multiple hne,
    eval_normSq_zero_sets_ne hne⟩

/-- A finite positive weighting of pointwise source kernels. -/
noncomputable def weightedKernel {X ι : Type*} [Fintype X]
    (K : X → Matrix ι ι ℝ) (w : X → ℝ) : Matrix ι ι ℝ :=
  ∑ x, w x • K x

/-- Every positive weighting is PSD exactly when every point kernel is PSD. -/
theorem weightedKernel_posSemidef_iff {X ι : Type*} [Fintype X] [Fintype ι]
    (K : X → Matrix ι ι ℝ) :
    (∀ w : X → ℝ, (∀ x, 0 ≤ w x) → (weightedKernel K w).PosSemidef) ↔
      ∀ x, (K x).PosSemidef := by
  classical
  constructor
  · intro hall x
    let w : X → ℝ := fun y => if y = x then 1 else 0
    have hw : ∀ y, 0 ≤ w y := by
      intro y
      by_cases h : y = x <;> simp [w, h]
    have hs := hall w hw
    simpa [weightedKernel, w] using hs
  · intro hpoint w hw
    unfold weightedKernel
    exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add)
      Matrix.PosSemidef.zero (fun x _ => (hpoint x).smul (hw x))

/-- A non-PSD point kernel is exposed by a nonnegative point-mass weighting. -/
theorem exists_nonnegative_weight_not_posSemidef_of_pointwise
    {X ι : Type*} [Fintype X] [Fintype ι]
    (K : X → Matrix ι ι ℝ) {x : X} (hx : ¬ (K x).PosSemidef) :
    ∃ w : X → ℝ, (∀ y, 0 ≤ w y) ∧ ¬ (weightedKernel K w).PosSemidef := by
  classical
  let w : X → ℝ := fun y => if y = x then 1 else 0
  refine ⟨w, ?_, ?_⟩
  · intro y
    by_cases h : y = x <;> simp [w, h]
  · simpa [weightedKernel, w] using hx

/-- The rank-one Hankel matrix of an atom of mass `m` at `r`. -/
def hankelAtom (d : ℕ) (m r : ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => m * r ^ ((i : ℕ) + (j : ℕ))

/-- A nonnegative atom gives a positive-semidefinite Hankel matrix. -/
theorem hankelAtom_posSemidef (d : ℕ) (m r : ℝ) (hm : 0 ≤ m) :
    (hankelAtom d m r).PosSemidef := by
  let v : Matrix (Fin (d + 1)) (Fin 1) ℝ := Matrix.of fun i _ => r ^ (i : ℕ)
  have heq : hankelAtom d m r = m • (v * vᴴ) := by
    ext i j
    simp [hankelAtom, v, Matrix.mul_apply, pow_add]
  rw [heq]
  exact (Matrix.posSemidef_self_mul_conjTranspose v).smul hm

/-- The quadratic form obtained by differentiating a mass-`m` atom at position `r`. -/
def hankelAtomDisplacementTangent (m r : ℝ) (q : Polynomial ℝ) : ℝ :=
  2 * m * q.eval r * q.derivative.eval r

def hankelAtomDisplacementPositiveWitness (r : ℝ) : Polynomial ℝ :=
  C 1 * X + C (1 - r)

def hankelAtomDisplacementNegativeWitness (r : ℝ) : Polynomial ℝ :=
  C (-1) * X + C (1 + r)

theorem hankelAtomDisplacementPositiveWitness_degree (r : ℝ) :
    (hankelAtomDisplacementPositiveWitness r).natDegree ≤ 1 := by
  simpa [hankelAtomDisplacementPositiveWitness] using
    (Polynomial.natDegree_linear_le (a := (1 : ℝ)) (b := 1 - r))

theorem hankelAtomDisplacementNegativeWitness_degree (r : ℝ) :
    (hankelAtomDisplacementNegativeWitness r).natDegree ≤ 1 := by
  simpa [hankelAtomDisplacementNegativeWitness] using
    (Polynomial.natDegree_linear_le (a := (-1 : ℝ)) (b := 1 + r))

theorem hankelAtomDisplacementTangent_positiveWitness (m r : ℝ) :
    hankelAtomDisplacementTangent m r (hankelAtomDisplacementPositiveWitness r) =
      2 * m := by
  simp [hankelAtomDisplacementTangent, hankelAtomDisplacementPositiveWitness]

theorem hankelAtomDisplacementTangent_negativeWitness (m r : ℝ) :
    hankelAtomDisplacementTangent m r (hankelAtomDisplacementNegativeWitness r) =
      -2 * m := by
  simp [hankelAtomDisplacementTangent, hankelAtomDisplacementNegativeWitness]

/-- Every nonzero-degree positive atom has both positive and negative displacement-tangent
directions. -/
theorem hankelAtomDisplacementTangent_indefinite
    (d : ℕ) (hd : 1 ≤ d) (m r : ℝ) (hm : 0 < m) :
    ∃ qpos qneg : Polynomial ℝ,
      qpos.natDegree ≤ d ∧ qneg.natDegree ≤ d ∧
      0 < hankelAtomDisplacementTangent m r qpos ∧
      hankelAtomDisplacementTangent m r qneg < 0 := by
  refine ⟨hankelAtomDisplacementPositiveWitness r,
    hankelAtomDisplacementNegativeWitness r, ?_, ?_, ?_, ?_⟩
  · exact (hankelAtomDisplacementPositiveWitness_degree r).trans hd
  · exact (hankelAtomDisplacementNegativeWitness_degree r).trans hd
  · rw [hankelAtomDisplacementTangent_positiveWitness]
    linarith
  · rw [hankelAtomDisplacementTangent_negativeWitness]
    linarith

end

end HTGeometry
