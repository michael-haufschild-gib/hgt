import GaloisForLFunctions.RHTower.SuzukiAffineResolventKreinDefect
import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite-Morse resolvent-jet completion

At fixed Suzuki aperture the restricted-Weil operator has only finitely many distinct negative
spectral levels.  The preceding Krein-defect theorem fixes the positive debt at each such level.
This file proves that all those debts can be paid simultaneously by the square of one polynomial
in one below-spectrum resolvent.

The polynomial is a Lagrange interpolant with zero constant term.  Zero constant term is the
algebraic reason its operator realization is compact when the resolvent is compact.  The final
no-go theorem proves that a finite polynomial cannot equal the exact negative projector on an
infinite positive spectral tail: positive overpayment is necessary.  Thus the source-compatible
target is a finite resolvent-jet square dominating the negative projector, not the discontinuous
projector itself.

All theorems are unconditional.  They use no RH premise, Xi-zero data, estimate, or computation.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- Spectral value of the resolvent `(A - rho I)⁻¹` at scalar spectral coordinate `t`. -/
def suzukiFiniteMorseResolventNode (rho t : ℝ) : ℝ :=
  (t - rho)⁻¹

/-- Positive amount required to cancel the affine Krein defect at a negative spectral node. -/
def suzukiFiniteMorseKreinDebt (alpha beta t : ℝ) : ℝ :=
  -suzukiAffineResolventKreinDefect alpha beta t

/-- Lagrange polynomial with zero constant term and prescribed squared values on finite nodes.

Writing the polynomial as `X` times an interpolant makes the zero-at-infinity condition for the
compact resolvent coordinate literal. -/
def suzukiFiniteMorseInterpolant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode debt : ι → ℝ) : ℝ[X] :=
  X * Lagrange.interpolate Finset.univ resolventNode
    (fun i => Real.sqrt (debt i) / resolventNode i)

/-- Specialization of the interpolant to exact affine Krein debts of spectral levels `t`. -/
def suzukiFiniteMorseKreinInterpolant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (alpha beta rho : ℝ) (t : ι → ℝ) : ℝ[X] :=
  suzukiFiniteMorseInterpolant
    (fun i => suzukiFiniteMorseResolventNode rho (t i))
    (fun i => suzukiFiniteMorseKreinDebt alpha beta (t i))

/-- Distinct spectral levels remain distinct after passing to one resolvent coordinate. -/
theorem suzukiFiniteMorseResolventNode_injective
    {ι : Type*} {rho : ℝ} {t : ι → ℝ} (ht : Function.Injective t) :
    Function.Injective (fun i => suzukiFiniteMorseResolventNode rho (t i)) := by
  intro i j hij
  apply ht
  apply sub_left_injective
  exact inv_injective hij

/-- A below-spectrum resolvent node is nonzero. -/
theorem suzukiFiniteMorseResolventNode_ne_zero
    {rho t : ℝ} (hrho : rho < t) :
    suzukiFiniteMorseResolventNode rho t ≠ 0 := by
  exact inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hrho))

/-- The finite-Morse interpolant vanishes at the compactified resolvent point `0`. -/
@[simp]
theorem suzukiFiniteMorseInterpolant_eval_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode debt : ι → ℝ) :
    (suzukiFiniteMorseInterpolant resolventNode debt).eval 0 = 0 := by
  simp [suzukiFiniteMorseInterpolant]

/-- At every interpolation node the polynomial takes the positive square root of its debt. -/
theorem suzukiFiniteMorseInterpolant_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode debt : ι → ℝ)
    (hnode : Function.Injective resolventNode)
    (hnode0 : ∀ i, resolventNode i ≠ 0) (i : ι) :
    (suzukiFiniteMorseInterpolant resolventNode debt).eval (resolventNode i) =
      Real.sqrt (debt i) := by
  rw [suzukiFiniteMorseInterpolant, Polynomial.eval_mul, Polynomial.eval_X,
    Lagrange.eval_interpolate_at_node _ hnode.injOn (Finset.mem_univ i)]
  exact mul_div_cancel₀ _ (hnode0 i)

/-- Squaring gives the prescribed debt exactly. -/
theorem suzukiFiniteMorseInterpolant_eval_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode debt : ι → ℝ)
    (hnode : Function.Injective resolventNode)
    (hnode0 : ∀ i, resolventNode i ≠ 0)
    (hdebt : ∀ i, 0 ≤ debt i) (i : ι) :
    (suzukiFiniteMorseInterpolant resolventNode debt).eval (resolventNode i) ^ 2 =
      debt i := by
  rw [suzukiFiniteMorseInterpolant_eval resolventNode debt hnode hnode0 i]
  exact Real.sq_sqrt (hdebt i)

/-- On finitely many distinct negative spectral levels, one resolvent polynomial square pays all
Krein debts exactly. -/
theorem suzukiFiniteMorseKreinInterpolant_exact_negativeDebt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {alpha beta rho : ℝ} {t : ι → ℝ}
    (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : ∀ i, beta < t i) (htneg : ∀ i, t i < 0)
    (hrho : ∀ i, rho < t i) (ht : Function.Injective t) (i : ι) :
    (suzukiFiniteMorseKreinInterpolant alpha beta rho t).eval
          (suzukiFiniteMorseResolventNode rho (t i)) ^ 2 =
      suzukiFiniteMorseKreinDebt alpha beta (t i) := by
  unfold suzukiFiniteMorseKreinInterpolant
  have hdebt : ∀ j, 0 ≤ suzukiFiniteMorseKreinDebt alpha beta (t j) := by
    intro j
    exact le_of_lt (suzukiNegativeSpectralNode_compensationDeficit_pos
      hab hb0 (hbt j) (htneg j))
  exact suzukiFiniteMorseInterpolant_eval_sq
    (fun j => suzukiFiniteMorseResolventNode rho (t j))
    (fun j => suzukiFiniteMorseKreinDebt alpha beta (t j))
    (suzukiFiniteMorseResolventNode_injective ht)
    (fun j => suzukiFiniteMorseResolventNode_ne_zero (hrho j)) hdebt i

/-- Exact negative-block cancellation: completed affine Krein coefficient is zero at every
negative spectral level. -/
theorem suzukiFiniteMorseKreinInterpolant_cancels_negativeDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {alpha beta rho : ℝ} {t : ι → ℝ}
    (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : ∀ i, beta < t i) (htneg : ∀ i, t i < 0)
    (hrho : ∀ i, rho < t i) (ht : Function.Injective t) (i : ι) :
    suzukiAffineResolventKreinDefect alpha beta (t i) +
        (suzukiFiniteMorseKreinInterpolant alpha beta rho t).eval
          (suzukiFiniteMorseResolventNode rho (t i)) ^ 2 = 0 := by
  rw [suzukiFiniteMorseKreinInterpolant_exact_negativeDebt
    hab hb0 hbt htneg hrho ht i]
  simp [suzukiFiniteMorseKreinDebt]

/-- Sharp scalar classification: a polynomial square completes one node exactly when it dominates
that node's Krein debt. -/
theorem suzukiPolynomialResolventSquare_completes_iff
    (alpha beta rho t : ℝ) (q : ℝ[X]) :
    0 ≤ suzukiAffineResolventKreinDefect alpha beta t +
        q.eval (suzukiFiniteMorseResolventNode rho t) ^ 2 ↔
      suzukiFiniteMorseKreinDebt alpha beta t ≤
        q.eval (suzukiFiniteMorseResolventNode rho t) ^ 2 := by
  simp only [suzukiFiniteMorseKreinDebt]
  constructor <;> intro h <;> linarith

/-- Adding any polynomial square preserves positivity at a positive spectral node. -/
theorem suzukiPolynomialResolventSquare_preserves_positiveDefect
    {alpha beta rho t : ℝ} (q : ℝ[X])
    (hab : alpha < beta) (hb0 : beta < 0) (htpos : 0 < t) :
    0 ≤ suzukiAffineResolventKreinDefect alpha beta t +
      q.eval (suzukiFiniteMorseResolventNode rho t) ^ 2 := by
  have hdefect : 0 < suzukiAffineResolventKreinDefect alpha beta t :=
    (suzukiAffineResolventKreinDefect_pos_iff hab hb0
      (lt_trans hb0 htpos) (ne_of_gt htpos)).2 htpos
  exact add_nonneg (le_of_lt hdefect) (sq_nonneg _)

/-- Full finite diagonal theorem.  The interpolant cancels every distinct negative level and can
only add a nonnegative square on every positive coordinate, so the mixed-sign quadratic form is
nonnegative for arbitrary amplitudes. -/
theorem suzukiFiniteMorseKreinDiagonalForm_nonneg
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {alpha beta rho : ℝ} {negativeLevel : ι → ℝ} {positiveLevel : κ → ℝ}
    (negativeAmplitude : ι → ℝ) (positiveAmplitude : κ → ℝ)
    (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : ∀ i, beta < negativeLevel i)
    (hnegative : ∀ i, negativeLevel i < 0)
    (hrho : ∀ i, rho < negativeLevel i)
    (hinjective : Function.Injective negativeLevel)
    (hpositive : ∀ j, 0 < positiveLevel j) :
    0 ≤
      (∑ i, (suzukiAffineResolventKreinDefect alpha beta (negativeLevel i) +
          (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel).eval
            (suzukiFiniteMorseResolventNode rho (negativeLevel i)) ^ 2) *
          negativeAmplitude i ^ 2) +
      ∑ j, (suzukiAffineResolventKreinDefect alpha beta (positiveLevel j) +
          (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel).eval
            (suzukiFiniteMorseResolventNode rho (positiveLevel j)) ^ 2) *
          positiveAmplitude j ^ 2 := by
  have hnegativeSum :
      (∑ i, (suzukiAffineResolventKreinDefect alpha beta (negativeLevel i) +
          (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel).eval
            (suzukiFiniteMorseResolventNode rho (negativeLevel i)) ^ 2) *
          negativeAmplitude i ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [suzukiFiniteMorseKreinInterpolant_cancels_negativeDefect
      hab hb0 hbt hnegative hrho hinjective i]
    simp
  rw [hnegativeSum, zero_add]
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg
    (suzukiPolynomialResolventSquare_preserves_positiveDefect
      (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel)
      hab hb0 (hpositive j))
    (sq_nonneg _)

/-- A polynomial whose square vanishes on an infinite set of spectral nodes is the zero
polynomial.  This is the algebraic obstruction to realizing an exact negative projector by a
finite resolvent polynomial. -/
theorem suzukiPolynomialSquare_zero_on_infiniteSet_forces_zero
    (q : ℝ[X]) {spectralNodes : Set ℝ} (hinfinite : spectralNodes.Infinite)
    (hzero : ∀ x ∈ spectralNodes, q.eval x ^ 2 = 0) :
    q = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot q
  apply hinfinite.mono
  intro x hx
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot]
  exact sq_eq_zero_iff.mp (hzero x hx)

/-- **Exact-projector no-go.**  Vanishing on an infinite positive tail is incompatible with paying
one strictly positive negative-node debt.  Finite resolvent polynomials must therefore overpay on
some positive spectral coordinates. -/
theorem suzukiFiniteResolventPolynomial_exactProjector_impossible
    (q : ℝ[X]) {positiveResolventNodes : Set ℝ} {negativeResolventNode debt : ℝ}
    (hinfinite : positiveResolventNodes.Infinite)
    (hpositiveTail : ∀ x ∈ positiveResolventNodes, q.eval x ^ 2 = 0)
    (hdebt : 0 < debt) (hnegativeMatch : q.eval negativeResolventNode ^ 2 = debt) :
    False := by
  have hq : q = 0 :=
    suzukiPolynomialSquare_zero_on_infiniteSet_forces_zero q hinfinite hpositiveTail
  rw [hq] at hnegativeMatch
  norm_num at hnegativeMatch
  linarith

end

end RHTower
