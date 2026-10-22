import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The affine recurrence envelope

Compensation between a sector and its complement is useful only if it *iterates*: the residual
left after a scale transition must feed the next one.  The abstract shape of such an iteration is
an affine recurrence

`F_{j+1} ≤ q_j F_j + r_j`,  `F_j, q_j, r_j ≥ 0`,

and the content of the iteration is whether its explicit solution stays bounded.  This module
supplies the envelope, its closed form, the criterion that actually produces a uniform bound, and
the sharpness statement that boundedness is an extra condition, not a consequence.

* `affineEnvelope` is the explicit solution of the recurrence with equality.
* `le_affineEnvelope` dominates any family obeying the inequality by it.
* `affineEnvelope_eq` is the closed form `F₀ ∏_{i<J} q_i + Σ_{j<J} r_j ∏_{j<i<J} q_i`.
* `affineEnvelope_le_of_contraction` is the usable criterion: multipliers bounded by `θ < 1` and
  sources bounded by `R` give the horizon-free bound `max(F₀, R/(1−θ))`.
* `affineEnvelope_one_one` shows unit multipliers with unit sources diverge linearly, so a
  compensation scheme that merely cancels at leading order per stage proves nothing: the stage
  multiplier must be strictly below one, or the sources must decay.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

set_option autoImplicit false

/-- The explicit solution of the affine recurrence with equality. -/
def affineEnvelope (F₀ : ℝ) (q r : ℕ → ℝ) : ℕ → ℝ
  | 0 => F₀
  | (j + 1) => q j * affineEnvelope F₀ q r j + r j

/-- **The envelope dominates.**  Any family satisfying the affine inequality is below the envelope
of its own initial value. -/
theorem le_affineEnvelope {F q r : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j)
    (hrec : ∀ j, F (j + 1) ≤ q j * F j + r j) (J : ℕ) : F J ≤ affineEnvelope (F 0) q r J := by
  induction J with
  | zero => exact le_rfl
  | succ J ih =>
    refine (hrec J).trans ?_
    have := mul_le_mul_of_nonneg_left ih (hq J)
    simp only [affineEnvelope]
    linarith

/-- **Closed form.**  The envelope is the initial value transported by the product of multipliers
plus each source transported by the multipliers after it. -/
theorem affineEnvelope_eq (F₀ : ℝ) (q r : ℕ → ℝ) (J : ℕ) :
    affineEnvelope F₀ q r J =
      F₀ * ∏ i ∈ range J, q i + ∑ j ∈ range J, r j * ∏ i ∈ Ico (j + 1) J, q i := by
  induction J with
  | zero => simp [affineEnvelope]
  | succ J ih =>
    have hsum : ∑ j ∈ range (J + 1), r j * ∏ i ∈ Ico (j + 1) (J + 1), q i =
        (∑ j ∈ range J, r j * ∏ i ∈ Ico (j + 1) J, q i) * q J + r J := by
      rw [Finset.sum_range_succ]
      congr 1
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.prod_Ico_succ_top (Finset.mem_range.mp hj)]
        ring
      · simp
    rw [affineEnvelope, ih, hsum, Finset.prod_range_succ]
    ring

/-- **The contraction criterion.**  Stage multipliers below `θ < 1` and stage sources below `R`
give a bound free of the stage index.  This is the hypothesis a sector-compensation scheme has to
meet: per-stage cancellation is not enough, the transported residual must contract. -/
theorem affineEnvelope_le_of_contraction {F₀ R θ : ℝ} {q r : ℕ → ℝ} (hF₀ : 0 ≤ F₀)
    (hθ1 : θ < 1) (hq : ∀ j, 0 ≤ q j) (hqθ : ∀ j, q j ≤ θ) (hr : ∀ j, 0 ≤ r j)
    (hrR : ∀ j, r j ≤ R) (J : ℕ) : affineEnvelope F₀ q r J ≤ max F₀ (R / (1 - θ)) := by
  have hR : 0 ≤ R := (hr 0).trans (hrR 0)
  have hθ0 : 0 ≤ θ := (hq 0).trans (hqθ 0)
  have hM0 : 0 ≤ max F₀ (R / (1 - θ)) := le_max_of_le_left hF₀
  have hstep : R ≤ (1 - θ) * max F₀ (R / (1 - θ)) := by
    have h1 : (0 : ℝ) < 1 - θ := by linarith
    have h2 : R / (1 - θ) ≤ max F₀ (R / (1 - θ)) := le_max_right _ _
    calc R = (1 - θ) * (R / (1 - θ)) := by field_simp
      _ ≤ (1 - θ) * max F₀ (R / (1 - θ)) := mul_le_mul_of_nonneg_left h2 h1.le
  induction J with
  | zero => exact le_max_left _ _
  | succ J ih =>
    have h1 : q J * affineEnvelope F₀ q r J ≤ θ * max F₀ (R / (1 - θ)) :=
      (mul_le_mul_of_nonneg_left ih (hq J)).trans
        (mul_le_mul_of_nonneg_right (hqθ J) hM0)
    simp only [affineEnvelope]
    linarith [hrR J]

/-- **Boundedness is an extra condition.**  Unit multipliers with unit sources give the envelope
`J`: cancellation that merely preserves the residual per stage diverges linearly. -/
theorem affineEnvelope_one_one (J : ℕ) :
    affineEnvelope 0 (fun _ => 1) (fun _ => 1) J = (J : ℝ) := by
  induction J with
  | zero => simp [affineEnvelope]
  | succ J ih => simp only [affineEnvelope, ih, one_mul]; push_cast; ring

theorem not_bddAbove_affineEnvelope_one_one :
    ¬ ∃ C : ℝ, ∀ J : ℕ, affineEnvelope 0 (fun _ => 1) (fun _ => 1) J ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨J, hJ⟩ := exists_nat_gt C
  exact absurd (hC J) (not_le.mpr (by rwa [affineEnvelope_one_one]))

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
