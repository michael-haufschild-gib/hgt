import GaloisForLFunctions.HTGeometry.FiniteAdditiveFiberEnergy
import GaloisForLFunctions.RHTower.SquareResidueQuadraticCompletion

/-!
Exact family energy of quadratic Fourier completion, at every positive modulus.
The observable data are signed totals over square fibres. Thus collisions are
retained before taking absolute values, and the kernel of the completed family
is classified exactly. At prime modulus, each fibre has at most two points.
This applies the finite completion and cancellation-before-estimation mechanisms
of paper2 to the existing quadratic Gauss family, rather than its sextic theta family.
-/

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open scoped BigOperators

variable {q : ℕ} [NeZero q]

theorem sum_norm_sq_weighted_quadratic_eq_fibers (w : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ x : ZMod q, w x * ZMod.stdAddChar (a * x ^ 2)‖ ^ 2) =
      (q : ℝ) * ∑ y : ZMod q, ‖finiteWeightedFiber (fun x : ZMod q => x ^ 2) w y‖ ^ 2 :=
  sum_norm_sq_additive_phase_eq_fiber_energy (fun x => x ^ 2) w

theorem weighted_quadratic_vanishes_iff_square_fibers (w : ZMod q → ℂ) :
    (∀ a : ZMod q, ∑ x : ZMod q, w x * ZMod.stdAddChar (a * x ^ 2) = 0) ↔
      ∀ y, finiteWeightedFiber (fun x : ZMod q => x ^ 2) w y = 0 :=
  additive_phase_vanishes_iff_fibers (fun x => x ^ 2) w

/-- Completion preserves the exact square-fibre energy, including its cubic modulus factor. -/
theorem sum_norm_sq_quadratic_completion_eq_fibers (w : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ b : ZMod q,
      squareResidueFourierCoeff w b * squareResidueQuadraticGaussSum a b‖ ^ 2) =
      (q : ℝ) ^ 3 *
        ∑ y : ZMod q, ‖finiteWeightedFiber (fun x : ZMod q => x ^ 2) w y‖ ^ 2 := by
  simp_rw [← squareResidueQuadraticGaussSum_completion, norm_mul,
    Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum, sum_norm_sq_weighted_quadratic_eq_fibers]
  ring

theorem quadratic_completion_vanishes_iff_square_fibers (w : ZMod q → ℂ) :
    (∀ a : ZMod q, ∑ b : ZMod q,
      squareResidueFourierCoeff w b * squareResidueQuadraticGaussSum a b = 0) ↔
      ∀ y, finiteWeightedFiber (fun x : ZMod q => x ^ 2) w y = 0 := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp_rw [← squareResidueQuadraticGaussSum_completion, mul_eq_zero,
    hq, false_or]
  exact weighted_quadratic_vanishes_iff_square_fibers w

/-- Antisymmetric coefficients cancel before any estimate, including at composite modulus. -/
theorem weighted_quadratic_eq_zero_of_odd
    (w : ZMod q → ℂ) (hw : Function.Odd w) (a : ZMod q) :
    (∑ x : ZMod q, w x * ZMod.stdAddChar (a * x ^ 2)) = 0 := by
  apply Function.Odd.sum_eq_zero
  intro x
  dsimp only
  rw [neg_sq, hw x, neg_mul]

theorem quadratic_completion_eq_zero_of_odd
    (w : ZMod q → ℂ) (hw : Function.Odd w) (a : ZMod q) :
    (∑ b : ZMod q, squareResidueFourierCoeff w b *
      squareResidueQuadraticGaussSum a b) = 0 := by
  rw [← squareResidueQuadraticGaussSum_completion,
    weighted_quadratic_eq_zero_of_odd w hw, mul_zero]

theorem prime_square_fiber_card_le_two [Fact q.Prime] (y : ZMod q) :
    Fintype.card {x : ZMod q // x ^ 2 = y} ≤ 2 := by
  classical
  rw [Fintype.card_of_subtype (Finset.univ.filter (fun x : ZMod q => x ^ 2 = y))
    (by simp)]
  by_cases hy : ∃ x : ZMod q, x ^ 2 = y
  · obtain ⟨x, rfl⟩ := hy
    apply (Finset.card_le_card (t := {x, -x}) ?_).trans Finset.card_le_two
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (sq_eq_sq_iff_eq_or_eq_neg.mp hz')
  · have he : Finset.univ.filter (fun x : ZMod q => x ^ 2 = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [he]

/-- Prime-modulus quadratic averaging loses at most the two-point square collision. -/
theorem sum_norm_sq_weighted_quadratic_le_prime [Fact q.Prime] (w : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ x : ZMod q, w x * ZMod.stdAddChar (a * x ^ 2)‖ ^ 2) ≤
      (q : ℝ) * 2 * ∑ x : ZMod q, ‖w x‖ ^ 2 :=
  sum_norm_sq_additive_phase_le_fiber_card (fun x => x ^ 2) w 2 prime_square_fiber_card_le_two

/-- At prime modulus the invisible subspace is exactly the odd coefficients. -/
theorem weighted_quadratic_vanishes_iff_odd [Fact q.Prime] (w : ZMod q → ℂ) :
    (∀ a : ZMod q, ∑ x : ZMod q, w x * ZMod.stdAddChar (a * x ^ 2) = 0) ↔
      Function.Odd w := by
  classical
  constructor
  · intro h
    have hf := (weighted_quadratic_vanishes_iff_square_fibers w).mp h
    intro x
    have hx := hf (x ^ 2)
    unfold finiteWeightedFiber at hx
    rw [← Finset.sum_subtype {x, -x} (fun z => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact sq_eq_sq_iff_eq_or_eq_neg.symm)] at hx
    by_cases hxx : x = -x
    · have hx0 : w x = 0 := by simpa [← hxx] using hx
      simp [← hxx, hx0]
    · rw [Finset.sum_pair hxx] at hx
      linear_combination hx
  · intro h a
    exact weighted_quadratic_eq_zero_of_odd w h a

theorem quadratic_completion_vanishes_iff_odd [Fact q.Prime] (w : ZMod q → ℂ) :
    (∀ a : ZMod q, ∑ b : ZMod q,
      squareResidueFourierCoeff w b * squareResidueQuadraticGaussSum a b = 0) ↔
      Function.Odd w := by
  rw [quadratic_completion_vanishes_iff_square_fibers,
    ← weighted_quadratic_vanishes_iff_square_fibers,
    weighted_quadratic_vanishes_iff_odd]

theorem sum_norm_sq_quadratic_completion_le_prime [Fact q.Prime] (w : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ b : ZMod q,
      squareResidueFourierCoeff w b * squareResidueQuadraticGaussSum a b‖ ^ 2) ≤
      2 * (q : ℝ) ^ 3 * ∑ x : ZMod q, ‖w x‖ ^ 2 := by
  simp_rw [← squareResidueQuadraticGaussSum_completion, norm_mul,
    Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (q : ℝ) ^ 2 * ((q : ℝ) * 2 * ∑ x : ZMod q, ‖w x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_norm_sq_weighted_quadratic_le_prime w) (sq_nonneg _)
    _ = _ := by ring

end RHTower
