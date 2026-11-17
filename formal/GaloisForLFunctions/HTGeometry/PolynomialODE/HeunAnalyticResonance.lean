import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Analytic solutions at a biconfluent-Heun resonance

At parameters `α = -2`, `β = γ = q = 0`, every global real analytic solution
is `A + B exp(x²)`. Its value and second derivative recover both coefficients;
its first derivative at zero always vanishes. Thus a normalized first jet
leaves a genuine free parameter at this singular resonance.

This analyzes the nonresonance requirement behind the coefficient recurrence
in Castro, arXiv:2611.20963, equation (38). The resonant parameter lies outside
the physical `α ≥ 0` range. A weighted derivative determines the solution on
the positive half-line, and analytic uniqueness extends it globally.
-/

open Set Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry.Heun
noncomputable section

/-- The canonical biconfluent-Heun differential expression. -/
def action (α β γ q : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * deriv (deriv f) x + (1 + α - β * x - 2 * x ^ 2) * deriv f x +
    ((γ - α - 2) * x - q) * f x

def resonantSolution (A B x : ℝ) : ℝ := A + B * Real.exp (x ^ 2)
def resonantFirst (B x : ℝ) : ℝ := 2 * B * x * Real.exp (x ^ 2)
def resonantSecond (B x : ℝ) : ℝ := 2 * B * (1 + 2 * x ^ 2) * Real.exp (x ^ 2)

/-- Every member of the resonant family is real analytic everywhere. -/
theorem resonantSolution_analyticAt (A B x : ℝ) :
    AnalyticAt ℝ (resonantSolution A B) x := by
  unfold resonantSolution
  exact analyticAt_const.add (analyticAt_const.mul ((analyticAt_id.pow 2).rexp))

private theorem exp_sq_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t ^ 2)) (Real.exp (x ^ 2) * (2 * x)) x := by
  simpa only [pow_two, Pi.mul_apply, id_eq, one_mul, mul_one, two_mul] using
    ((hasDerivAt_id x).mul (hasDerivAt_id x)).exp

theorem resonantSolution_hasDerivAt (A B x : ℝ) :
    HasDerivAt (resonantSolution A B) (resonantFirst B x) x := by
  have h := (hasDerivAt_const x A).add ((exp_sq_derivative x).const_mul B)
  have he : 0 + B * (Real.exp (x ^ 2) * (2 * x)) = resonantFirst B x := by
    unfold resonantFirst
    ring
  rw [he] at h
  exact h

theorem resonantFirst_hasDerivAt (B x : ℝ) :
    HasDerivAt (resonantFirst B) (resonantSecond B x) x := by
  have h := ((hasDerivAt_id x).const_mul (2 * B)).mul (exp_sq_derivative x)
  have he : 2 * B * 1 * Real.exp (x ^ 2) +
      2 * B * id x * (Real.exp (x ^ 2) * (2 * x)) = resonantSecond B x := by
    unfold resonantSecond
    dsimp only [id_eq]
    ring
  rw [he] at h
  exact h

theorem resonantSolution_deriv (A B : ℝ) :
    deriv (resonantSolution A B) = resonantFirst B :=
  funext fun x => (resonantSolution_hasDerivAt A B x).deriv

theorem resonantSolution_deriv_two (A B : ℝ) :
    deriv (deriv (resonantSolution A B)) = resonantSecond B := by
  rw [resonantSolution_deriv]
  exact funext fun x => (resonantFirst_hasDerivAt B x).deriv

/-- A two-dimensional family solves the resonant equation on the whole real line. -/
theorem resonantSolution_equation (A B x : ℝ) :
    action (-2) 0 0 0 (resonantSolution A B) x = 0 := by
  rw [action, resonantSolution_deriv_two, resonantSolution_deriv]
  dsimp only [resonantSolution, resonantFirst, resonantSecond]
  ring

/-- The value and second derivative recover both coefficients; the first derivative is blind. -/
theorem resonantSolution_initial_jet (A B : ℝ) :
    resonantSolution A B 0 = A + B ∧
      deriv (resonantSolution A B) 0 = 0 ∧
        deriv (deriv (resonantSolution A B)) 0 = 2 * B := by
  rw [resonantSolution_deriv_two, resonantSolution_deriv]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [resonantSolution, resonantFirst, resonantSecond, zero_pow (by omega : 2 ≠ 0),
      Real.exp_zero, mul_one, mul_zero, add_zero]

/-- Normalizing the value and first derivative leaves a free genuine solution parameter. -/
theorem resonant_normalized_family :
    (∀ B : ℝ, (∀ x : ℝ, action (-2) 0 0 0 (resonantSolution (1 - B) B) x = 0) ∧
      resonantSolution (1 - B) B 0 = 1 ∧ deriv (resonantSolution (1 - B) B) 0 = 0) ∧
      Function.Injective (fun B : ℝ => resonantSolution (1 - B) B) := by
  constructor
  · intro B
    have hj := resonantSolution_initial_jet (1 - B) B
    refine ⟨resonantSolution_equation (1 - B) B, ?_, hj.2.1⟩
    rw [hj.1]
    ring
  · intro B C h
    have hjB := (resonantSolution_initial_jet (1 - B) B).2.2
    have hjC := (resonantSolution_initial_jet (1 - C) C).2.2
    have hh := congrArg (fun f : ℝ → ℝ => deriv (deriv f) 0) h
    rw [hjB, hjC] at hh
    linarith only [hh]

/-- The degree-zero tuning and normalized first jet do not force a constant at resonance. -/
theorem resonant_first_jet_does_not_force_constant :
    ∃ f : ℝ → ℝ, (∀ x : ℝ, AnalyticAt ℝ f x) ∧
      (∀ x : ℝ, action (-2) 0 0 0 f x = 0) ∧
      f 0 = 1 ∧ deriv f 0 = 0 ∧ f ≠ (fun _ => 1) := by
  refine ⟨resonantSolution (1 - 1) 1, resonantSolution_analyticAt (1 - 1) 1,
    (resonant_normalized_family.1 1).1,
    (resonant_normalized_family.1 1).2.1, (resonant_normalized_family.1 1).2.2, ?_⟩
  intro h
  have hc : resonantSolution (1 - 0) 0 = (fun _ => 1) := by
    funext x
    simp only [resonantSolution, sub_zero, zero_mul, add_zero]
  have he := resonant_normalized_family.2 (h.trans hc.symm)
  norm_num at he

/-- A weighted derivative is constant on the positive half-line. -/
private theorem resonant_weighted_derivative {f : ℝ → ℝ}
    (hf : ∀ x, AnalyticAt ℝ f x)
    (hode : ∀ x, action (-2) 0 0 0 f x = 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => deriv f t / (t * Real.exp (t ^ 2))) 0 x := by
  have hd := ((hf x).deriv.differentiableAt.hasDerivAt).div
    ((hasDerivAt_id x).mul (exp_sq_derivative x))
    (mul_ne_zero hx.ne' (Real.exp_ne_zero _))
  have ho := hode x
  dsimp only [action] at ho
  have hnum : deriv (deriv f) x * (x * Real.exp (x ^ 2)) -
      deriv f x * (1 * Real.exp (x ^ 2) + x * (Real.exp (x ^ 2) * (2 * x))) = 0 := by
    linear_combination Real.exp (x ^ 2) * ho
  simp only [Pi.mul_apply, id_eq] at hd
  rw [hnum, zero_div] at hd
  exact hd

/-- All global analytic solutions are exactly the explicit two-parameter resonant family. -/
theorem resonant_analytic_solutions_iff (f : ℝ → ℝ) :
    ((∀ x, AnalyticAt ℝ f x) ∧ (∀ x, action (-2) 0 0 0 f x = 0)) ↔
      ∃ A B : ℝ, f = resonantSolution A B := by
  constructor
  · rintro ⟨hf, hode⟩
    let K := deriv f 1 / (1 * Real.exp (1 ^ 2))
    have hg (x : ℝ) (hx : 0 < x) :
        deriv f x / (x * Real.exp (x ^ 2)) = K := by
      exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun t ht => (resonant_weighted_derivative hf hode ht).differentiableAt.differentiableWithinAt)
        (fun t ht => (resonant_weighted_derivative hf hode ht).deriv) hx (by norm_num : (0 : ℝ) < 1)
    have hd (x : ℝ) (hx : 0 < x) :
        HasDerivAt (fun t => f t - (K / 2) * Real.exp (t ^ 2)) 0 x := by
      have h := (hf x).differentiableAt.hasDerivAt.sub
        ((exp_sq_derivative x).const_mul (K / 2))
      have he := (div_eq_iff (mul_ne_zero hx.ne' (Real.exp_ne_zero _))).mp (hg x hx)
      have hz : deriv f x - (K / 2) * (Real.exp (x ^ 2) * (2 * x)) = 0 := by
        linear_combination he
      rw [hz] at h
      exact h
    let A := f 1 - (K / 2) * Real.exp (1 ^ 2)
    have hp (x : ℝ) (hx : 0 < x) : f x = resonantSolution A (K / 2) x := by
      have hc : f x - (K / 2) * Real.exp (x ^ 2) = A :=
        isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
          (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
          (fun t ht => (hd t ht).deriv) hx (by norm_num : (0 : ℝ) < 1)
      dsimp only [resonantSolution]
      linarith only [hc]
    refine ⟨A, K / 2, AnalyticOnNhd.eq_of_eventuallyEq (z₀ := (1 : ℝ))
      (fun x _ => hf x) (fun x _ => resonantSolution_analyticAt A (K / 2) x) ?_⟩
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
    exact hp x hx
  · rintro ⟨A, B, rfl⟩
    exact ⟨resonantSolution_analyticAt A B, resonantSolution_equation A B⟩

/-- The value and second derivative give the complete analytic solution, even at resonance. -/
theorem resonant_solution_from_second_jet (f : ℝ → ℝ)
    (hf : ∀ x, AnalyticAt ℝ f x) (hode : ∀ x, action (-2) 0 0 0 f x = 0) :
    f = resonantSolution (f 0 - deriv (deriv f) 0 / 2) (deriv (deriv f) 0 / 2) := by
  obtain ⟨A, B, rfl⟩ := (resonant_analytic_solutions_iff f).mp ⟨hf, hode⟩
  have hj := resonantSolution_initial_jet A B
  rw [hj.1, hj.2.2]
  congr 1 <;> ring

#print axioms resonant_analytic_solutions_iff
#print axioms resonant_solution_from_second_jet

#print axioms resonantSolution_equation
#print axioms resonant_first_jet_does_not_force_constant
#print axioms resonant_normalized_family
end
end GaloisForLFunctions.HTGeometry.Heun
