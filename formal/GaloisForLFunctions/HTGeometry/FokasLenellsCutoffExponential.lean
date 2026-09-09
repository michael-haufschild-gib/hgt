import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffGenerator
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The actual cutoff evolution is an operator exponential

Uniqueness for its concrete bounded linear differential equation identifies
the existing phase multiplier with the Banach-algebra exponential. The same
operator is therefore real analytic in time, and every derivative is an
explicit power of the skew-adjoint generator times the actual unitary.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The actual phase multiplier solves an autonomous bounded linear equation on every vector. -/
theorem cutoffEvolution_generator_hasDerivAt (a t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    HasDerivAt (fun s => cutoffEvolution a s u)
      (cutoffEvolutionTimeOperator a 0 (cutoffEvolution a t u)) t := by
  change HasDerivAt (fun s => cutoffEvolution a s u)
    ((cutoffEvolutionTimeOperator a 0).comp (cutoffEvolution a t) u) t
  rw [← cutoffEvolutionTimeOperator_eq_generator_comp a t]
  exact cutoffEvolution_hasDerivAt a t u

private theorem exponential_generator_hasDerivAt (a t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • cutoffEvolutionTimeOperator a 0) u)
      (cutoffEvolutionTimeOperator a 0 (NormedSpace.exp (t • cutoffEvolutionTimeOperator a 0) u)) t :=
  ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 (volume : Measure ℝ)) u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (cutoffEvolutionTimeOperator a 0) t)

/-- The existing cutoff unitary is exactly the exponential of its actual bounded generator. -/
theorem cutoffEvolution_eq_exp (a t : ℝ) :
    cutoffEvolution a t = NormedSpace.exp (t • cutoffEvolutionTimeOperator a 0) := by
  apply ContinuousLinearMap.ext
  intro u
  let f : ℝ → Lp ℂ 2 (volume : Measure ℝ) := fun s => cutoffEvolution a s u
  let g : ℝ → Lp ℂ 2 (volume : Measure ℝ) := fun s => NormedSpace.exp (s • cutoffEvolutionTimeOperator a 0) u
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun s => (cutoffEvolution_generator_hasDerivAt a s u).continuousAt
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun s => (exponential_generator_hasDerivAt a s u).continuousAt
  have h0 : f 0 = g 0 := by simp [f,g,cutoffEvolution_zero]
  have h := ODE_solution_unique_of_mem_Icc
    (f := f) (g := g) (a := -|t|-1) (b := |t|+1) (t₀ := 0)
    (v := fun _ y => cutoffEvolutionTimeOperator a 0 y) (s := fun _ => Set.univ)
    (fun _ _ => (cutoffEvolutionTimeOperator a 0).lipschitz.lipschitzOnWith)
    (by constructor <;> linarith [abs_nonneg t]) hf.continuousOn
    (fun s _ => cutoffEvolution_generator_hasDerivAt a s u) (fun _ _ => mem_univ _)
    hg.continuousOn (fun s _ => exponential_generator_hasDerivAt a s u)
    (fun _ _ => mem_univ _) h0
  exact h (by constructor <;> linarith [neg_abs_le t,le_abs_self t])

/-- The cutoff evolution is real analytic in operator norm at every time. -/
theorem cutoffEvolution_analyticAt (a t : ℝ) : AnalyticAt ℝ (cutoffEvolution a) t := by
  have he : cutoffEvolution a = fun s => NormedSpace.exp (s • cutoffEvolutionTimeOperator a 0) :=
    funext (cutoffEvolution_eq_exp a)
  rw [he]
  have hl : AnalyticAt ℝ (fun s : ℝ => s • cutoffEvolutionTimeOperator a 0) t := by fun_prop
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp hl

/-- The actual cutoff evolution is smooth to every order in operator norm. -/
theorem cutoffEvolution_contDiff (a : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (cutoffEvolution a) :=
  (show AnalyticOnNhd ℝ (cutoffEvolution a) Set.univ from fun t _ => cutoffEvolution_analyticAt a t).contDiff

/-- Its existing strong time generator is also the operator-norm derivative. -/
theorem cutoffEvolution_operator_hasDerivAt (a t : ℝ) :
    HasDerivAt (cutoffEvolution a) (cutoffEvolutionTimeOperator a t) t := by
  rw [cutoffEvolutionTimeOperator_eq_generator_comp]
  change HasDerivAt (fun s => cutoffEvolution a s)
    (cutoffEvolutionTimeOperator a 0 * cutoffEvolution a t) t
  have he : cutoffEvolution a = fun s => NormedSpace.exp (s • cutoffEvolutionTimeOperator a 0) :=
    funext (cutoffEvolution_eq_exp a)
  simpa only [he] using hasDerivAt_exp_smul_const' (cutoffEvolutionTimeOperator a 0) t

/-- The actual cutoff evolution is a unitary element of the bounded operator algebra. -/
theorem cutoffEvolution_mem_unitary (a t : ℝ) :
    cutoffEvolution a t ∈ unitary (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) := by
  simpa only [Unitary.coe_symm_linearIsometryEquiv_apply,cutoffEvolution] using
    (Unitary.linearIsometryEquiv.symm (cutoffPhaseUnitary a t)).property

/-- The operator exponential retains exactly unit norm at every real time. -/
theorem norm_cutoffEvolution (a t : ℝ) : ‖cutoffEvolution a t‖ = 1 :=
  CStarRing.norm_of_mem_unitary (cutoffEvolution_mem_unitary a t)

/-- The concrete candidate for every operator-norm time derivative. -/
def cutoffEvolutionDerivative (a : ℝ) (n : ℕ) (t : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  cutoffEvolutionTimeOperator a 0 ^ n * cutoffEvolution a t

/-- Zeroth derivative is the original actual unitary. -/
theorem cutoffEvolutionDerivative_zero (a t : ℝ) :
    cutoffEvolutionDerivative a 0 t = cutoffEvolution a t := by simp [cutoffEvolutionDerivative]

/-- First derivative is exactly the existing time-generator operator. -/
theorem cutoffEvolutionDerivative_one (a t : ℝ) :
    cutoffEvolutionDerivative a 1 t = cutoffEvolutionTimeOperator a t := by
  rw [cutoffEvolutionTimeOperator_eq_generator_comp]
  rfl

/-- Every derivative has exactly the corresponding power of the cutoff budget as norm. -/
theorem norm_cutoffEvolutionDerivative (a t : ℝ) (n : ℕ) :
    ‖cutoffEvolutionDerivative a n t‖ = cutoffPhaseBudget a ^ n := by
  rw [cutoffEvolutionDerivative,CStarRing.norm_mul_mem_unitary _ (cutoffEvolution_mem_unitary a t),
    norm_cutoffEvolutionTimeOperator_zero_pow]

/-- Each concrete derivative differentiates to its next power in operator norm. -/
theorem cutoffEvolutionDerivative_hasDerivAt (a t : ℝ) (n : ℕ) :
    HasDerivAt (cutoffEvolutionDerivative a n) (cutoffEvolutionDerivative a (n+1) t) t := by
  have h := (cutoffEvolution_operator_hasDerivAt a t).const_mul (cutoffEvolutionTimeOperator a 0 ^ n)
  rw [cutoffEvolutionTimeOperator_eq_generator_comp a t] at h
  change HasDerivAt (fun s => cutoffEvolutionTimeOperator a 0 ^ n * cutoffEvolution a s)
    (cutoffEvolutionTimeOperator a 0 ^ n * (cutoffEvolutionTimeOperator a 0 * cutoffEvolution a t)) t at h
  change HasDerivAt (fun s => cutoffEvolutionTimeOperator a 0 ^ n * cutoffEvolution a s)
    (cutoffEvolutionTimeOperator a 0 ^ (n+1) * cutoffEvolution a t) t
  simpa only [pow_succ,mul_assoc] using h

/-- Every iterated derivative of the actual cutoff evolution is the explicit bounded operator. -/
theorem iteratedDeriv_cutoffEvolution (a : ℝ) (n : ℕ) :
    iteratedDeriv n (cutoffEvolution a) = cutoffEvolutionDerivative a n := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    exact funext fun t => (cutoffEvolutionDerivative_zero a t).symm
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun t => (cutoffEvolutionDerivative_hasDerivAt a t n).deriv

/-- The exact norm of every actual iterated time derivative is the corresponding budget power. -/
theorem norm_iteratedDeriv_cutoffEvolution (a t : ℝ) (n : ℕ) :
    ‖iteratedDeriv n (cutoffEvolution a) t‖ = cutoffPhaseBudget a ^ n := by
  rw [iteratedDeriv_cutoffEvolution,norm_cutoffEvolutionDerivative]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
