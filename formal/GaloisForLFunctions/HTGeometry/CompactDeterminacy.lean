import GaloisForLFunctions.HTGeometry.PolySeqApprox

/-!
# Compactly supported representing measures are unique

Two finite measures carried by the same compact interval and having the same moments are equal.

Against a bounded continuous `f`, approximate uniformly on the interval by polynomials; the
polynomial integrals converge to the integral of `f` against each measure, and they agree termwise
because the moments do.  Uniqueness of limits gives equality of the two integrals, and a finite
measure on `ℝ` is determined by the integrals of bounded continuous functions.
-/

open scoped BigOperators
open MeasureTheory Polynomial Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Determinacy on a compact interval.** -/
theorem measure_eq_of_moments_eq_of_carried {mu nu : Measure ℝ}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] {m M : ℝ}
    (hmus : mu (Set.Icc m M)ᶜ = 0) (hnus : nu (Set.Icc m M)ᶜ = 0)
    (hsmu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂mu)
    (hintmu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) mu)
    (hsnu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂nu)
    (hintnu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu) :
    mu = nu := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  obtain ⟨P, hP⟩ := exists_poly_seq_tendstoUniformlyOn
    (g := fun x => f x) f.continuous.continuousOn
  have hintPmu : ∀ n, Integrable (fun x : ℝ => (P n).eval x) mu :=
    fun n => integrable_eval hintmu (P n)
  have hintPnu : ∀ n, Integrable (fun x : ℝ => (P n).eval x) nu :=
    fun n => integrable_eval hintnu (P n)
  have hfmu : Integrable (fun x : ℝ => f x) mu := f.integrable mu
  have hfnu : Integrable (fun x : ℝ => f x) nu := f.integrable nu
  have h1 := tendsto_integral_of_tendstoUniformlyOn hmus hintPmu hfmu hP
  have h2 := tendsto_integral_of_tendstoUniformlyOn hnus hintPnu hfnu hP
  have heq : ∀ n, ∫ x, (P n).eval x ∂mu = ∫ x, (P n).eval x ∂nu :=
    fun n => integral_eval_eq_of_moments_eq hsmu hintmu hsnu hintnu (P n)
  have h2' : Tendsto (fun n => ∫ x, (P n).eval x ∂mu) atTop (nhds (∫ x, f x ∂nu)) :=
    Filter.Tendsto.congr (fun n => (heq n).symm) h2
  exact tendsto_nhds_unique h1 h2'

end HTGeometry
