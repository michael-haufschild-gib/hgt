import GaloisForLFunctions.HTGeometry.QKrawtchoukMaximalAtoms

/-!
# Polynomial approximation of a maximal atom

The maximal-atom mechanism in arXiv:2609.24149 also gives a concrete density
statement. A normalized Christoffel kernel approximates the indicator of
the selected atom. Its squared integral error is exactly the difference
between the finite and infinite Christoffel values. No density assumption
on the polynomial space is used.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace HTGeometry

private theorem polynomial_indicator_error {s : ℕ → ℝ} (μ : ProbabilityMeasure ℝ)
    (hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ))
    (x : ℝ) (p : Polynomial ℝ) (hval : p.eval x = 1) :
    Integrable (fun y => (({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) y - p.eval y) ^ 2)
      (μ : Measure ℝ) ∧
    (∫ y, (({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) y - p.eval y) ^ 2
      ∂(μ : Measure ℝ)) = momentInner s p p - (μ : Measure ℝ).real {x} := by
  classical
  have hp := integrable_eval (fun k => (hm k).1) p
  have hsq : Integrable (fun y => (p.eval y) ^ 2) (μ : Measure ℝ) :=
    (integrable_eval (fun k => (hm k).1) (p ^ (2 : ℕ))).congr
      (ae_of_all _ fun _ => Polynomial.eval_pow 2)
  have hi : Integrable (({x} : Set ℝ).indicator (fun y => 1 - 2 * p.eval y))
      (μ : Measure ℝ) :=
    ((integrable_const (1 : ℝ)).sub (hp.const_mul 2)).indicator (measurableSet_singleton x)
  have hexpand :
      (fun y => (({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) y - p.eval y) ^ 2) =
      (fun y => ({x} : Set ℝ).indicator (fun y => 1 - 2 * p.eval y) y + (p.eval y) ^ 2) := by
    funext y
    by_cases hy : y ∈ ({x} : Set ℝ)
    · simp only [Set.indicator_of_mem hy]
      ring
    · simp only [Set.indicator_of_notMem hy]
      ring
  have hnorm : (∫ y, (p.eval y) ^ 2 ∂(μ : Measure ℝ)) = momentInner s p p := by
    simpa only [pow_two, momentInner_def] using
      (momentFunctional_pow_two_eq_integral_sq s (fun k => (hm k).2.symm)
        (fun k => (hm k).1) p).symm
  rw [hexpand]
  refine ⟨hi.add hsq, ?_⟩
  rw [integral_add hi hsq, integral_indicator (measurableSet_singleton x),
    integral_singleton, smul_eq_mul, hval, hnorm]
  ring

/-- The finite normalized kernel, as an actual polynomial in the existing
inverse-q Hermite moment problem. -/
def inverseQHermiteAtomProbe (t u x : ℝ) (n : ℕ) : Polynomial ℝ :=
  christoffel (inverseQHermiteMoment t u) n x • cdKernel (inverseQHermiteMoment t u) n x

/-- The exact squared error of the polynomial atom probe is the remaining
Christoffel gap. Integrability is included to exclude totalized-integral artifacts. -/
theorem inverseQHermiteAtomProbe_error (t u x : ℝ) (n : ℕ) :
    Integrable (fun y => (({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) y -
      (inverseQHermiteAtomProbe t u x n).eval y) ^ 2)
      (inverseQHermiteAtomMeasure t u x : Measure ℝ) ∧
    (∫ y, (({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) y -
      (inverseQHermiteAtomProbe t u x n).eval y) ^ 2
      ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ)) =
      christoffel (inverseQHermiteMoment t u) n x -
        christoffelLimit (inverseQHermiteMoment t u) x := by
  have he := polynomial_indicator_error (inverseQHermiteAtomMeasure t u x)
    (inverseQHermiteAtomMeasure_moments t u x) x (inverseQHermiteAtomProbe t u x n)
    (normalisedKernel_eval_self (inverseQHermiteMoment_positive t u) n x)
  simpa only [inverseQHermiteAtomProbe,
    christoffel_eq_momentInner_normalisedKernel (inverseQHermiteMoment_positive t u),
    inverseQHermiteAtomMeasure_atom_real] using he

/-- Every selected maximal atom admits polynomial approximation in squared
integral norm. This is the atomwise input to polynomial completeness. -/
theorem inverseQHermiteAtomProbe_error_tendsto (t u x : ℝ) :
    Tendsto (fun n => ∫ y, (({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) y -
      (inverseQHermiteAtomProbe t u x n).eval y) ^ 2
      ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ)) atTop (𝓝 0) := by
  have heq n := (inverseQHermiteAtomProbe_error t u x n).2
  have ht := (tendsto_christoffel (inverseQHermiteMoment_positive t u) x).sub_const
    (christoffelLimit (inverseQHermiteMoment t u) x)
  simpa only [heq, sub_self] using ht

end HTGeometry
