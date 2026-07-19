import GaloisForLFunctions.HTGeometry.GaussQuadrature

/-!
# The Gauss quadrature measure

The Gauss nodes carrying the Christoffel weights assemble into an honest measure

`gaussMeasure s n = ∑_{ξ} λₙ(ξ) δ_ξ`,

a finite positive measure whose moments agree with `s` up to order `2n+1`.  Integration against it
is the quadrature sum, so the exactness theorem transfers verbatim from the moment functional to the
integral.

The measure-theoretic content is a two-step induction over the node set: a finite weighted sum of
Dirac measures integrates any function, and integrates it to the corresponding weighted sum of
values.  Both are proved for an arbitrary finite weighted Dirac family, since nothing about the
Christoffel weights is used beyond their nonnegativity.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Every function is integrable against a finite weighted sum of Dirac measures. -/
theorem integrable_finsetWeightedDirac (t : Finset ℝ) (w : ℝ → ℝ) (f : ℝ → ℝ) :
    Integrable f (∑ x ∈ t, ENNReal.ofReal (w x) • Measure.dirac x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (Integrable.smul_measure (integrable_dirac (by simp)) (by simp)).add_measure ih

/-- A finite weighted sum of Dirac measures integrates to the weighted sum of values. -/
theorem integral_finsetWeightedDirac (t : Finset ℝ) (w : ℝ → ℝ) (hw : ∀ x, 0 ≤ w x)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂(∑ y ∈ t, ENNReal.ofReal (w y) • Measure.dirac y) = ∑ y ∈ t, w y * f y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        integral_add_measure
          (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))
          (integrable_finsetWeightedDirac t w f),
        integral_smul_measure, integral_dirac, ih, ENNReal.toReal_ofReal (hw a), smul_eq_mul]

/-- **The Gauss quadrature measure**: the nodes carrying their Christoffel weights. -/
noncomputable def gaussMeasure (s : ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  ∑ x ∈ gaussNodes s n, ENNReal.ofReal (christoffel s n x) • Measure.dirac x

theorem integrable_gaussMeasure (n : ℕ) (f : ℝ → ℝ) : Integrable f (gaussMeasure s n) :=
  integrable_finsetWeightedDirac _ _ f

/-- Integration against the Gauss measure is the quadrature sum. -/
theorem integral_gaussMeasure (h : PositiveMomentForm s) (n : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(gaussMeasure s n) = ∑ x ∈ gaussNodes s n, christoffel s n x * f x :=
  integral_finsetWeightedDirac _ _ (fun x => (christoffel_pos h n x).le) f

/-- **The Gauss measure reproduces the moments up to order `2n+1`.** -/
theorem gaussMeasure_moment (h : PositiveMomentForm s) (n k : ℕ) (hk : k ≤ 2 * n + 1) :
    ∫ x, x ^ k ∂(gaussMeasure s n) = s k := by
  rw [integral_gaussMeasure h n fun x => x ^ k]
  have hdeg : (Polynomial.X ^ k : Polynomial ℝ).degree < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast (by omega : k < 2 * n + 2)
  have hq := momentFunctional_eq_gaussSum h n (Polynomial.X ^ k) hdeg
  rw [momentFunctional_X_pow s k] at hq
  rw [hq]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

/-- The total mass of the Gauss measure is the zeroth moment. -/
theorem gaussMeasure_mass (h : PositiveMomentForm s) (n : ℕ) :
    ∫ _x, (1 : ℝ) ∂(gaussMeasure s n) = s 0 := by
  have hk := gaussMeasure_moment h n 0 (by omega)
  simpa using hk

end HTGeometry
