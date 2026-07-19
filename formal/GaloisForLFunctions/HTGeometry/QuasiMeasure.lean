import GaloisForLFunctions.HTGeometry.QuasiQuadrature
import GaloisForLFunctions.HTGeometry.GaussMeasure

/-!
# The quasi-orthogonal quadrature measure

The nodes carrying their interpolatory weights assemble into a finite positive measure whose moments
agree with `s` up to order `2n`.

The weights are only known to be nonnegative *at the nodes* — away from them a Lagrange functional
has no sign — so the integration lemma of the Gauss construction is restated with nonnegativity
required on the node set alone.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- A finite weighted sum of Dirac measures integrates to the weighted sum of values, needing the
weights nonnegative only where they are used. -/
theorem integral_finsetWeightedDirac_of_mem (t : Finset ℝ) (w : ℝ → ℝ)
    (hw : ∀ x ∈ t, 0 ≤ w x) (f : ℝ → ℝ) :
    ∫ x, f x ∂(∑ y ∈ t, ENNReal.ofReal (w y) • Measure.dirac y) = ∑ y ∈ t, w y * f y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      have hwa : 0 ≤ w a := hw a (Finset.mem_insert_self a t)
      have hwt : ∀ x ∈ t, 0 ≤ w x := fun x hx => hw x (Finset.mem_insert_of_mem hx)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        integral_add_measure
          (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))
          (integrable_finsetWeightedDirac t w f),
        integral_smul_measure, integral_dirac, ih hwt, ENNReal.toReal_ofReal hwa, smul_eq_mul]

/-- **The quasi-orthogonal quadrature measure.** -/
noncomputable def quasiMeasure (s : ℕ → ℝ) (n : ℕ) (t : ℝ) : Measure ℝ :=
  ∑ x ∈ quasiNodes s n t, ENNReal.ofReal (quasiWeight s n t x) • Measure.dirac x

theorem integrable_quasiMeasure (n : ℕ) (t : ℝ) (f : ℝ → ℝ) :
    Integrable f (quasiMeasure s n t) :=
  integrable_finsetWeightedDirac _ _ f

/-- Integration against the quasi measure is the quadrature sum. -/
theorem integral_quasiMeasure (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(quasiMeasure s n t)
      = ∑ x ∈ quasiNodes s n t, quasiWeight s n t x * f x :=
  integral_finsetWeightedDirac_of_mem _ _ (fun _ hx => (quasiWeight_pos h n t hx).le) f

/-- **The quasi measure reproduces the moments up to order `2n`.** -/
theorem quasiMeasure_moment (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (k : ℕ)
    (hk : k ≤ 2 * n) : ∫ x, x ^ k ∂(quasiMeasure s n t) = s k := by
  rw [integral_quasiMeasure h n t fun x => x ^ k]
  have hdeg : (Polynomial.X ^ k : Polynomial ℝ).degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast hk
  have hq := momentFunctional_eq_quasiSum h n t (Polynomial.X ^ k) hdeg
  rw [momentFunctional_X_pow s k] at hq
  rw [hq]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

/-- The total mass of the quasi measure is the zeroth moment. -/
theorem quasiMeasure_mass (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    ∫ _x, (1 : ℝ) ∂(quasiMeasure s n t) = s 0 := by
  have hk := quasiMeasure_moment h n t 0 (by omega)
  simpa using hk

/-- The total mass of a finite weighted Dirac family is the sum of its weights. -/
theorem measure_univ_finsetWeightedDirac (t : Finset ℝ) (w : ℝ → ℝ) :
    (∑ y ∈ t, ENNReal.ofReal (w y) • Measure.dirac y) Set.univ
      = ∑ y ∈ t, ENNReal.ofReal (w y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_apply, ih]
      simp

/-- The quasi measure is finite. -/
instance isFiniteMeasure_quasiMeasure (s : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    IsFiniteMeasure (quasiMeasure s n t) := by
  constructor
  rw [quasiMeasure, measure_univ_finsetWeightedDirac]
  exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top

end HTGeometry
