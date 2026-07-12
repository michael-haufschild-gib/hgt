import GaloisForLFunctions.HTGeometry.GraphSaturationCore
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The analytic-polynomial graph on a circle measure

This module instantiates the abstract graph-saturation core for the polynomial synthesis map
from finitely supported coefficient sequences to `L²` of a finite circle measure.  It proves that
the joint annihilator may be tested on monomials alone.  The remaining singular-measure input is
the one-sided Fourier rigidity theorem; it is deliberately not encoded as an assumption about
the graph closure.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable instance : MeasurableSpace Circle := borel Circle
instance : BorelSpace Circle := ⟨rfl⟩
instance : OpensMeasurableSpace Circle := ⟨le_rfl⟩

/-- The coefficient Hilbert space `ℓ²(ℕ)`. -/
abbrev CoefficientL2 := lp (fun _ : ℕ => ℂ) 2

/-- The canonical inclusion of finitely supported coefficient sequences into `ℓ²(ℕ)`. -/
noncomputable def finsuppCoefficientL2 : (ℕ →₀ ℂ) →ₗ[ℂ] CoefficientL2 :=
  Finsupp.lsum ℂ (fun n => lp.lsingle (E := fun _ : ℕ => ℂ) 2 n)

@[simp]
theorem finsuppCoefficientL2_single (n : ℕ) (c : ℂ) :
    finsuppCoefficientL2 (Finsupp.single n c) = lp.single 2 n c := by
  simp [finsuppCoefficientL2]

/-- The `n`th analytic monomial as an element of `L²(μ)`. -/
noncomputable def circleMonomialLp (mu : Measure Circle) [IsFiniteMeasure mu] (n : ℕ) :
    Lp ℂ 2 mu :=
  MemLp.toLp (fun z : Circle => (z : ℂ) ^ n)
    (MemLp.of_bound
      ((by fun_prop : Continuous (fun z : Circle => (z : ℂ) ^ n)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun z => by simp [norm_pow]))

/-- Analytic-polynomial synthesis in `L²(μ)`. -/
noncomputable def polynomialSynthesisL2 (mu : Measure Circle) [IsFiniteMeasure mu] :
    (ℕ →₀ ℂ) →ₗ[ℂ] Lp ℂ 2 mu :=
  Finsupp.lsum ℂ (fun n => LinearMap.toSpanSingleton ℂ _ (circleMonomialLp mu n))

@[simp]
theorem polynomialSynthesisL2_single (mu : Measure Circle) [IsFiniteMeasure mu]
    (n : ℕ) (c : ℂ) :
    polynomialSynthesisL2 mu (Finsupp.single n c) = c • circleMonomialLp mu n := by
  simp [polynomialSynthesisL2]

/-- Testing the joint annihilator on the monomial basis is equivalent to testing it on every
finitely supported polynomial. -/
theorem polynomial_annihilator_of_monomial_annihilator
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (x : CoefficientL2) (y : Lp ℂ 2 mu)
    (hmono : ∀ n : ℕ,
      inner ℂ (lp.single 2 n 1) x + inner ℂ (circleMonomialLp mu n) y = 0) :
    ∀ d : ℕ →₀ ℂ,
      inner ℂ (finsuppCoefficientL2 d) x + inner ℂ (polynomialSynthesisL2 mu d) y = 0 := by
  intro d
  induction d using Finsupp.induction with
  | zero => simp
  | single_add n c d hn hc ih =>
      have hsingle :
          (lp.single (E := fun _ : ℕ => ℂ) 2 n c : CoefficientL2) =
            c • lp.single 2 n 1 := by
        apply lp.ext
        funext j
        simp [lp.single_apply, Pi.single_apply]
      simp only [map_add, finsuppCoefficientL2_single, polynomialSynthesisL2_single,
        inner_add_left, inner_smul_left]
      rw [hsingle]
      simp only [inner_smul_left]
      calc
        (starRingEnd ℂ) c * inner ℂ (lp.single 2 n 1) x +
              inner ℂ (finsuppCoefficientL2 d) x +
            ((starRingEnd ℂ) c * inner ℂ (circleMonomialLp mu n) y +
              inner ℂ (polynomialSynthesisL2 mu d) y) =
            (starRingEnd ℂ) c *
                (inner ℂ (lp.single 2 n 1) x + inner ℂ (circleMonomialLp mu n) y) +
              (inner ℂ (finsuppCoefficientL2 d) x +
                inner ℂ (polynomialSynthesisL2 mu d) y) := by ring
        _ = 0 := by rw [hmono n, ih]; ring

/-- **Polynomial graph-saturation reduction.** It suffices to prove that the monomial joint
annihilator is trivial.  This is the exact interface at which one-sided Fourier rigidity enters. -/
theorem polynomialGraph_closure_eq_top_of_monomial_annihilator
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hann : ∀ x : CoefficientL2, ∀ y : Lp ℂ 2 mu,
      (∀ n : ℕ,
        inner ℂ (lp.single 2 n 1) x + inner ℂ (circleMonomialLp mu n) y = 0) →
      x = 0 ∧ y = 0) :
    (linearGraphSubmodule finsuppCoefficientL2 (polynomialSynthesisL2 mu)).topologicalClosure =
      ⊤ := by
  apply linearGraphSubmodule_closure_eq_top_of_annihilator
  intro x y hall
  apply hann x y
  intro n
  simpa using hall (Finsupp.single n 1)

end

end GaloisForLFunctions.HTGeometry
