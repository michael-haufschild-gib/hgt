import GaloisForLFunctions.HTGeometry.BarnesCotangentSingularityThreshold
import GaloisForLFunctions.HTGeometry.MeromorphicGammaSuperselection
import GaloisForLFunctions.HTGeometry.FiniteCommutingShiftPeeling
import GaloisForLFunctions.HTGeometry.PolynomialOnePointRecession
import GaloisForLFunctions.HTGeometry.KolchinFrequencyBudgetPhase

/-!
# Gamma phase completion

This module joins the genuine meromorphic Gamma superselection theorem to the remaining named
classical inputs: all-order multiple-sine hypertranscendence, the ADH one-shift Laurent dichotomy
plus scaled-Borel charge selector, and the neutral Gamma-ratio Poincare-field boundary theorem.
No classical result is installed as an axiom.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology
open scoped Topology

noncomputable section

universe u

/-- The analytic parent theorem for the Barnes hierarchy, at the exact interface needed to compare
it with the internally checked cotangent threshold. -/
structure BarnesReflectionAnalyticThresholdInput where
  multipleSineHypertranscendental : ℕ → Prop
  logDerivHypertranscendental : ℕ → Prop
  sine_threshold : ∀ N,
    multipleSineHypertranscendental N ↔ 2 ≤ N
  logDeriv_threshold : ∀ N,
    logDerivHypertranscendental N ↔ 2 ≤ N

/-- The analytic multiple-sine threshold is exactly the intrinsic cotangent-singularity threshold,
and the sine/logarithmic-derivative formulations agree. -/
theorem barnesReflection_cotangentSingularity_exactThreshold
    {F : Type*} [Field F]
    (input : BarnesReflectionAnalyticThresholdInput) (r : ℕ) :
    (input.multipleSineHypertranscendental (r + 1) ↔
      input.logDerivHypertranscendental (r + 1)) ∧
    (input.logDerivHypertranscendental (r + 1) ↔
      GaloisForLFunctions.VeroneseIdeal.derivationalCriticalIdeal (R := F)
        (GaloisForLFunctions.VeroneseIdeal.normalCrossingPolynomial
          (F := F) r) ≠ ⊤) ∧
    (GaloisForLFunctions.VeroneseIdeal.derivationalCriticalIdeal (R := F)
        (GaloisForLFunctions.VeroneseIdeal.normalCrossingPolynomial
          (F := F) r) ≠ ⊤ ↔ 2 ≤ r + 1) := by
  have hcritical :=
    GaloisForLFunctions.VeroneseIdeal.normalCrossingCotangentSingularityThreshold
      (F := F) r
  exact ⟨(input.sine_threshold (r + 1)).trans
      (input.logDeriv_threshold (r + 1)).symm,
    (input.logDeriv_threshold (r + 1)).trans hcritical.symm,
    hcritical⟩

/-- Abstract arbitrary-scale Gamma classification at its exact reusable boundary.  The finite
shift word is proved by the project; `oneShiftDichotomy` is the ADH Laurent theorem and
`nonzeroCharge_excludesRational` is the scaled-Borel-residue calculation. -/
theorem alienCharge_shiftWord_classification
    {X : Type u} {n : ℕ}
    (Delta : Fin n → X → X) (Rational Hypertranscendental : X → Prop)
    (word : List (Fin n)) (f : X)
    (oneShiftDichotomy : ∀ (i : Fin n) (g : X),
      Rational (Delta i g) → Rational g ∨ Hypertranscendental g)
    (htDown : ∀ (i : Fin n) (g : X),
      Hypertranscendental (Delta i g) → Hypertranscendental g)
    (word_rational : Rational (_root_.HTGeometry.shiftWord Delta word f))
    (chargeZero : Prop)
    (zeroCharge_rational : chargeZero → Rational f)
    (nonzeroCharge_excludesRational : ¬ chargeZero → ¬ Rational f) :
    (chargeZero → Rational f) ∧
      (¬ chargeZero → Hypertranscendental f) ∧
      (Rational f ∨ Hypertranscendental f) := by
  have hdich : Rational f ∨ Hypertranscendental f :=
    _root_.HTGeometry.shiftWord_dichotomy
      oneShiftDichotomy htDown word f word_rational
  refine ⟨zeroCharge_rational, ?_, hdich⟩
  intro hcharge
  rcases hdich with hrational | hht
  · exact (nonzeroCharge_excludesRational hcharge hrational).elim
  · exact hht

/-- Exact functional-projective polynomial boundary property used by the neutral Gamma-ratio
field.  It quantifies over every finite nonzero coefficient tuple and every upper-height sequence,
including the common meromorphic normalization and a nonzero polynomial limit tuple. -/
def HasPolynomialFunctionalProjectiveBoundary
    (K : Set (ℂ → ℂ)) : Prop :=
  ∀ {r : ℕ} (a : Fin r → ℂ → ℂ)
    (_haK : ∀ j, a j ∈ K) (_ha : ∃ j, a j ≠ 0)
    (S : ℕ → ℝ) (_hS : Tendsto S atTop atTop),
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ normalization : ℕ → ℂ → ℂ,
      ∃ limit : Fin r → Polynomial ℂ,
        (∃ j, limit j ≠ 0) ∧
        ∀ j, TendstoLocallyUniformly
          (fun k z => normalization k z *
            a j (z + Complex.I * (S (phi k) : ℂ)))
          (fun z => (limit j).eval z) atTop

/-- The neutral Gamma-ratio boundary has two checked stages: the named Poincare-field theorem gives
the polynomial carrier, and the internal recession theorem sends every nonzero polynomial tuple to
a nonzero constant leading-coefficient vector. -/
theorem neutralGammaRatio_twoStageBoundary
    (K : Set (ℂ → ℂ))
    (hfirst : HasPolynomialFunctionalProjectiveBoundary K) :
    HasPolynomialFunctionalProjectiveBoundary K ∧
      ∀ {r : ℕ} (p : Fin r → Polynomial ℂ), (∃ j, p j ≠ 0) →
        ∃ d : ℕ, (∃ j, (p j).coeff d ≠ 0) ∧
          ∀ (z : ℂ) (j : Fin r),
            Tendsto
              (fun T : ℝ =>
                (p j).eval (z + Complex.I * (T : ℂ)) /
                  (Complex.I * (T : ℂ)) ^ d)
              atTop (𝓝 ((p j).coeff d)) := by
  refine ⟨hfirst, ?_⟩
  intro r p hp
  exact _root_.HTGeometry.finiteTuple_polynomial_onePoint_recession p hp

end

end GaloisForLFunctions.HTGeometry
