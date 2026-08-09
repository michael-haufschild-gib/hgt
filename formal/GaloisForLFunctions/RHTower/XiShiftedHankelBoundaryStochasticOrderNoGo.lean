import GaloisForLFunctions.HTGeometry.MonotoneLikelihoodRatio
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryFactorialRootThresholdNoGo

/-!
# Stochastic-order collapse on a shifted-Hankel null face

The ordinary monotone-likelihood route cannot orient the first omitted shifted-Xi coupling.
Abstractly, `monotoneLikelihoodKernel_ae_eq_zero_of_equal_mass_moment` says that equal visible
mass and tested moment saturate every nonnegative two-sample likelihood kernel.

This file closes the route-specific obstruction.  The two exact positive squared-factorial
carriers already known to share one singular face have crossing upper tails, so neither first-order
stochastically dominates the other.  Moreover the actual adaptive observable

`t^2 P^sharp(t) = t^2 (t - 9) / 36`

is neither monotone nor antitone on the positive ray.  Thus first stochastic order has neither an
ordered carrier pair nor an admissible observable at this face.  Higher-order order specialized to
the first unseen monomial is the already formalized boundary extension coordinate itself, not an
independent sign producer.
-/

open Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Strict upper-tail mass of a finite squared-factorial carrier. -/
def squaredFactorialCarrierUpperTailMass
    (weight node : Fin 2 → ℝ) (threshold : ℝ) : ℝ :=
  ∑ i : Fin 2, if threshold < node i then weight i else 0

/-- First-order upper-tail dominance for the finite carriers used at the boundary face. -/
def squaredFactorialCarrierUpperTailDominates
    (weight₁ node₁ weight₂ node₂ : Fin 2 → ℝ) : Prop :=
  ∀ threshold : ℝ,
    squaredFactorialCarrierUpperTailMass weight₂ node₂ threshold ≤
      squaredFactorialCarrierUpperTailMass weight₁ node₁ threshold

@[simp] theorem squaredFactorialPositiveCarrierUpperTailMass_fiveEighths :
    squaredFactorialCarrierUpperTailMass squaredFactorialPositiveCarrierWeight
      squaredFactorialPositiveCarrierNode (5 / 8) = 1 := by
  norm_num [squaredFactorialCarrierUpperTailMass,
    squaredFactorialPositiveCarrierWeight, squaredFactorialPositiveCarrierNode,
    Fin.sum_univ_two]

@[simp] theorem squaredFactorialNegativeCarrierUpperTailMass_fiveEighths :
    squaredFactorialCarrierUpperTailMass squaredFactorialNegativeCarrierWeight
      squaredFactorialNegativeCarrierNode (5 / 8) = 1 / 13 := by
  norm_num [squaredFactorialCarrierUpperTailMass,
    squaredFactorialNegativeCarrierWeight, squaredFactorialNegativeCarrierNode,
    Fin.sum_univ_two]

@[simp] theorem squaredFactorialPositiveCarrierUpperTailMass_one :
    squaredFactorialCarrierUpperTailMass squaredFactorialPositiveCarrierWeight
      squaredFactorialPositiveCarrierNode 1 = 1 / 49 := by
  norm_num [squaredFactorialCarrierUpperTailMass,
    squaredFactorialPositiveCarrierWeight, squaredFactorialPositiveCarrierNode,
    Fin.sum_univ_two]

@[simp] theorem squaredFactorialNegativeCarrierUpperTailMass_one :
    squaredFactorialCarrierUpperTailMass squaredFactorialNegativeCarrierWeight
      squaredFactorialNegativeCarrierNode 1 = 1 / 13 := by
  norm_num [squaredFactorialCarrierUpperTailMass,
    squaredFactorialNegativeCarrierWeight, squaredFactorialNegativeCarrierNode,
    Fin.sum_univ_two]

/-- The common-face carriers' upper tails cross: neither law first-order stochastically dominates
the other. -/
theorem squaredFactorialCarriers_not_upperTailComparable :
    ¬ squaredFactorialCarrierUpperTailDominates
        squaredFactorialPositiveCarrierWeight squaredFactorialPositiveCarrierNode
        squaredFactorialNegativeCarrierWeight squaredFactorialNegativeCarrierNode ∧
    ¬ squaredFactorialCarrierUpperTailDominates
        squaredFactorialNegativeCarrierWeight squaredFactorialNegativeCarrierNode
        squaredFactorialPositiveCarrierWeight squaredFactorialPositiveCarrierNode := by
  constructor
  · intro hdom
    have h := hdom 1
    simp only [squaredFactorialPositiveCarrierUpperTailMass_one,
      squaredFactorialNegativeCarrierUpperTailMass_one] at h
    norm_num at h
  · intro hdom
    have h := hdom (5 / 8)
    simp only [squaredFactorialPositiveCarrierUpperTailMass_fiveEighths,
      squaredFactorialNegativeCarrierUpperTailMass_fiveEighths] at h
    norm_num at h

/-- Adaptive observable tested by the positive carrier on the first hostile null face. -/
def squaredFactorialCarrierNoGoAdaptiveTest (t : ℝ) : ℝ :=
  t ^ 2 * xiShiftedBoundaryFactorialCarrierPolynomial 2
    squaredFactorialCarrierNoGoKernel t

@[simp] theorem squaredFactorialCarrierNoGoAdaptiveTest_zero :
    squaredFactorialCarrierNoGoAdaptiveTest 0 = 0 := by
  simp [squaredFactorialCarrierNoGoAdaptiveTest]

@[simp] theorem squaredFactorialCarrierNoGoAdaptiveTest_three :
    squaredFactorialCarrierNoGoAdaptiveTest 3 = -(3 / 2) := by
  rw [squaredFactorialCarrierNoGoAdaptiveTest,
    squaredFactorialCarrierNoGoPolynomial_eq]
  norm_num

@[simp] theorem squaredFactorialCarrierNoGoAdaptiveTest_six :
    squaredFactorialCarrierNoGoAdaptiveTest 6 = -3 := by
  rw [squaredFactorialCarrierNoGoAdaptiveTest,
    squaredFactorialCarrierNoGoPolynomial_eq]
  norm_num

@[simp] theorem squaredFactorialCarrierNoGoAdaptiveTest_nine :
    squaredFactorialCarrierNoGoAdaptiveTest 9 = 0 := by
  rw [squaredFactorialCarrierNoGoAdaptiveTest,
    squaredFactorialCarrierNoGoPolynomial_eq]
  norm_num

/-- The adaptive root-threshold observable is not monotone on the positive ray. -/
theorem squaredFactorialCarrierNoGoAdaptiveTest_not_monotoneOn :
    ¬ MonotoneOn squaredFactorialCarrierNoGoAdaptiveTest (Set.Ici 0) := by
  intro hmono
  have h03 := hmono (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show (3 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num : (0 : ℝ) ≤ 3)
  norm_num at h03

/-- The same adaptive observable is not antitone on the positive ray. -/
theorem squaredFactorialCarrierNoGoAdaptiveTest_not_antitoneOn :
    ¬ AntitoneOn squaredFactorialCarrierNoGoAdaptiveTest (Set.Ici 0) := by
  intro hanti
  have h69 := hanti (show (6 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (9 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num : (6 : ℝ) ≤ 9)
  norm_num at h69

/-- **Closed stochastic-order orientation no-go.**  The exact carriers agree on the entire visible
size-two moment face, but their upper tails cross; the adaptive test is outside both monotone cones;
and their first Krein crossings have opposite signs.  Ordinary likelihood-ratio/first stochastic
order therefore cannot supply the missing strict boundary orientation. -/
theorem squaredFactorialCarrierStochasticOrderOrientationNoGo :
    (∀ k : Fin 3,
      squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
          squaredFactorialPositiveCarrierNode k =
        squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
          squaredFactorialNegativeCarrierNode k) ∧
    (¬ squaredFactorialCarrierUpperTailDominates
        squaredFactorialPositiveCarrierWeight squaredFactorialPositiveCarrierNode
        squaredFactorialNegativeCarrierWeight squaredFactorialNegativeCarrierNode ∧
      ¬ squaredFactorialCarrierUpperTailDominates
        squaredFactorialNegativeCarrierWeight squaredFactorialNegativeCarrierNode
        squaredFactorialPositiveCarrierWeight squaredFactorialPositiveCarrierNode) ∧
    ¬ MonotoneOn squaredFactorialCarrierNoGoAdaptiveTest (Set.Ici 0) ∧
    ¬ AntitoneOn squaredFactorialCarrierNoGoAdaptiveTest (Set.Ici 0) ∧
    HTGeometry.finiteHankelBoundaryNullCrossingForm
      (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
        squaredFactorialPositiveCarrierNode) squaredFactorialCarrierNoGoKernel = 37 / 144 ∧
    HTGeometry.finiteHankelBoundaryNullCrossingForm
      (squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
        squaredFactorialNegativeCarrierNode) squaredFactorialCarrierNoGoKernel = -(19 / 72) := by
  refine ⟨?_, squaredFactorialCarriers_not_upperTailComparable,
    squaredFactorialCarrierNoGoAdaptiveTest_not_monotoneOn,
    squaredFactorialCarrierNoGoAdaptiveTest_not_antitoneOn,
    squaredFactorialPositiveCarrier_crossing,
    squaredFactorialNegativeCarrier_crossing⟩
  intro k
  fin_cases k <;> simp

end

end RHTower
