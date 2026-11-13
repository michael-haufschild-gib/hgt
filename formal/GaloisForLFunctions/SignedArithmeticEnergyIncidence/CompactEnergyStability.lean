import GaloisForLFunctions.SignedArithmeticEnergyIncidence.QuadraticMomentStability
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheRestrictedWeilFormIsCompactlyNegative
import GaloisForLFunctions.RHTower.CorrelationBoundsCountNotLocation
import Mathlib.Tactic.GCongr

/-!
# Quantitative stability of compactly perturbed energies

The mixed-plus-quadratic moment estimate controls the existing compact
energy and the actual restricted Weil form. The sharper bound measures
the error after the physical embedding. Operator approximation has a
separate norm cost, as required when passing from finite spectral models
to the underlying form.
-/

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Source error and physically observed error contribute separately. -/
theorem compactPerturbedEnergy_sub_le (J : E →L[ℂ] F) (R : F →L[ℂ] F) (u v : E) :
    |compactPerturbedEnergy J R u - compactPerturbedEnergy J R v| ≤
      (2 * ‖v‖ * ‖u - v‖ + ‖u - v‖ ^ 2) +
        ‖R‖ * (2 * ‖J v‖ * ‖J u - J v‖ + ‖J u - J v‖ ^ 2) := by
  have hn : |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 2 * ‖v‖ * ‖u - v‖ + ‖u - v‖ ^ 2 := by
    simpa only [← add_sub_assoc, add_sub_cancel_left] using
      RHTower.sq_norm_perturbation v (u - v)
  have he : compactPerturbedEnergy J R u - compactPerturbedEnergy J R v =
      (‖u‖ ^ 2 - ‖v‖ ^ 2) +
        (inner ℂ (R (J u)) (J u) - inner ℂ (R (J v)) (J v)).re := by
    simp only [compactPerturbedEnergy, Complex.sub_re]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hn
    ((Complex.abs_re_le_norm _).trans (norm_operator_quadratic_sub_le R (J u) (J v))))

/-- A uniform source-norm bound for the compactly perturbed energy. -/
theorem compactPerturbedEnergy_sub_le_source (J : E →L[ℂ] F) (R : F →L[ℂ] F) (u v : E) :
    |compactPerturbedEnergy J R u - compactPerturbedEnergy J R v| ≤
      (1 + ‖R‖ * ‖J‖ ^ 2) * (2 * ‖v‖ * ‖u - v‖ + ‖u - v‖ ^ 2) := by
  refine (compactPerturbedEnergy_sub_le J R u v).trans ?_
  rw [← map_sub]
  calc
    _ ≤ (2 * ‖v‖ * ‖u - v‖ + ‖u - v‖ ^ 2) +
        ‖R‖ * (2 * (‖J‖ * ‖v‖) * (‖J‖ * ‖u - v‖) + (‖J‖ * ‖u - v‖) ^ 2) := by
      gcongr <;> exact J.le_opNorm _
    _ = _ := by ring

/-- An approximation to the remainder operator has an explicit quadratic cost. -/
theorem compactPerturbedEnergy_operator_sub_le
    (J : E →L[ℂ] F) (R S : F →L[ℂ] F) (u : E) :
    |compactPerturbedEnergy J R u - compactPerturbedEnergy J S u| ≤
      ‖R - S‖ * ‖J u‖ ^ 2 := by
  have he : compactPerturbedEnergy J R u - compactPerturbedEnergy J S u =
      (inner ℂ ((R - S) (J u)) (J u)).re := by
    simp only [compactPerturbedEnergy, ContinuousLinearMap.sub_apply,
      inner_sub_left, Complex.sub_re]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℂ ((R - S) (J u)) (J u)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖R - S‖ * ‖J u‖ * ‖J u‖ := norm_operator_pairing_le (R - S) (J u) (J u)
    _ = _ := by ring

/-- The actual restricted Weil form obeys the moment estimate at every aperture. -/
theorem re_ccmRestrictedWeilForm_difference_le (a : RHTower.SuzukiPositiveAperture)
    (u v : RHTower.CCMArchimedeanFormDomain a) :
    |(RHTower.ccmRestrictedWeilForm a u u).re -
        (RHTower.ccmRestrictedWeilForm a v v).re| ≤
      (1 + ‖RHTower.ccmRestrictedWeilBoundedRemainder a‖ *
        ‖RHTower.ccmArchimedeanFormToAperture a‖ ^ 2) *
          (2 * ‖v‖ * ‖u - v‖ + ‖u - v‖ ^ 2) := by
  rw [re_ccmRestrictedWeilForm_eq, re_ccmRestrictedWeilForm_eq]
  exact compactPerturbedEnergy_sub_le_source _ _ u v

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
