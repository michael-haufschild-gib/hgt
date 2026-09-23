import GaloisForLFunctions.HTGeometry.VenezianoGammaRatioBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Virasoro--Shapiro closed-string differential boundary

After one crossed channel is fixed and its constant Gamma factor is removed, the
Virasoro--Shapiro four-tachyon amplitude has variable-channel core

`Gamma(z+a) Gamma(1-z-a-b) / (Gamma(1-z-a) Gamma(z+a+b))`.

Euler reflection identifies this core with a nonzero differentially algebraic sine gauge times
the square of the reduced Veneziano amplitude.  Consequently open/closed string double copy
doubles the Gamma-orbit charge without changing its cancellation lattice: the reduced closed
amplitude is differentially algebraic exactly when the fixed channel separation is integral, and
is hypertranscendental otherwise.

The physical Gamma formula is the closed-bosonic-string four-tachyon Virasoro--Shapiro amplitude;
the KLT interpretation is external to Lean.  Every differential-algebraic statement below is an
unconditional equality or classification in the genuine meromorphic function field.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The variable-channel core of the Virasoro--Shapiro amplitude after the fixed factor
`Gamma(b) / Gamma(1-b)` is removed.  Its three Gamma arguments obey the mass-shell relation
`(z+a) + b + (1-z-a-b) = 1`. -/
def reducedVirasoroShapiroAmplitudeMero (a b : ℂ) : meroField Set.univ :=
  (gammaShiftMero a * gammaNegativeShiftMero (1 - a - b)) /
    (gammaNegativeShiftMero (1 - a) * gammaShiftMero (a + b))

/-- The nonzero sine quotient left by reflecting both negative-orientation Gamma factors. -/
def virasoroShapiroReflectionGaugeMero (a b : ℂ) : meroField Set.univ :=
  gammaReflectionGaugeMero (1 - a - b) /
    gammaReflectionGaugeMero (1 - a)

theorem virasoroShapiroReflectionGaugeMero_ne_zero (a b : ℂ) :
    virasoroShapiroReflectionGaugeMero a b ≠ 0 := by
  exact div_ne_zero (gammaReflectionGaugeMero_ne_zero (1 - a - b))
    (gammaReflectionGaugeMero_ne_zero (1 - a))

theorem differentialAlgebraicOver_virasoroShapiroReflectionGaugeMero (a b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (virasoroShapiroReflectionGaugeMero a b) := by
  exact HTGeometry.differentialAlgebraicOver_div
    (differentialAlgebraicOver_gammaReflectionGaugeMero (1 - a - b))
    (differentialAlgebraicOver_gammaReflectionGaugeMero (1 - a))

/-- **Closed/open double-copy normal form.**  Euler reflection turns the reduced closed-string
amplitude into a nonzero DA gauge times the square of the reduced open-string amplitude. -/
theorem reducedVirasoroShapiroAmplitudeMero_eq_gauge_mul_veneziano_sq (a b : ℂ) :
    reducedVirasoroShapiroAmplitudeMero a b =
      virasoroShapiroReflectionGaugeMero a b *
        reducedVenezianoAmplitudeMero a b ^ (2 : ℕ) := by
  rw [reducedVirasoroShapiroAmplitudeMero,
    virasoroShapiroReflectionGaugeMero,
    reducedVenezianoAmplitudeMero,
    gammaNegativeShiftMero_reflection,
    gammaNegativeShiftMero_reflection]
  rw [show 1 - (1 - a - b) = a + b by ring,
    show 1 - (1 - a) = a by ring]
  have hga : gammaShiftMero a ≠ 0 := gammaShiftMero_ne_zero a
  have hgab : gammaShiftMero (a + b) ≠ 0 := gammaShiftMero_ne_zero (a + b)
  have hgauge : gammaReflectionGaugeMero (1 - a) ≠ 0 :=
    gammaReflectionGaugeMero_ne_zero (1 - a)
  field_simp [hga, hgab, hgauge]

theorem differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_of_integerShift
    (a b : ℂ) (hinteger : ∃ k : ℤ, b = (k : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (reducedVirasoroShapiroAmplitudeMero a b) := by
  rw [reducedVirasoroShapiroAmplitudeMero_eq_gauge_mul_veneziano_sq]
  exact HTGeometry.differentialAlgebraicOver_mul
    (differentialAlgebraicOver_virasoroShapiroReflectionGaugeMero a b)
    (HTGeometry.differentialAlgebraicOver_pow
      ((differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
        a b).2 hinteger) 2)

theorem hypertranscendentalOver_reducedVirasoroShapiroAmplitudeMero_of_nonintegerShift
    (a b : ℂ) (hnoninteger : ∀ k : ℤ, b ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (reducedVirasoroShapiroAmplitudeMero a b) := by
  rw [reducedVirasoroShapiroAmplitudeMero_eq_gauge_mul_veneziano_sq]
  have hsq : HypertranscendentalOver (RatFunc ℂ)
      (reducedVenezianoAmplitudeMero a b ^ (2 : ℕ)) :=
    HTGeometry.hypertranscendentalOver_pow_of_pos (N := 2)
    ((hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift
      a b).2 hnoninteger) (by norm_num)
  have hproduct : HypertranscendentalOver (RatFunc ℂ)
      (reducedVenezianoAmplitudeMero a b ^ (2 : ℕ) *
        virasoroShapiroReflectionGaugeMero a b) :=
    (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_virasoroShapiroReflectionGaugeMero a b)
      (virasoroShapiroReflectionGaugeMero_ne_zero a b)).2 hsq
  simpa [mul_comm] using hproduct

/-- **Exact closed-string differential boundary.**  The reduced Virasoro--Shapiro channel is
differentially algebraic exactly on the integer crossed-channel lattice. -/
theorem differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_iff_integerShift
    (a b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (reducedVirasoroShapiroAmplitudeMero a b) ↔
      ∃ k : ℤ, b = (k : ℂ) := by
  constructor
  · intro hDA
    by_contra hnoninteger
    push Not at hnoninteger
    exact hypertranscendentalOver_reducedVirasoroShapiroAmplitudeMero_of_nonintegerShift
      a b hnoninteger hDA
  · exact
      differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_of_integerShift a b

/-- Open and closed four-point Gamma amplitudes have the same noninteger HT sector: double copy
doubles the orbit charge but creates no new cancellation locus. -/
theorem hypertranscendentalOver_reducedVirasoroShapiroAmplitudeMero_iff_nonintegerShift
    (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (reducedVirasoroShapiroAmplitudeMero a b) ↔
      ∀ k : ℤ, b ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_iff_integerShift]
  push Not
  rfl

/-- **Open/closed differential-algebra equivalence.**  The reduced open- and closed-string
four-point channels are differentially algebraic on exactly the same parameter locus. -/
theorem differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_iff_veneziano
    (a b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (reducedVirasoroShapiroAmplitudeMero a b) ↔
      DifferentialAlgebraicOver (RatFunc ℂ)
        (reducedVenezianoAmplitudeMero a b) := by
  rw [differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_iff_integerShift,
    differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift]

/-- The corresponding open/closed equivalence holds in the complementary
hypertranscendental sector. -/
theorem hypertranscendentalOver_reducedVirasoroShapiroAmplitudeMero_iff_veneziano
    (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (reducedVirasoroShapiroAmplitudeMero a b) ↔
      HypertranscendentalOver (RatFunc ℂ)
        (reducedVenezianoAmplitudeMero a b) := by
  rw [hypertranscendentalOver_reducedVirasoroShapiroAmplitudeMero_iff_nonintegerShift,
    hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift]

end

end GaloisForLFunctions
