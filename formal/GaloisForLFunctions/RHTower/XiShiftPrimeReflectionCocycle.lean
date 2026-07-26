import GaloisForLFunctions.HTGeometry.AdditiveReflectionCocycleHalving
import GaloisForLFunctions.RHTower.ReflectionDifferenceFaces
import GaloisForLFunctions.RHTower.XiUpperEndHypertranscendence
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Reflection centering of the xi shift-two prime defect

The functional equation makes `logDeriv xi` anti-invariant about `1 / 2`.  The general
finite-difference reflection law therefore makes its raw `+2` defect invariant about `-1 / 2`.
The explicit archimedean correction is not invariant: it contributes the rational reflection
cocycle `1 / s + 1 / (s + 1)`.  Adding half of this anti-invariant cocycle produces an exactly
reflection-fixed prime defect.

On the upper end, the half-cocycle belongs to the genuine rational coordinate field.  The centered
carrier is consequently the filtered von Mangoldt carrier plus a differential-algebraic base
element, so it remains hypertranscendental unconditionally.
-/

namespace RHTower

open Complex Filter
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

open scoped UpperEndDifferentialInstances
open scoped UpperEndComplexTowerInstances

/-- The globally defined rationally corrected `+2` defect of `xi'/xi`.  On `re s > 1` this is
the filtered von Mangoldt L-series. -/
noncomputable def xiShiftTwoPrimeDefect (s : ℂ) : ℂ :=
  logDeriv xi (s + 2) - logDeriv xi s -
    (1 / (s + 2) + 1 / (s + 1) - 1 / (s - 1))

/-- The rational cocycle contributed by reflecting the archimedean correction about `-1 / 2`. -/
noncomputable def xiShiftTwoReflectionCocycle (s : ℂ) : ℂ :=
  1 / s + 1 / (s + 1)

/-- Half-cocycle centering of the filtered prime defect. -/
noncomputable def xiCenteredShiftTwoPrimeDefect (s : ℂ) : ℂ :=
  xiShiftTwoPrimeDefect s + (1 / 2 : ℂ) * xiShiftTwoReflectionCocycle s

/-- The raw `+2` logarithmic difference is reflection-fixed about `-1 / 2`. -/
theorem xiLogDerivShiftTwoDefect_reflection (s : ℂ) :
    logDeriv xi ((-1 - s) + 2) - logDeriv xi (-1 - s) =
      logDeriv xi (s + 2) - logDeriv xi s := by
  have hsym : ∀ z : ℂ,
      logDeriv xi (2 * (1 / 2 : ℂ) - z) = (-1 : ℂ) * logDeriv xi z := by
    intro z
    convert logDeriv_xi_reciprocity z using 1 <;> ring_nf
  have h := forwardDifference_signed_reflection
    (f := logDeriv xi) (c := (1 / 2 : ℂ)) (ε := (-1 : ℂ)) (τ := (2 : ℂ)) hsym s
  rw [show 2 * ((1 / 2 : ℂ) - 2 / 2) - s = -1 - s by ring_nf] at h
  simpa [forwardDifference] using h

/-- The reflection cocycle is anti-invariant about `-1 / 2`. -/
theorem xiShiftTwoReflectionCocycle_reflection (s : ℂ) :
    xiShiftTwoReflectionCocycle (-1 - s) = -xiShiftTwoReflectionCocycle s := by
  rw [xiShiftTwoReflectionCocycle, xiShiftTwoReflectionCocycle,
    show -1 - s + 1 = -s by ring_nf,
    show -1 - s = -(s + 1) by ring_nf]
  simp only [one_div, inv_neg]
  ring_nf

/-- The shift-two rational cocycle vanishes at the reflection center `-1/2`. -/
theorem xiShiftTwoReflectionCocycle_center :
    xiShiftTwoReflectionCocycle (-1 / 2) = 0 := by
  apply IsAdditiveReflectionCocycle.eq_zero_of_fixed
    xiShiftTwoReflectionCocycle_reflection
  ring

/-- **Exact shift-two reflection cocycle.**  The filtered prime defect changes under
`s ↦ -1-s` by the explicit rational cocycle `1/s + 1/(s+1)`. -/
theorem xiShiftTwoPrimeDefect_reflection_cocycle (s : ℂ) :
    xiShiftTwoPrimeDefect (-1 - s) =
      xiShiftTwoPrimeDefect s + xiShiftTwoReflectionCocycle s := by
  have hraw := xiLogDerivShiftTwoDefect_reflection s
  have hcorrection :
      1 / ((-1 - s) + 2) + 1 / ((-1 - s) + 1) - 1 / ((-1 - s) - 1) =
        (1 / (s + 2) + 1 / (s + 1) - 1 / (s - 1)) -
          xiShiftTwoReflectionCocycle s := by
    rw [xiShiftTwoReflectionCocycle,
      show (-1 - s) + 2 = -(s - 1) by ring_nf,
      show (-1 - s) + 1 = -s by ring_nf,
      show (-1 - s) - 1 = -(s + 2) by ring_nf]
    simp only [one_div, inv_neg]
    ring_nf
  rw [xiShiftTwoPrimeDefect, xiShiftTwoPrimeDefect, hraw, hcorrection]
  ring_nf

/-- **Half-cocycle centered reflection law.**  The centered prime defect is exactly fixed by
reflection about `-1 / 2`. -/
theorem xiCenteredShiftTwoPrimeDefect_reflection (s : ℂ) :
    xiCenteredShiftTwoPrimeDefect (-1 - s) =
      xiCenteredShiftTwoPrimeDefect s := by
  change xiShiftTwoPrimeDefect (-1 - s) +
      (1 / 2 : ℂ) * xiShiftTwoReflectionCocycle (-1 - s) =
    xiShiftTwoPrimeDefect s + (1 / 2 : ℂ) * xiShiftTwoReflectionCocycle s
  exact (add_half_reflection_fixed_iff
    (r := fun z : ℂ ↦ -1 - z)
    (f := xiShiftTwoPrimeDefect)
    (c := xiShiftTwoReflectionCocycle)
    xiShiftTwoReflectionCocycle_reflection s).2
      (xiShiftTwoPrimeDefect_reflection_cocycle s)

/-- Upper-end germ of the actual half-cocycle centered prime defect in the rotated coordinate
`s = -I*z`. -/
noncomputable def xiCenteredShiftTwoPrimeDefectUpperEndGerm : Germ upperEndFilter ℂ :=
  ((fun z : ℂ ↦ xiCenteredShiftTwoPrimeDefect (-I * z)) : Germ upperEndFilter ℂ)

/-- The centered upper-end germ is the filtered von Mangoldt germ plus the rational half-cocycle. -/
theorem xiCenteredShiftTwoPrimeDefectUpperEndGerm_eq :
    xiCenteredShiftTwoPrimeDefectUpperEndGerm =
      filteredVonMangoldtUpperEndGerm +
        ((fun z : ℂ ↦ (1 / 2 : ℂ) *
          (1 / (-I * z) + 1 / (-I * z + 1))) : Germ upperEndFilter ℂ) := by
  rw [filteredVonMangoldtUpperEndGerm_eq_xiLogDerivShiftTwoPrimeDefect]
  change
    ((fun z : ℂ ↦ xiCenteredShiftTwoPrimeDefect (-I * z)) : Germ upperEndFilter ℂ) =
      ((fun z : ℂ ↦ xiShiftTwoPrimeDefect (-I * z)) : Germ upperEndFilter ℂ) +
        ((fun z : ℂ ↦ (1 / 2 : ℂ) *
          (1 / (-I * z) + 1 / (-I * z + 1))) : Germ upperEndFilter ℂ)
  rw [← Germ.coe_add]
  apply Germ.coe_eq.mpr
  filter_upwards [] with z
  rfl

/-- Actual upper-end analytic germ of the rational half reflection cocycle. -/
noncomputable def xiShiftTwoReflectionHalfCocycleUpperEndAnalytic :
    upperEndAnalyticSubring :=
  upperEndPolyToAnalytic (Polynomial.C (1 / 2)) *
    (xiShiftReciprocalUpperEndAnalytic 0 +
      xiShiftReciprocalUpperEndAnalytic 1)

@[simp]
theorem xiShiftTwoReflectionHalfCocycleUpperEndAnalytic_coe :
    ((xiShiftTwoReflectionHalfCocycleUpperEndAnalytic : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) =
      ((fun z : ℂ ↦ (1 / 2 : ℂ) *
        (1 / (-I * z) + 1 / (-I * z + 1))) : Germ upperEndFilter ℂ) := by
  apply Germ.coe_eq.mpr
  filter_upwards [] with z
  simp

/-- Actual upper-end analytic realization of the centered prime defect. -/
noncomputable def xiCenteredShiftTwoPrimeDefectUpperEndAnalytic :
    upperEndAnalyticSubring :=
  finiteAbscissaLSeriesToUpperEndAnalytic filteredVonMangoldtFiniteAbscissaSource +
    xiShiftTwoReflectionHalfCocycleUpperEndAnalytic

/-- The analytic realization has exactly the centered value germ. -/
theorem xiCenteredShiftTwoPrimeDefectUpperEndAnalytic_coe :
    ((xiCenteredShiftTwoPrimeDefectUpperEndAnalytic : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) =
      xiCenteredShiftTwoPrimeDefectUpperEndGerm := by
  rw [xiCenteredShiftTwoPrimeDefectUpperEndGerm_eq]
  change filteredVonMangoldtUpperEndGerm +
      (xiShiftTwoReflectionHalfCocycleUpperEndAnalytic : Germ upperEndFilter ℂ) = _
  rw [xiShiftTwoReflectionHalfCocycleUpperEndAnalytic_coe]

/-- Actual meromorphic carrier of the half-cocycle centered prime defect. -/
noncomputable def xiCenteredShiftTwoPrimeDefectUpperEndCarrier : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField
    xiCenteredShiftTwoPrimeDefectUpperEndAnalytic

theorem xiCenteredShiftTwoPrimeDefectUpperEndCarrier_eq :
    xiCenteredShiftTwoPrimeDefectUpperEndCarrier =
      filteredVonMangoldtUpperEndCarrier +
        algebraMap upperEndAnalyticSubring upperEndMeroField
          xiShiftTwoReflectionHalfCocycleUpperEndAnalytic := by
  rw [xiCenteredShiftTwoPrimeDefectUpperEndCarrier,
    xiCenteredShiftTwoPrimeDefectUpperEndAnalytic, map_add]
  rfl

private theorem xiShiftTwoReflectionHalfCocycleUpperEndCarrier_differentialAlgebraic :
    DifferentialAlgebraicOver ℂ
      (algebraMap upperEndAnalyticSubring upperEndMeroField
        xiShiftTwoReflectionHalfCocycleUpperEndAnalytic) := by
  rw [xiShiftTwoReflectionHalfCocycleUpperEndAnalytic, map_mul, map_add]
  exact differentialAlgebraicOver_mul
    (differentialAlgebraicOver_algebraMap (1 / 2 : ℂ))
    (differentialAlgebraicOver_add
      (xiShiftReciprocalUpperEndCarrier_differentialAlgebraic 0)
      (xiShiftReciprocalUpperEndCarrier_differentialAlgebraic 1))

/-- **Centered prime-source hypertranscendence.**  Exact reflection centering changes the
filtered von Mangoldt carrier only by a rational base element, so the centered upper-end carrier
remains hypertranscendental over the genuine rational coordinate field. -/
theorem xiCenteredShiftTwoPrimeDefectUpperEndCarrier_hypertranscendentalOver :
    HypertranscendentalOver upperEndRationalCoordinateField
      xiCenteredShiftTwoPrimeDefectUpperEndCarrier := by
  rw [xiCenteredShiftTwoPrimeDefectUpperEndCarrier_eq]
  have hbase : DifferentialAlgebraicOver upperEndRationalCoordinateField
      (algebraMap upperEndAnalyticSubring upperEndMeroField
        xiShiftTwoReflectionHalfCocycleUpperEndAnalytic) :=
    differentialAlgebraicOver_mono
      xiShiftTwoReflectionHalfCocycleUpperEndCarrier_differentialAlgebraic
  exact (hypertranscendentalOver_add_differentialAlgebraic_iff hbase).2
    filteredVonMangoldtUpperEndCarrier_hypertranscendentalOver

end

end RHTower
