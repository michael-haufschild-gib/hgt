/-
Prime-clock saturation at an arbitrary index family.

The clock-saturation correspondence exists twice.  Its restricted form
(`differentialAlgebraic_fractionPrimeProfile_iff_clockPolynomialSaturated`) assumes a finite,
nonempty, decidable index type and clock independence of the old family, and it carries the
hypertranscendence reading.  Its arbitrary-index form
(`differentialAlgebraic_fractionPrimeProfile_iff_intrinsicClockSaturated`) drops all four premises
but was never negated, and it names the saturation predicate differently.

The two saturation predicates are the same predicate, so the hypertranscendence reading transfers
to the arbitrary-index form and the four premises come off:

* `hypertranscendental_fractionPrimeProfile_iff_not_intrinsicClockSaturated`;
* `differentialAlgebraic_fractionPrimeProfile_iff_not_relativeClockIndependent`;
* `hypertranscendental_fractionPrimeProfile_iff_relativeClockIndependent` — hypertranscendence over
  the generated prime-profile field is exactly relative clock independence.
-/
import GaloisForLFunctions.HTGeometry.PrimeClockCompletionCorrespondence

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- The intrinsic and polynomial clock-saturation predicates are the same predicate. -/
theorem primeProfileIntrinsicClockSaturatedOver_iff_clockPolynomialSaturatedOver
    {I : Type*} (c : I → ArithmeticFunction ℂ) (f : ArithmeticFunction ℂ) :
    PrimeProfileIntrinsicClockSaturatedOver c f ↔
      PrimeProfileClockPolynomialSaturatedOver c f := Iff.rfl

/-- **Hypertranscendence over a generated prime-profile field, at an arbitrary index family.**
The negation of the arbitrary-index saturation correspondence; no finiteness, nonemptiness,
decidability or clock independence of the old family is used. -/
theorem hypertranscendental_fractionPrimeProfile_iff_not_intrinsicClockSaturated
    {I : Type*} (c : I → ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    GaloisForLFunctions.HypertranscendentalOver
        (GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (c i))))
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) ↔
      ¬ PrimeProfileIntrinsicClockSaturatedOver c f := by
  rw [GaloisForLFunctions.HypertranscendentalOver,
    differentialAlgebraic_fractionPrimeProfile_iff_intrinsicClockSaturated
      c hcsupport f hfsupport]

/-- **Differential algebraicity is failure of relative clock independence**, at an arbitrary index
family. -/
theorem differentialAlgebraic_fractionPrimeProfile_iff_not_relativeClockIndependent
    {I : Type*} (c : I → ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    GaloisForLFunctions.DifferentialAlgebraicOver
        (GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (c i))))
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) ↔
      ¬ PrimeProfileRelativeClockIndependent c (fun _ : Unit => f) :=
  (differentialAlgebraic_fractionPrimeProfile_iff_intrinsicClockSaturated
      c hcsupport f hfsupport).trans
    (primeProfileClockPolynomialSaturatedOver_iff_not_relativeClockIndependent c f)

/-- **Hypertranscendence is relative clock independence**, at an arbitrary index family.  The
sharpest form of the correspondence: no hypothesis on the old family beyond its support. -/
theorem hypertranscendental_fractionPrimeProfile_iff_relativeClockIndependent
    {I : Type*} (c : I → ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    GaloisForLFunctions.HypertranscendentalOver
        (GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
          (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (c i))))
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) ↔
      PrimeProfileRelativeClockIndependent c (fun _ : Unit => f) := by
  classical
  rw [GaloisForLFunctions.HypertranscendentalOver,
    differentialAlgebraic_fractionPrimeProfile_iff_not_relativeClockIndependent
      c hcsupport f hfsupport, not_not]

end

end GaloisForLFunctions.HTGeometry
