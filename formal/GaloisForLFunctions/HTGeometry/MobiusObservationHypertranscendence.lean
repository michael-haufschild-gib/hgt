import GaloisForLFunctions.HTGeometry.ProjectiveJetHorizon
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence

/-!
# Nondegenerate Möbius observations preserve differential complexity

Exterior matching, boundary conditions, and detector calibration often dress one response `x` by
a fractional-linear law

`(a*x + b) / (c*x + d)`.

This file proves that every nondegenerate dressing preserves both differential algebraicity and
hypertranscendence.  The proof is not a formal cancellation assumption: at an HT source the
forward and inverse denominators are forced to be nonzero, the source is recovered by the inverse
Möbius transformation, and the existing fractional-linear recovery theorem transfers HT to the
observed response.

The result supplies the exact no-cancellation certificate needed when a near-horizon response is
matched to an exterior region by frequency-independent connection coefficients.  Any
frequency-dependent matching coefficients must still be classified in their own differential
base; this theorem does not declare unknown matching data elementary.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential E] [Algebra F E]

/-- Fractional-linear observation of a field element by coefficients in the base field. -/
def mobiusObservable (a b c d : F) (x : E) : E :=
  (algebraMap F E a * x + algebraMap F E b) /
    (algebraMap F E c * x + algebraMap F E d)

/-- At an HT source, nondegeneracy of the Möbius matrix forces the denominator of the inverse
observation to be nonzero as well. -/
theorem mobiusObservable_inverse_denominator_ne_zero
    (x : E) (hx : HypertranscendentalOver F x)
    (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    algebraMap F E (-c) * mobiusObservable a b c d x +
        algebraMap F E a ≠ 0 := by
  have hden :
      algebraMap F E c * x + algebraMap F E d ≠ 0 :=
    mobiusDenominator_ne_zero_of_hypertranscendentalOver
      x hx a b c d hdet
  have hden' :
      x * algebraMap F E c + algebraMap F E d ≠ 0 := by
    simpa [mul_comm] using hden
  have hdetE : algebraMap F E (a * d - b * c) ≠ 0 :=
    by simpa only [map_zero] using (algebraMap F E).injective.ne hdet
  have hid :
      algebraMap F E (-c) * mobiusObservable a b c d x +
          algebraMap F E a =
        algebraMap F E (a * d - b * c) /
          (algebraMap F E c * x + algebraMap F E d) := by
    unfold mobiusObservable
    apply (eq_div_iff hden).2
    field_simp [hden, hden']
    simp only [map_neg, map_sub, map_mul]
    ring
  rw [hid]
  exact div_ne_zero hdetE hden

/-- Exact inverse Möbius recovery at an HT source. -/
theorem mobiusObservable_recover_of_hypertranscendental
    (x : E) (hx : HypertranscendentalOver F x)
    (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    x = mobiusObservable d (-b) (-c) a
      (mobiusObservable a b c d x) := by
  have hden :
      algebraMap F E c * x + algebraMap F E d ≠ 0 :=
    mobiusDenominator_ne_zero_of_hypertranscendentalOver
      x hx a b c d hdet
  have hden' :
      x * algebraMap F E c + algebraMap F E d ≠ 0 := by
    simpa [mul_comm] using hden
  have hinvden :=
    mobiusObservable_inverse_denominator_ne_zero x hx a b c d hdet
  unfold mobiusObservable at hinvden ⊢
  apply (eq_div_iff hinvden).2
  field_simp [hden, hden']
  simp only [map_neg]
  ring

/-- A nondegenerate base-field Möbius observation of an HT source remains HT. -/
theorem hypertranscendentalOver_mobiusObservable
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] [CharZero E]
    (x : E) (hx : HypertranscendentalOver F x)
    (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    HypertranscendentalOver F (mobiusObservable a b c d x) := by
  apply hypertranscendentalOver_fractionalLinearObservable_of_recovery
    (a := d) (b := -b) (c := -c) (d := a) hx
  exact mobiusObservable_recover_of_hypertranscendental x hx a b c d hdet

/-- **Exact Möbius differential-complexity law.**  A nondegenerate fractional-linear observation
is DA exactly when its source is DA. -/
theorem differentialAlgebraicOver_mobiusObservable_iff
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] [CharZero E]
    (x : E) (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    DifferentialAlgebraicOver F (mobiusObservable a b c d x) ↔
      DifferentialAlgebraicOver F x := by
  constructor
  · intro hobs
    by_contra hx
    exact (hypertranscendentalOver_mobiusObservable x hx a b c d hdet) hobs
  · intro hx
    unfold mobiusObservable
    exact differentialAlgebraicOver_div
      (differentialAlgebraicOver_add
        (differentialAlgebraicOver_mul
          (differentialAlgebraicOver_algebraMap a) hx)
        (differentialAlgebraicOver_algebraMap b))
      (differentialAlgebraicOver_add
        (differentialAlgebraicOver_mul
          (differentialAlgebraicOver_algebraMap c) hx)
        (differentialAlgebraicOver_algebraMap d))

/-- A nondegenerate fractional-linear observation is HT exactly when its source is HT. -/
theorem hypertranscendentalOver_mobiusObservable_iff
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E] [CharZero E]
    (x : E) (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    HypertranscendentalOver F (mobiusObservable a b c d x) ↔
      HypertranscendentalOver F x := by
  rw [HypertranscendentalOver, HypertranscendentalOver,
    differentialAlgebraicOver_mobiusObservable_iff x a b c d hdet]

end

end GaloisForLFunctions.HTGeometry
