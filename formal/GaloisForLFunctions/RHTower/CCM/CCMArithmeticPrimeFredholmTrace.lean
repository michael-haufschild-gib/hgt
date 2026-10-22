import GaloisForLFunctions.RHTower.CCM.CCMArithmeticPrimeFredholmOrientation
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniZetaCycleCompletedXiNaturality

/-!
# Arithmetic-prime Fredholm orientation: downstream trace and Xi receiver

`CCMArithmeticPrimeFredholmOrientation` constructs the source object, its
duality, signed index, horizontal polarization, and compact-stable infinite
completion without importing zeta or Xi.  Only here do the established
Connes--Consani trace formula and completed-Xi receiver enter.

The source period `log p` becomes a zeta-circle length.  Its character grade
has centered spectral label equal to the already constructed horizontal
orientation.  Completed Xi vanishes at that label exactly when every
Deninger--Meyer source trace has zero Fourier coefficient there.  No zero is
selected or assumed.
-/

namespace RHTower

open scoped SchwartzMap

noncomputable section

namespace CCMArithmeticPrimeFredholmCycle

/-- Prime-orbit period viewed as a Connes--Consani zeta-circle length. -/
def zetaCircleLength (X : CCMArithmeticPrimeFredholmCycle) :
    CCMZetaCircleLength :=
  X.period

/-- Centered label supplied by the downstream completed-Xi receiver. -/
def completedXiLabel (X : CCMArithmeticPrimeFredholmCycle) : ℂ :=
  ccmZetaCircleCompletedXiSpectralLabel X.zetaCircleLength X.grade

/-- Receiver label is exactly the source-first horizontal orientation. -/
theorem completedXiLabel_eq_horizontalOrientation
    (X : CCMArithmeticPrimeFredholmCycle) :
    X.completedXiLabel = (X.horizontalOrientation : ℂ) := by
  rfl

/-- Receiver reflection is inherited from source duality, not from a chosen
Xi zero. -/
theorem completedXiLabel_dual (X : CCMArithmeticPrimeFredholmCycle) :
    X.dual.completedXiLabel = -X.completedXiLabel := by
  rw [completedXiLabel_eq_horizontalOrientation,
    completedXiLabel_eq_horizontalOrientation, horizontalOrientation_dual]
  norm_num

/-- Exact source trace formula at the prime-orbit period and Fredholm grade.
Zeta appears as the Fourier multiplier only after the Fredholm object has
already been constructed. -/
theorem primeFredholm_sourceTrace_formula
    (X : CCMArithmeticPrimeFredholmCycle) (f : DeningerMeyerCap) :
    fourierCoeff (ccmZetaCycleTrace X.zetaCircleLength f) X.grade =
      (1 / (X.zetaCircleLength : ℝ)) •
        (riemannZeta
            (ccmZetaCircleCriticalPoint X.zetaCircleLength X.grade) *
          mellin ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ))
            (ccmZetaCircleCriticalPoint X.zetaCircleLength X.grade)) :=
  fourierCoeff_ccmZetaCycleTrace_eq_zeta_mul_mellin
    X.zetaCircleLength f X.grade

/-- Completed Xi is only a downstream trace receiver: its vanishing at the
source orientation is equivalent to vanishing of every source trace Fourier
coefficient. -/
theorem completedXi_horizontalOrientation_eq_zero_iff_sourceTrace
    (X : CCMArithmeticPrimeFredholmCycle) :
    XiC (X.horizontalOrientation : ℂ) = 0 ↔
      ∀ f : DeningerMeyerCap,
        fourierCoeff (ccmZetaCycleTrace X.zetaCircleLength f) X.grade = 0 := by
  rw [← completedXiLabel_eq_horizontalOrientation,
    completedXiLabel, XiC_ccmZetaCircleSpectralLabel_eq_zero_iff,
    ← ccmZetaCycleCharacterSurvives_iff]
  rfl

/-- Closed source-first receiver package.  Both reflected labels and both
trace criteria are produced without importing a zero location into the
Fredholm construction. -/
theorem source_first_completedXi_trace_receiver
    (X : CCMArithmeticPrimeFredholmCycle) :
    X.completedXiLabel = (X.horizontalOrientation : ℂ) ∧
      X.dual.completedXiLabel = -X.completedXiLabel ∧
      (XiC (X.horizontalOrientation : ℂ) = 0 ↔
        ∀ f : DeningerMeyerCap,
          fourierCoeff (ccmZetaCycleTrace X.zetaCircleLength f) X.grade = 0) ∧
      (XiC (X.dual.horizontalOrientation : ℂ) = 0 ↔
        ∀ f : DeningerMeyerCap,
          fourierCoeff
            (ccmZetaCycleTrace X.dual.zetaCircleLength f) X.dual.grade = 0) :=
  ⟨completedXiLabel_eq_horizontalOrientation X, completedXiLabel_dual X,
    completedXi_horizontalOrientation_eq_zero_iff_sourceTrace X,
    completedXi_horizontalOrientation_eq_zero_iff_sourceTrace X.dual⟩

end CCMArithmeticPrimeFredholmCycle

end

end RHTower
