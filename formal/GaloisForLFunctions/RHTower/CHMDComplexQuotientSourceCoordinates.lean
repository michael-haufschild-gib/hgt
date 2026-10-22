import GaloisForLFunctions.RHTower.CHMDQuotientWeilForm
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.RHTower.CHMDBoundStateInertia
import GaloisForLFunctions.RHTower.OddSectorEnergyCompletion
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual complex RW, EWU and OWU source energies in the complete quotient

Real and imaginary inverse-Doob lifts give coordinates in the doubled real Hilbert
quotient. The native RW source energy and both parity-profile energies pull back
exactly, with all polar corrections retained.
-/

set_option autoImplicit false

open Complex MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar WeilSpectral Zeta23


/-- The real Hilbert realization of the complexified signed-radical quotient. -/
abbrev ComplexSignedQuotient := PiLp 2 (fun _ : Fin 2 => SignedQuotient)

instance complexSignedQuotient_complete : CompleteSpace ComplexSignedQuotient := inferInstance

def complexQuotientWeilEnergy (x : ComplexSignedQuotient) : ℝ :=
  quotientWeilForm (x 0) + quotientWeilForm (x 1)

def complexCompactQuotient (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ComplexSignedQuotient :=
  WithLp.toLp 2 ![
    signedQuotientMk (testLift (rePart f) (contDiff_rePart hf) (hasCompactSupport_rePart hc)),
    signedQuotientMk (testLift (imPart f) (contDiff_imPart hf) (hasCompactSupport_imPart hc))]

theorem complexCompactQuotient_energy (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    complexQuotientWeilEnergy (complexCompactQuotient f hf hc) = (zetaZeroConfig.W f f).re := by
  change quotientWeilForm (signedQuotientMk (testLift (rePart f) _ _)) +
    quotientWeilForm (signedQuotientMk (testLift (imPart f) _ _)) = _
  rw [quotientWeilForm_testLift, quotientWeilForm_testLift]
  have hr := contDiff_rePart hf
  have hi := contDiff_imPart hf
  have hrc := hasCompactSupport_rePart hc
  have hic := hasCompactSupport_imPart hc
  have hrC : ContDiff ℝ 2 (fun x => (rePart f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hr
  have hiC : ContDiff ℝ 2 (fun x => (imPart f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hi
  have hrcC : HasCompactSupport (fun x => (rePart f x : ℂ)) :=
    hrc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hicC : HasCompactSupport (fun x => (imPart f x : ℂ)) :=
    hic.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  rw [zeta_W_eq_weilFullFunctional hf hc, zeta_W_eq_weilFullFunctional hrC hrcC,
    zeta_W_eq_weilFullFunctional hiC hicC]
  exact (re_weilFullFunctional_split _ ⟨f, hf, hc⟩).symm

def complexSmoothQuotient {a : SuzukiPositiveAperture} (f : CCMComplexSmoothInteriorSource a) :
    ComplexSignedQuotient := complexCompactQuotient f
      (f.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) f.hasCompactSupport

/-- The actual complex RW source energy factors through the doubled literal quotient. -/
theorem complexSmoothQuotient_energy {a : SuzukiPositiveAperture}
    (f : CCMComplexSmoothInteriorSource a) :
    complexQuotientWeilEnergy (complexSmoothQuotient f) =
      ccmRestrictedWeilSourceQuadratic a f.toCCMFormVector := by
  rw [complexSmoothQuotient, complexCompactQuotient_energy,
    ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil]

def evenInteriorQuotient {a : SuzukiPositiveAperture}
    (f : EvenSector.InteriorWindowedSmoothEvenPolarTestFn a) : ComplexSignedQuotient :=
  complexSmoothQuotient (EvenSector.interiorCCMSource f)

def oddInteriorQuotient {a : SuzukiPositiveAperture}
    (f : OddSector.InteriorWindowedSmoothOddTestFn a) : ComplexSignedQuotient :=
  complexSmoothQuotient (OddSector.interiorCCMSource f)

/-- The actual EWU profile energy on each native interior test, without discarding pole terms. -/
theorem evenInteriorQuotient_energy {a : SuzukiPositiveAperture}
    (f : EvenSector.InteriorWindowedSmoothEvenPolarTestFn a) :
    complexQuotientWeilEnergy (evenInteriorQuotient f) =
      EvenSector.nativeProfileEnergy (Zeta23.EF.weilTest f.1.1.1.1 f.1.1.1.1) := by
  rw [evenInteriorQuotient, complexSmoothQuotient_energy]
  exact EvenSector.sourceEnergy_interiorCCMSource f

/-- The actual OWU profile energy on each native interior test, including its odd pole correction. -/
theorem oddInteriorQuotient_energy {a : SuzukiPositiveAperture}
    (f : OddSector.InteriorWindowedSmoothOddTestFn a) :
    complexQuotientWeilEnergy (oddInteriorQuotient f) =
      EvenSector.nativeProfileEnergy (Zeta23.EF.weilTest f.1.1.1.1 f.1.1.1.1) := by
  rw [oddInteriorQuotient, complexSmoothQuotient_energy]
  exact OddSector.sourceEnergy_interiorCCMSource f

end RHTower.CHMDDoobGraph

end
