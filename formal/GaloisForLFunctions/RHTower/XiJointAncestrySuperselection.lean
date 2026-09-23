import GaloisForLFunctions.RHTower.XiInternalTransverseCompletionSyndrome
import GaloisForLFunctions.RHTower.XiCompletionDefectSyndrome
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw
import GaloisForLFunctions.HTGeometry.PrimePoissonSourceLinearSuperselection

/-!
# Joint-ancestry superselection for Xi divisors

Internal divisor structure and transverse placement are different formal objects.  Every Xi
divisor has a nonzero square-zero EWQ channel, while only an off-line divisor has the transverse
completion syndrome.  Independently, the reflected prime-Poisson multiplication representations
admit a nonzero closed source-linear correspondence exactly at neutral horizontal grade.

This module joins those results without imposing a new source law.  A divisor is internal-only
exactly when its reflected prime-source sectors admit nonzero closed sewing.  A hypothetical
right-half Xi divisor therefore retains its internal nilpotent channel while simultaneously
carrying:

* the full completion/TailRoos/Noether/shared-gauge syndrome;
* the all-orders modular/Rees type fracture;
* disjoint reflected prime-source representations;
* failure of every nonzero closed source-linear sewing.

This is a classifier, not an RH proof.  Missing arithmetic theorem remains construction of one
divisor-independent physical reflection correspondence from the completed source.  Existing
synchronized-lcm recovery supplies all finite-support compound grades but is first-jet transparent;
it does not provide that reflection correspondence.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Existence of one nonzero closed source-linear correspondence between the forward and
reflected prime-Poisson multiplication representations attached to a Xi divisor point. -/
def XiPrimePoissonReflectionSewing (rho : XiDivisorSupport) : Prop :=
  let hstrip := xi_divisor_support_re_mem_open_unit rho
  NonzeroClosedSourceLinearSewing
    (continuousL2Mul
      (primePoissonMeasure (rho : ℂ).re (rho : ℂ).im hstrip.1))
    (continuousL2Mul
      (primePoissonMeasure (1 - (rho : ℂ).re) (rho : ℂ).im
        (sub_pos.mpr hstrip.2)))

/-- Disjointness of the reflected prime-source multiplication representations attached to a Xi
divisor point. -/
def XiPrimePoissonReflectionDisjoint (rho : XiDivisorSupport) : Prop :=
  let hstrip := xi_divisor_support_re_mem_open_unit rho
  OperatorFamiliesDisjoint
    (continuousL2Mul
      (primePoissonMeasure (rho : ℂ).re (rho : ℂ).im hstrip.1))
    (continuousL2Mul
      (primePoissonMeasure (1 - (rho : ℂ).re) (rho : ℂ).im
        (sub_pos.mpr hstrip.2)))

/-- **Internal/prime-source bridge.**  A Xi divisor is internal-only exactly when its forward and
reflected prime-source sectors admit a nonzero closed source-linear sewing. -/
theorem xiPrimePoissonReflectionSewing_iff_internalOnly
    (rho : XiDivisorSupport) :
    XiPrimePoissonReflectionSewing rho ↔
      XiDivisorSyndromeIsInternalOnly rho := by
  let hstrip := xi_divisor_support_re_mem_open_unit rho
  rw [XiPrimePoissonReflectionSewing,
    primePoisson_reflection_nonzeroClosedSourceLinearSewing_iff
      (rho : ℂ).re (rho : ℂ).im hstrip.1 hstrip.2,
    xiDivisorSyndromeIsInternalOnly_iff_re_eq_half]

/-- Reflected prime-source sectors of an off-line Xi divisor are disjoint. -/
theorem xiPrimePoissonReflectionDisjoint_of_offLine
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    XiPrimePoissonReflectionDisjoint rho := by
  let hstrip := xi_divisor_support_re_mem_open_unit rho
  exact primePoisson_reflection_continuousL2Mul_disjoint_of_ne_half
    (rho : ℂ).re (rho : ℂ).im hstrip.1 hstrip.2 hoff

/-- Joint corpus certificate for one hypothetical right-half Xi divisor.  Internal divisor
nilpotence survives; transverse placement simultaneously produces completion, asymptotic-type,
and prime-source superselection defects. -/
structure XiRightJointAncestrySuperselectionCertificate
    (q : XiRightZeroCopy) : Prop where
  internalChannel :
    ∃ n : ℕ,
      GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension
          (q.1.1 : ℂ) n ≠ 0 ∧
      GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension
          (q.1.1 : ℂ) n *
        GaloisForLFunctions.RHTower.eulerWickCompletedJetExtension
          (q.1.1 : ℂ) n = 0
  transverseChannel :
    xiTransverseCompletionDefect q.1.1 ≠ 0 ∧
    xiTransverseCompletionDefect q.1.1 ^ (2 : ℕ) = 0 ∧
    routeRSummableHadamardShiftEquiv
        (xiTransverseCompletionDefect q.1.1) =
      xiTransverseCompletionDefect q.1.1
  completionSyndrome : XiCompletionDefectSyndrome q.1.1
  modularTypeSyndrome : XiRightSourceModularTypeSuperselectionCertificate q
  reflectedPrimeSectorsDisjoint : XiPrimePoissonReflectionDisjoint q.1.1
  noClosedSourceLinearSewing : ¬ XiPrimePoissonReflectionSewing q.1.1

/-- **Joint-ancestry superselection law.**  Every hypothetical right-half Xi divisor carries the
complete joint-ancestry failure while retaining its nonzero internal square-zero divisor channel. -/
theorem xiRightJointAncestrySuperselection_law
    (q : XiRightZeroCopy) :
    XiRightJointAncestrySuperselectionCertificate q := by
  have hcharge := xiRightSourceModularCharge_pos q
  have hoff : (q.1.1 : ℂ).re ≠ 1 / 2 := by
    intro hhalf
    rw [xiRightSourceModularCharge, hhalf] at hcharge
    norm_num at hcharge
  have hinternal :=
    xiDivisor_internal_nonzero_transverse_stationary_squareZero q.1.1
  have htransverse := xiDivisor_offLine_transverse_completion_defect q.1.1 hoff
  refine
    { internalChannel := hinternal.1
      transverseChannel := ⟨htransverse.1, htransverse.2.1, htransverse.2.2.1⟩
      completionSyndrome :=
        (xiCompletionDefectSyndrome_iff_re_ne_half q.1.1).2 hoff
      modularTypeSyndrome := xiRightSourceModularTypeSuperselection_law q
      reflectedPrimeSectorsDisjoint :=
        xiPrimePoissonReflectionDisjoint_of_offLine q.1.1 hoff
      noClosedSourceLinearSewing := ?_ }
  rw [xiPrimePoissonReflectionSewing_iff_internalOnly,
    xiDivisorSyndromeIsInternalOnly_iff_re_eq_half]
  exact hoff

end

end RHTower
