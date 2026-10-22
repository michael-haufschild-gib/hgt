import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittKoszulSource
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Local and all-prime Calderón--Witt Koszul quotients

The local Koszul boundary is surjective with precisely the Calderón-defect axis as kernel.
Its all-prime finite-support analogue has the direct sum of these axes as its kernel.  This module
records the resulting quotient realization statements.
-/

namespace RHTower

noncomputable section

/-- At one prime, Koszul source classes modulo their local defect axis are exactly degree-two
local data. -/
noncomputable def deningerCalderonWittKoszulQuotientEquiv
    (p : Nat.Primes) :
    (DeningerCalderonWittAlgebraicDegreeOne p ⧸
      LinearMap.range (deningerCalderonWittDefectAxisInclusion p)) ≃ₗ[ℂ]
        DeningerCalderonWittAlgebraicDegreeTwo p :=
  (Submodule.quotEquivOfEq _ _
    (LinearMap.exact_iff.mp (deningerCalderonWittDefectAxis_exact (p := p))).symm).trans
      (LinearMap.quotKerEquivOfSurjective
        (deningerCalderonWittKoszulBoundary p)
        (deningerCalderonWittKoszulBoundary_surjective p))

theorem deningerCalderonWittKoszulQuotientEquiv_mk
    (p : Nat.Primes) (x : DeningerCalderonWittAlgebraicDegreeOne p) :
    deningerCalderonWittKoszulQuotientEquiv p (Submodule.Quotient.mk x) =
      deningerCalderonWittKoszulBoundary p x := by
  simp [deningerCalderonWittKoszulQuotientEquiv]

/-- The additive form of all-prime defect inclusion. -/
def deningerCalderonWittGlobalDefectAxisInclusionAdd :
    DeningerCalderonWittGlobalDefectAxis →+
      DeningerCalderonWittAlgebraicGlobalDegreeOne :=
  deningerCalderonWittGlobalDefectAxisInclusion.toAddMonoidHom

/-- The additive form of the all-prime Koszul boundary. -/
def deningerCalderonWittGlobalKoszulBoundaryAdd :
    DeningerCalderonWittAlgebraicGlobalDegreeOne →+
      DeningerCalderonWittAlgebraicGlobalDegreeTwo :=
  deningerCalderonWittGlobalKoszulBoundary.toAddMonoidHom

/-- All-prime defect inclusion is exact at the all-prime Koszul boundary. -/
theorem deningerCalderonWittGlobalDefectAxis_exact_add :
    Function.Exact deningerCalderonWittGlobalDefectAxisInclusionAdd
      deningerCalderonWittGlobalKoszulBoundaryAdd :=
  deningerCalderonWittGlobalDefectAxis_exact

/-- Across all primes, finite-support source data modulo all local defect axes are exactly the
finite-support global degree-two profile. -/
noncomputable def deningerCalderonWittGlobalKoszulQuotientEquiv :
    (DeningerCalderonWittAlgebraicGlobalDegreeOne ⧸
      deningerCalderonWittGlobalDefectAxisInclusionAdd.range) ≃+
        DeningerCalderonWittAlgebraicGlobalDegreeTwo :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (AddMonoidHom.exact_iff.mp deningerCalderonWittGlobalDefectAxis_exact_add).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        deningerCalderonWittGlobalKoszulBoundaryAdd
        deningerCalderonWittGlobalKoszulBoundary_surjective)

theorem deningerCalderonWittGlobalKoszulQuotientEquiv_mk
    (x : DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    deningerCalderonWittGlobalKoszulQuotientEquiv (QuotientAddGroup.mk x) =
      deningerCalderonWittGlobalKoszulBoundary x := by
  simp only [deningerCalderonWittGlobalKoszulQuotientEquiv, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  change QuotientAddGroup.kerLift deningerCalderonWittGlobalKoszulBoundaryAdd
    (QuotientAddGroup.mk x) = _
  rfl

end

end RHTower
