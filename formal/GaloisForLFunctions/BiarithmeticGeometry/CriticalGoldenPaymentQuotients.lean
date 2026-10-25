import GaloisForLFunctions.BiarithmeticGeometry.GoldenPrimePayment
import GaloisForLFunctions.ArithmeticDefectRigidity.TheClosedCofactorAnnihilatorHasNoCountableIndex

/-!
# The actual critical payment quotient and its closure defect

The paid ideal, its closure, and the quotient of the latter by the former
are distinct algebraic objects. Restriction of scalars gives their complex
vector spaces without a closedness assumption. Actual coefficient cardinality
bounds the Hamel rank of both quotients by continuum.
-/

noncomputable section
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The actual critical golden paid ideal as a complex vector subspace. -/
def criticalGoldenPaidSubmodule : Submodule ℂ (WienerAlgebraAt (1 / 2)) :=
  (paidIdeal (goldenArithmeticSource goldenCriticalParameter)
    (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
      goldenCriticalParameter_bounds.2.le)).restrictScalars ℂ

/-- Wiener closure of the actual critical golden paid subspace. -/
def criticalGoldenPaidClosure : Submodule ℂ (WienerAlgebraAt (1 / 2)) :=
  criticalGoldenPaidSubmodule.topologicalClosure

/-- The original paid subspace viewed inside its Wiener closure. -/
def criticalGoldenClosurePaid : Submodule ℂ criticalGoldenPaidClosure :=
  criticalGoldenPaidSubmodule.comap criticalGoldenPaidClosure.subtype

/-- The unreduced actual payment quotient. -/
abbrev CriticalGoldenPaymentQuotient := WienerAlgebraAt (1 / 2) ⧸ criticalGoldenPaidSubmodule

/-- The algebraic defect between payment and its Wiener closure. -/
abbrev CriticalGoldenPaymentClosureDefect := criticalGoldenPaidClosure ⧸ criticalGoldenClosurePaid

/-- The closure-defect classes map canonically to the unreduced actual payment quotient. -/
def criticalGoldenDefectToQuotient :
    CriticalGoldenPaymentClosureDefect →ₗ[ℂ] CriticalGoldenPaymentQuotient :=
  criticalGoldenClosurePaid.liftQ
    (criticalGoldenPaidSubmodule.mkQ.comp criticalGoldenPaidClosure.subtype) (by
      intro x hx
      change criticalGoldenPaidSubmodule.mkQ (x : WienerAlgebraAt (1 / 2)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx)

theorem criticalGoldenDefectToQuotient_mk (x : criticalGoldenPaidClosure) :
    criticalGoldenDefectToQuotient (criticalGoldenClosurePaid.mkQ x) =
      criticalGoldenPaidSubmodule.mkQ (x : WienerAlgebraAt (1 / 2)) := rfl

/-- The unreduced quotient cannot have Hamel rank above continuum. -/
theorem rank_criticalGoldenPaymentQuotient_le_continuum :
    Module.rank ℂ CriticalGoldenPaymentQuotient ≤ Cardinal.continuum := by
  exact (rank_le_card ℂ CriticalGoldenPaymentQuotient).trans
    ((Cardinal.mk_le_of_surjective criticalGoldenPaidSubmodule.mkQ_surjective).trans
      (WienerAlgebraAt.cardinal_le_continuum (1 / 2)))

/-- The closure defect has the same ambient cardinality upper bound, without Hausdorffness. -/
theorem rank_criticalGoldenPaymentClosureDefect_le_continuum :
    Module.rank ℂ CriticalGoldenPaymentClosureDefect ≤ Cardinal.continuum := by
  have hclosure : Cardinal.mk criticalGoldenPaidClosure ≤ Cardinal.continuum :=
    (Cardinal.mk_le_of_injective
      (Subtype.val_injective : Function.Injective
        (fun x : criticalGoldenPaidClosure => (x : WienerAlgebraAt (1 / 2))))).trans
      (WienerAlgebraAt.cardinal_le_continuum (1 / 2))
  exact (rank_le_card ℂ CriticalGoldenPaymentClosureDefect).trans
    ((Cardinal.mk_le_of_surjective criticalGoldenClosurePaid.mkQ_surjective).trans hclosure)

end GaloisForLFunctions.BiarithmeticGeometry
