import GaloisForLFunctions.HTGeometry.TailHadamardReducedProduct
import GaloisForLFunctions.HTGeometry.TailQuotientSeparationLaw

/-!
# Finite-observation separation in the Hadamard tail algebra

Every finite coordinate prescription occurs in every class of the real
Hadamard reduced product modulo finite support.  Consequently, no
nonconstant reporter on that reduced product is determined by finitely many
coefficient coordinates.
-/

namespace HTGeometry

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Every finite coordinate cylinder maps onto the entire Hadamard reduced
product. -/
theorem finiteCoordinateCylinder_surjective_tailHadamardReducedProduct
    {I : Type*} [DecidableEq I]
    (s : Finset I) (observed : I → ℝ)
    (q : TailHadamardReducedProduct I) :
    ∃ record : I → ℝ,
      FiniteCoordinatesAgree s record observed ∧ tailHadamardClass record = q := by
  obtain ⟨tail, rfl⟩ :=
    Submodule.Quotient.mk_surjective (finiteSupportIdeal I) q
  refine ⟨finiteCoordinateSplice s observed tail,
    finiteCoordinateSplice_agrees s observed tail, ?_⟩
  apply (tailHadamardClass_eq_iff _ _).mpr
  exact finite_setOf_finiteCoordinateSplice_ne_tail s observed tail

/-- A Hadamard-tail reporter is determined by the coefficient coordinates in
`s` when representatives agreeing there always receive the same value. -/
def TailHadamardReporterDeterminedBy
    {I Y : Type*} (s : Finset I)
    (F : TailHadamardReducedProduct I → Y) : Prop :=
  ∀ a b : I → ℝ,
    FiniteCoordinatesAgree s a b →
      F (tailHadamardClass a) = F (tailHadamardClass b)

/-- **Hadamard-tail finite-observation separation.** Every reporter on the
coefficient-tail algebra that is determined by finitely many coefficients is
constant. -/
theorem finiteCoordinate_tailHadamardReporter_constant
    {I Y : Type*} [DecidableEq I]
    (s : Finset I) (F : TailHadamardReducedProduct I → Y)
    (hF : TailHadamardReporterDeterminedBy s F) :
    ReporterConstant F := by
  intro q₁ q₂
  obtain ⟨a, ha⟩ :=
    Submodule.Quotient.mk_surjective (finiteSupportIdeal I) q₁
  obtain ⟨w, hcoordinates, hw⟩ :=
    finiteCoordinateCylinder_surjective_tailHadamardReducedProduct s a q₂
  rw [← ha, ← hw]
  exact hF a w fun i hi => (hcoordinates i hi).symm

end

end HTGeometry
