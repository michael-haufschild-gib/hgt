import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionMatroid
import GaloisForLFunctions.HTGeometry.HassePredicate

/-!
# Finitary Hasse principle for differential independence

An arbitrarily indexed differential family is independent exactly when every finite restriction is
independent.  Contrapositively, every global differential relation is witnessed on a finite index
packet.  This is the local--global compactness interface for infinite source dictionaries.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

/-- Differential independence is equivalent to independence at every finite index place. -/
theorem differentialIndependent_iff_forall_finite_subfamily
    {F E : Type u} {ι : Type v}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) :
    DifferentialIndependent F x ↔
      ∀ I : Set ι, I.Finite → DifferentialIndependent F (fun i : I => x i) := by
  constructor
  · intro hx I _hI
    change DifferentialIndependent F (x ∘ fun i : I => i.1)
    exact hx.comp (fun i : I => i.1) Subtype.val_injective
  · exact differentialIndependent_of_forall_finite_subfamily x

/-- Failure of global differential independence is detected on one finite index packet. -/
theorem not_differentialIndependent_iff_exists_finite_subfamily
    {F E : Type u} {ι : Type v}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : ι → E) :
    ¬ DifferentialIndependent F x ↔
      ∃ I : Set ι, I.Finite ∧ ¬ DifferentialIndependent F (fun i : I => x i) := by
  constructor
  · intro hx
    by_contra hfinite
    push Not at hfinite
    exact hx (differentialIndependent_of_forall_finite_subfamily x hfinite)
  · rintro ⟨I, _hI, hI⟩ hx
    apply hI
    change DifferentialIndependent F (x ∘ fun i : I => i.1)
    exact hx.comp (fun i : I => i.1) Subtype.val_injective

/-- A finite index set viewed as a local place for an arbitrarily indexed family. -/
abbrev FiniteSubfamilyPlace (ι : Type*) := {I : Set ι // I.Finite}

/-- Differential independence is a predicate-level Hasse principle over finite subfamilies. -/
def differentialIndependenceHassePredicate
    {F E : Type u} {ι : Type v}
    [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E] :
    HassePredicate (ι → E) (FiniteSubfamilyPlace ι) where
  global x := DifferentialIndependent F x
  atPlace I x := DifferentialIndependent F (fun i : I.1 => x i)
  local_global x := by
    constructor
    · intro hx I
      exact (differentialIndependent_iff_forall_finite_subfamily x).mp hx I.1 I.2
    · intro hx
      apply (differentialIndependent_iff_forall_finite_subfamily x).mpr
      intro I hI
      exact hx ⟨I, hI⟩

end


end GaloisForLFunctions.HTGeometry
