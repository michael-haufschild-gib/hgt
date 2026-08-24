import GaloisForLFunctions.HTGeometry.HassePredicate

/-!
# Finitary Hasse principle for algebraic independence

An arbitrary algebraic family is independent exactly when every finite restriction is independent.
Equivalently, every algebraic dependence has one finite index witness.  The result supplies the
ordinary-algebraic precursor of the differential-independence Hasse principle.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Algebraic independence is equivalent to independence of every finite subfamily. -/
theorem algebraicIndependent_iff_forall_finite_subfamily
    {R A : Type u} {ι : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (x : ι → A) :
    AlgebraicIndependent R x ↔
      ∀ I : Set ι, I.Finite → AlgebraicIndependent R (fun i : I => x i) := by
  constructor
  · intro hx I _hI
    change AlgebraicIndependent R (x ∘ fun i : I => i.1)
    exact hx.comp (fun i : I => i.1) Subtype.val_injective
  · exact algebraicIndependent_of_finite_type

/-- Failure of global algebraic independence is detected on one finite index packet. -/
theorem not_algebraicIndependent_iff_exists_finite_subfamily
    {R A : Type u} {ι : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (x : ι → A) :
    ¬ AlgebraicIndependent R x ↔
      ∃ I : Set ι, I.Finite ∧ ¬ AlgebraicIndependent R (fun i : I => x i) := by
  constructor
  · intro hx
    by_contra hfinite
    push Not at hfinite
    exact hx (algebraicIndependent_of_finite_type hfinite)
  · rintro ⟨I, _hI, hI⟩ hx
    apply hI
    change AlgebraicIndependent R (x ∘ fun i : I => i.1)
    exact hx.comp (fun i : I => i.1) Subtype.val_injective

/-- Algebraic independence is a predicate-level Hasse principle over finite subfamilies. -/
def algebraicIndependenceHassePredicate
    {R A : Type u} {ι : Type v}
    [CommRing R] [CommRing A] [Algebra R A] :
    HassePredicate (ι → A) {I : Set ι // I.Finite} where
  global x := AlgebraicIndependent R x
  atPlace I x := AlgebraicIndependent R (fun i : I.1 => x i)
  local_global x := by
    constructor
    · intro hx I
      exact (algebraicIndependent_iff_forall_finite_subfamily x).mp hx I.1 I.2
    · intro hx
      apply (algebraicIndependent_iff_forall_finite_subfamily x).mpr
      intro I hI
      exact hx ⟨I, hI⟩

end GaloisForLFunctions.HTGeometry
