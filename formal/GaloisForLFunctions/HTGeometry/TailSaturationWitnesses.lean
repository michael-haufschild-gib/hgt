import GaloisForLFunctions.HTGeometry.TailQuotientSeparationLaw
import GaloisForLFunctions.HTGeometry.RelativeCharacterDerivation

/-!
# The saturation classes are inhabited

The separation laws of the tail quotient run on setoids insensitive to finite modification or to
eventual equality, and the relative-character laws on carriers whose two endpoint actions agree.
Nothing exhibited any of them.

All three are realized, and by more than the trivial identifications: finite symmetric difference is
itself a setoid saturated by construction, and so is eventual equality.  The two are linked — on a
sequence index, eventual equality has finite difference set — so finite-modification saturation is
the stronger notion.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

/-! ## Finite modification -/

/-- Records differing in finitely many coordinates. -/
def finiteModificationSetoid (I A : Type*) : Setoid (I → A) where
  r u v := {i | u i ≠ v i}.Finite
  iseqv := by
    refine ⟨fun u => ?_, fun {u v} h => ?_, fun {u v w} huv hvw => ?_⟩
    · have hempty : {i : I | u i ≠ u i} = (∅ : Set I) := by
        ext i
        simp
      rw [hempty]
      exact Set.finite_empty
    · have hsym : {i : I | v i ≠ u i} = {i : I | u i ≠ v i} := by
        ext i
        exact ne_comm
      rw [hsym]
      exact h
    · refine (huv.union hvw).subset fun i hi => ?_
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      exact hi (by rw [hcon.1, hcon.2])

/-- **Finite symmetric difference is saturated by construction.** -/
theorem finiteModificationSaturated_finiteModificationSetoid (I A : Type*) :
    FiniteModificationSaturated (finiteModificationSetoid I A) := fun _ _ h => h

/-- The all-identifying setoid is saturated. -/
theorem finiteModificationSaturated_top (I A : Type*) :
    FiniteModificationSaturated (⊤ : Setoid (I → A)) := fun _ _ _ => trivial

/-! ## Eventual equality -/

/-- Sequences agreeing from some index on. -/
def tailSetoid (A : Type*) : Setoid (ℕ → A) where
  r u v := u =ᶠ[atTop] v
  iseqv := ⟨fun u => Filter.EventuallyEq.refl _ u, Filter.EventuallyEq.symm,
    Filter.EventuallyEq.trans⟩

/-- **Eventual equality is tail-saturated by construction.** -/
theorem tailSaturated_tailSetoid (A : Type*) : TailSaturated (tailSetoid A) := fun _ _ h => h

/-- The all-identifying setoid is tail-saturated. -/
theorem tailSaturated_top (A : Type*) : TailSaturated (⊤ : Setoid (ℕ → A)) := fun _ _ _ => trivial

/-- **Finite-modification saturation is the stronger notion.**  On a sequence index, eventual
equality has a finite difference set. -/
theorem tailSaturated_of_finiteModificationSaturated {A : Type*} {r : Setoid (ℕ → A)}
    (h : FiniteModificationSaturated r) : TailSaturated r := by
  intro u v huv
  refine h ?_
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp huv
  refine Set.Finite.subset (Set.finite_Iio N) fun n hn => ?_
  by_contra hcon
  simp only [Set.mem_Iio, not_lt] at hcon
  exact hn (hN n hcon)

/-! ## Relative character carriers -/

/-- The zero carrier has equal endpoint actions. -/
theorem isRelativeCharacterCarrier_zero {K A V : Type*} [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup V] [Module K V] (α β : A →ₐ[K] K) :
    IsRelativeCharacterCarrier α β (0 : V) := by
  intro a
  simp

/-- Every carrier has equal endpoint actions when the endpoints agree. -/
theorem isRelativeCharacterCarrier_of_eq {K A V : Type*} [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup V] [Module K V] {α β : A →ₐ[K] K} (hαβ : α = β) (x : V) :
    IsRelativeCharacterCarrier α β x := by
  intro a
  rw [hαβ]

end GaloisForLFunctions.HTGeometry
