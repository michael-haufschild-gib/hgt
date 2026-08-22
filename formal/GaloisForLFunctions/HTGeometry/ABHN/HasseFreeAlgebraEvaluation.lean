import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraUnits
import Mathlib.Algebra.FreeAlgebra

/-!
# Hasse detection for noncommutative polynomial identities

A fixed noncommutative polynomial expression in elements of a central simple algebra is equal to a
specified global element exactly when the scalar-extended expression is equal to that element at
every completion.  This includes word identities and commutator relations, but it does not assert
that independently chosen local tuples arise from a global tuple.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- A noncommutative polynomial identity in a central simple algebra over a number field holds
exactly when its scalar extension holds at every completed place. -/
theorem numberFieldFreeAlgebra_lift_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (X : Type w) (x : X → A.carrier)
    (P : FreeAlgebra K X) (c : A.carrier) :
    FreeAlgebra.lift K x P = c ↔ ∀ p : NumberFieldPlace K,
      FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P =
        numberFieldLocalScalarExtensionMap K p A c := by
  have hcomm (p : NumberFieldPlace K) :
      (numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x) =
        FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.coe_comp, FreeAlgebra.lift_ι_apply]
  constructor
  · intro h p
    calc
      FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P =
          ((numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x)) P :=
        congrArg (fun f => f P) (hcomm p).symm
      _ = numberFieldLocalScalarExtensionMap K p A c :=
        congrArg (numberFieldLocalScalarExtensionMap K p A) h
  · intro h
    apply numberFieldLocalScalarExtensionMap_injective K (witnessPlace K) A
    calc
      numberFieldLocalScalarExtensionMap K (witnessPlace K) A (FreeAlgebra.lift K x P) =
          ((numberFieldLocalScalarExtensionMap K (witnessPlace K) A).comp
            (FreeAlgebra.lift K x)) P := rfl
      _ = FreeAlgebra.lift K
          (fun i => numberFieldLocalScalarExtensionMap K (witnessPlace K) A (x i)) P :=
        congrArg (fun f => f P) (hcomm (witnessPlace K))
      _ = numberFieldLocalScalarExtensionMap K (witnessPlace K) A c := h (witnessPlace K)

/-- A noncommutative polynomial identity in a central simple algebra over `F(t)` holds exactly
when its scalar extension holds at every finite and infinite completion. -/
theorem rationalFunctionFreeAlgebra_lift_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (X : Type w) (x : X → A.carrier)
    (P : FreeAlgebra (RatFunc F) X) (c : A.carrier) :
    FreeAlgebra.lift (RatFunc F) x P = c ↔ ∀ p : RationalFunctionPlace F,
      FreeAlgebra.lift (RatFunc F)
        (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P =
        rationalFunctionLocalScalarExtensionMap F p A c := by
  have hcomm (p : RationalFunctionPlace F) :
      (rationalFunctionLocalScalarExtensionMap F p A).comp (FreeAlgebra.lift (RatFunc F) x) =
        FreeAlgebra.lift (RatFunc F)
          (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.coe_comp, FreeAlgebra.lift_ι_apply]
  constructor
  · intro h p
    calc
      FreeAlgebra.lift (RatFunc F)
          (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P =
          ((rationalFunctionLocalScalarExtensionMap F p A).comp
            (FreeAlgebra.lift (RatFunc F) x)) P :=
        congrArg (fun f => f P) (hcomm p).symm
      _ = rationalFunctionLocalScalarExtensionMap F p A c :=
        congrArg (rationalFunctionLocalScalarExtensionMap F p A) h
  · intro h
    apply rationalFunctionLocalScalarExtensionMap_injective F .infinite A
    calc
      rationalFunctionLocalScalarExtensionMap F .infinite A
          (FreeAlgebra.lift (RatFunc F) x P) =
          ((rationalFunctionLocalScalarExtensionMap F .infinite A).comp
            (FreeAlgebra.lift (RatFunc F) x)) P := rfl
      _ = FreeAlgebra.lift (RatFunc F)
          (fun i => rationalFunctionLocalScalarExtensionMap F .infinite A (x i)) P :=
        congrArg (fun f => f P) (hcomm .infinite)
      _ = rationalFunctionLocalScalarExtensionMap F .infinite A c := h .infinite

/-- A noncommutative polynomial value in a central simple algebra over a number field is a unit
exactly when its scalar-extended value is a unit at every completed place. -/
theorem numberFieldFreeAlgebra_lift_isUnit_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (X : Type w) (x : X → A.carrier) (P : FreeAlgebra K X) :
    IsUnit (FreeAlgebra.lift K x P) ↔ ∀ p : NumberFieldPlace K,
      IsUnit (FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P) := by
  have hcomm (p : NumberFieldPlace K) :
      (numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x) =
        FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.coe_comp, FreeAlgebra.lift_ι_apply]
  constructor
  · intro h p
    have hp :=
      (numberFieldLocalScalarExtensionMap_isUnit_iff_forall_place K A
        (FreeAlgebra.lift K x P)).mp h p
    have heq : numberFieldLocalScalarExtensionMap K p A (FreeAlgebra.lift K x P) =
        FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P := by
      change ((numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x)) P = _
      exact congrArg (fun f => f P) (hcomm p)
    rwa [heq] at hp
  · intro h
    apply (numberFieldLocalScalarExtensionMap_isUnit_iff_forall_place K A
      (FreeAlgebra.lift K x P)).mpr
    intro p
    have heq : numberFieldLocalScalarExtensionMap K p A (FreeAlgebra.lift K x P) =
        FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P := by
      change ((numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x)) P = _
      exact congrArg (fun f => f P) (hcomm p)
    rw [heq]
    exact h p

/-- A noncommutative polynomial value in a central simple algebra over `F(t)` is a unit exactly
when its scalar-extended value is a unit at every finite and infinite completion. -/
theorem rationalFunctionFreeAlgebra_lift_isUnit_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (X : Type w) (x : X → A.carrier)
    (P : FreeAlgebra (RatFunc F) X) :
    IsUnit (FreeAlgebra.lift (RatFunc F) x P) ↔ ∀ p : RationalFunctionPlace F,
      IsUnit (FreeAlgebra.lift (RatFunc F)
        (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P) := by
  have hcomm (p : RationalFunctionPlace F) :
      (rationalFunctionLocalScalarExtensionMap F p A).comp (FreeAlgebra.lift (RatFunc F) x) =
        FreeAlgebra.lift (RatFunc F)
          (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.coe_comp, FreeAlgebra.lift_ι_apply]
  constructor
  · intro h p
    have hp :=
      (rationalFunctionLocalScalarExtensionMap_isUnit_iff_forall_place F A
        (FreeAlgebra.lift (RatFunc F) x P)).mp h p
    have heq : rationalFunctionLocalScalarExtensionMap F p A
        (FreeAlgebra.lift (RatFunc F) x P) =
        FreeAlgebra.lift (RatFunc F)
          (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P := by
      change ((rationalFunctionLocalScalarExtensionMap F p A).comp
        (FreeAlgebra.lift (RatFunc F) x)) P = _
      exact congrArg (fun f => f P) (hcomm p)
    rwa [heq] at hp
  · intro h
    apply (rationalFunctionLocalScalarExtensionMap_isUnit_iff_forall_place F A
      (FreeAlgebra.lift (RatFunc F) x P)).mpr
    intro p
    have heq : rationalFunctionLocalScalarExtensionMap F p A
        (FreeAlgebra.lift (RatFunc F) x P) =
        FreeAlgebra.lift (RatFunc F)
          (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P := by
      change ((rationalFunctionLocalScalarExtensionMap F p A).comp
        (FreeAlgebra.lift (RatFunc F) x)) P = _
      exact congrArg (fun f => f P) (hcomm p)
    rw [heq]
    exact h p

/-- A fixed noncommutative polynomial identity in a number-field CSA can be certified at one
completion. -/
theorem numberFieldFreeAlgebra_lift_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (X : Type w) (x : X → A.carrier)
    (P : FreeAlgebra K X) (c : A.carrier) :
    FreeAlgebra.lift K x P = c ↔ ∃ p : NumberFieldPlace K,
      FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P =
        numberFieldLocalScalarExtensionMap K p A c := by
  have hcomm (p : NumberFieldPlace K) :
      (numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x) =
        FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.coe_comp, FreeAlgebra.lift_ι_apply]
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldFreeAlgebra_lift_eq_iff_forall_place K A X x P c).mp h (witnessPlace K)⟩
  · rintro ⟨p, hp⟩
    apply numberFieldLocalScalarExtensionMap_injective K p A
    calc
      numberFieldLocalScalarExtensionMap K p A (FreeAlgebra.lift K x P) =
          ((numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x)) P := rfl
      _ = FreeAlgebra.lift K
          (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P :=
        congrArg (fun f => f P) (hcomm p)
      _ = numberFieldLocalScalarExtensionMap K p A c := hp

/-- A fixed noncommutative polynomial identity in an `F(t)`-CSA can be certified at one
completion. -/
theorem rationalFunctionFreeAlgebra_lift_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (X : Type w) (x : X → A.carrier)
    (P : FreeAlgebra (RatFunc F) X) (c : A.carrier) :
    FreeAlgebra.lift (RatFunc F) x P = c ↔ ∃ p : RationalFunctionPlace F,
      FreeAlgebra.lift (RatFunc F)
        (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P =
          rationalFunctionLocalScalarExtensionMap F p A c := by
  have hcomm (p : RationalFunctionPlace F) :
      (rationalFunctionLocalScalarExtensionMap F p A).comp (FreeAlgebra.lift (RatFunc F) x) =
        FreeAlgebra.lift (RatFunc F)
          (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.coe_comp, FreeAlgebra.lift_ι_apply]
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionFreeAlgebra_lift_eq_iff_forall_place F A X x P c).mp h .infinite⟩
  · rintro ⟨p, hp⟩
    apply rationalFunctionLocalScalarExtensionMap_injective F p A
    calc
      rationalFunctionLocalScalarExtensionMap F p A (FreeAlgebra.lift (RatFunc F) x P) =
          ((rationalFunctionLocalScalarExtensionMap F p A).comp
            (FreeAlgebra.lift (RatFunc F) x)) P := rfl
      _ = FreeAlgebra.lift (RatFunc F)
          (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P :=
        congrArg (fun f => f P) (hcomm p)
      _ = rationalFunctionLocalScalarExtensionMap F p A c := hp

/-- A fixed noncommutative polynomial value in a number-field CSA is a unit exactly when it is
a unit at one completion. -/
theorem numberFieldFreeAlgebra_lift_isUnit_iff_exists_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (X : Type w) (x : X → A.carrier) (P : FreeAlgebra K X) :
    IsUnit (FreeAlgebra.lift K x P) ↔ ∃ p : NumberFieldPlace K,
      IsUnit (FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P) := by
  have hcomm (p : NumberFieldPlace K) :
      (numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x) =
        FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.coe_comp, FreeAlgebra.lift_ι_apply]
  constructor
  · intro h
    rcases (numberFieldLocalScalarExtensionMap_isUnit_iff_exists_place K A
      (FreeAlgebra.lift K x P)).mp h with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    change IsUnit (((numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x)) P)
      at hp
    rwa [hcomm p] at hp
  · rintro ⟨p, hp⟩
    apply (numberFieldLocalScalarExtensionMap_isUnit_iff_exists_place K A
      (FreeAlgebra.lift K x P)).mpr
    refine ⟨p, ?_⟩
    change IsUnit (((numberFieldLocalScalarExtensionMap K p A).comp (FreeAlgebra.lift K x)) P)
    rwa [hcomm p]

/-- A fixed noncommutative polynomial value in an `F(t)`-CSA is a unit exactly when it is a unit
at one completion. -/
theorem rationalFunctionFreeAlgebra_lift_isUnit_iff_exists_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (X : Type w) (x : X → A.carrier)
    (P : FreeAlgebra (RatFunc F) X) :
    IsUnit (FreeAlgebra.lift (RatFunc F) x P) ↔ ∃ p : RationalFunctionPlace F,
      IsUnit (FreeAlgebra.lift (RatFunc F)
        (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P) := by
  have hcomm (p : RationalFunctionPlace F) :
      (rationalFunctionLocalScalarExtensionMap F p A).comp (FreeAlgebra.lift (RatFunc F) x) =
        FreeAlgebra.lift (RatFunc F)
          (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.coe_comp, FreeAlgebra.lift_ι_apply]
  constructor
  · intro h
    rcases (rationalFunctionLocalScalarExtensionMap_isUnit_iff_exists_place F A
      (FreeAlgebra.lift (RatFunc F) x P)).mp h with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    change IsUnit (((rationalFunctionLocalScalarExtensionMap F p A).comp
      (FreeAlgebra.lift (RatFunc F) x)) P) at hp
    rwa [hcomm p] at hp
  · rintro ⟨p, hp⟩
    apply (rationalFunctionLocalScalarExtensionMap_isUnit_iff_exists_place F A
      (FreeAlgebra.lift (RatFunc F) x P)).mpr
    refine ⟨p, ?_⟩
    change IsUnit (((rationalFunctionLocalScalarExtensionMap F p A).comp
      (FreeAlgebra.lift (RatFunc F) x)) P)
    rwa [hcomm p]

end GaloisForLFunctions.HTGeometry.ABHN
