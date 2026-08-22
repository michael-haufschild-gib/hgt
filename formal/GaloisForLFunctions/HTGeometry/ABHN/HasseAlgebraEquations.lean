import GaloisForLFunctions.HTGeometry.ABHN.LocalScalarExtension

/-!
# Hasse detection for equations in central simple algebras

For a fixed central simple algebra over a global field, an equation among specified global
elements holds exactly when it holds after scalar extension to every completion.  This is
representative-level separation, not the ABHN statement that local Brauer *classes* glue.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

/-- A specified multiplication equation in a central simple algebra over a number field holds
exactly when its scalar extension holds at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_mul_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (a b c : A.carrier) :
    a * b = c ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a *
        numberFieldLocalScalarExtensionMap K p A b =
          numberFieldLocalScalarExtensionMap K p A c := by
  constructor
  · intro h p
    calc
      numberFieldLocalScalarExtensionMap K p A a * numberFieldLocalScalarExtensionMap K p A b =
          numberFieldLocalScalarExtensionMap K p A (a * b) :=
        (map_mul (numberFieldLocalScalarExtensionMap K p A) a b).symm
      _ = numberFieldLocalScalarExtensionMap K p A c :=
        congrArg (numberFieldLocalScalarExtensionMap K p A) h
  · intro h
    apply numberFieldLocalScalarExtensionMap_injective K (witnessPlace K) A
    calc
      numberFieldLocalScalarExtensionMap K (witnessPlace K) A (a * b) =
          numberFieldLocalScalarExtensionMap K (witnessPlace K) A a *
            numberFieldLocalScalarExtensionMap K (witnessPlace K) A b :=
        map_mul (numberFieldLocalScalarExtensionMap K (witnessPlace K) A) a b
      _ = numberFieldLocalScalarExtensionMap K (witnessPlace K) A c := h (witnessPlace K)

/-- A specified multiplication equation in a central simple algebra over `F(t)` holds exactly
when its scalar extension holds at every finite and infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mul_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (a b c : A.carrier) :
    a * b = c ↔ ∀ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a *
        rationalFunctionLocalScalarExtensionMap F p A b =
          rationalFunctionLocalScalarExtensionMap F p A c := by
  constructor
  · intro h p
    calc
      rationalFunctionLocalScalarExtensionMap F p A a *
          rationalFunctionLocalScalarExtensionMap F p A b =
          rationalFunctionLocalScalarExtensionMap F p A (a * b) :=
        (map_mul (rationalFunctionLocalScalarExtensionMap F p A) a b).symm
      _ = rationalFunctionLocalScalarExtensionMap F p A c :=
        congrArg (rationalFunctionLocalScalarExtensionMap F p A) h
  · intro h
    apply rationalFunctionLocalScalarExtensionMap_injective F .infinite A
    calc
      rationalFunctionLocalScalarExtensionMap F .infinite A (a * b) =
          rationalFunctionLocalScalarExtensionMap F .infinite A a *
            rationalFunctionLocalScalarExtensionMap F .infinite A b :=
        map_mul (rationalFunctionLocalScalarExtensionMap F .infinite A) a b
      _ = rationalFunctionLocalScalarExtensionMap F .infinite A c := h .infinite

/-- A specified multiplication equation in a number-field CSA holds exactly when it holds at one
completion. -/
theorem numberFieldLocalScalarExtensionMap_mul_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (a b c : A.carrier) :
    a * b = c ↔ ∃ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a *
        numberFieldLocalScalarExtensionMap K p A b =
          numberFieldLocalScalarExtensionMap K p A c := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldLocalScalarExtensionMap_mul_eq_iff_forall_place K A a b c).mp h
        (witnessPlace K)⟩
  · rintro ⟨p, hp⟩
    apply numberFieldLocalScalarExtensionMap_injective K p A
    calc
      numberFieldLocalScalarExtensionMap K p A (a * b) =
          numberFieldLocalScalarExtensionMap K p A a *
            numberFieldLocalScalarExtensionMap K p A b :=
        map_mul (numberFieldLocalScalarExtensionMap K p A) a b
      _ = numberFieldLocalScalarExtensionMap K p A c := hp

/-- A specified multiplication equation in a rational-function-field CSA holds exactly when it
holds at one finite or infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mul_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (a b c : A.carrier) :
    a * b = c ↔ ∃ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a *
        rationalFunctionLocalScalarExtensionMap F p A b =
          rationalFunctionLocalScalarExtensionMap F p A c := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionLocalScalarExtensionMap_mul_eq_iff_forall_place F A a b c).mp h
        .infinite⟩
  · rintro ⟨p, hp⟩
    apply rationalFunctionLocalScalarExtensionMap_injective F p A
    calc
      rationalFunctionLocalScalarExtensionMap F p A (a * b) =
          rationalFunctionLocalScalarExtensionMap F p A a *
            rationalFunctionLocalScalarExtensionMap F p A b :=
        map_mul (rationalFunctionLocalScalarExtensionMap F p A) a b
      _ = rationalFunctionLocalScalarExtensionMap F p A c := hp

end GaloisForLFunctions.HTGeometry.ABHN
