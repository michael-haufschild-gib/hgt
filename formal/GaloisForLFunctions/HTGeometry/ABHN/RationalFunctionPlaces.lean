import GaloisForLFunctions.HTGeometry.ABHN.BrauerGroupStructure
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Rational-function-field places for Albert--Brauer--Hasse--Noether

For a finite field `F`, this file packages every place of the global function field `F(t)`:
height-one places of `F[t]` and the place at infinity.  Each branch uses Mathlib's actual
completion and canonical embedding.  This gives the function-field analogue of the number-field
place layer without adding any local-global axiom.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial

universe u

/-- Finite places and infinity of the rational global function field `F(t)`. -/
inductive RationalFunctionPlace (F : Type u) [Field F] [Finite F] where
  | finite : HeightOneSpectrum F[X] → RationalFunctionPlace F
  | infinite : RationalFunctionPlace F

/-- Completion of `F(t)` at a finite place or at infinity. -/
noncomputable def rationalFunctionCompletion (F : Type u) [Field F] [Finite F] :
    RationalFunctionPlace F → Type u := by
  classical
  exact fun
    | .finite v => v.adicCompletion (RatFunc F)
    | .infinite => RatFunc.CompletionAtInfty F

/-- Every packaged rational-function-field completion is a field. -/
noncomputable instance rationalFunctionCompletionField (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) : Field (rationalFunctionCompletion F v) := by
  classical
  cases v with
  | finite v =>
      change Field (v.adicCompletion (RatFunc F))
      infer_instance
  | infinite =>
      change Field (RatFunc.CompletionAtInfty F)
      infer_instance

/-- Each rational-function-field completion is canonically an `F(t)`-algebra. -/
noncomputable instance rationalFunctionCompletionAlgebra (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) : Algebra (RatFunc F) (rationalFunctionCompletion F v) := by
  classical
  cases v with
  | finite v =>
      change Algebra (RatFunc F) (v.adicCompletion (RatFunc F))
      infer_instance
  | infinite =>
      change Algebra (RatFunc F) (RatFunc.CompletionAtInfty F)
      infer_instance

/-- Canonical embedding into the completion at a rational-function-field place. -/
noncomputable def rationalFunctionPlaceEmbedding (F : Type u) [Field F] [Finite F] :
    (v : RationalFunctionPlace F) → RatFunc F →+* rationalFunctionCompletion F v := by
  classical
  exact fun
    | .finite v => NumberField.FinitePlace.embedding v
    | .infinite => algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)

/-- Each local embedding of `F(t)` is injective. -/
theorem rationalFunctionPlaceEmbedding_injective (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) : Function.Injective (rationalFunctionPlaceEmbedding F v) := by
  exact (rationalFunctionPlaceEmbedding F v).injective

/-- Diagonal embedding of `F(t)` into its completed local fields. -/
noncomputable def rationalFunctionPlaceDiagonal (F : Type u) [Field F] [Finite F] :
    RatFunc F → ((v : RationalFunctionPlace F) → rationalFunctionCompletion F v) :=
  fun x v => rationalFunctionPlaceEmbedding F v x

/-- A rational function is determined by its local images. -/
theorem rationalFunctionPlaceDiagonal_injective (F : Type u) [Field F] [Finite F] :
    Function.Injective (rationalFunctionPlaceDiagonal F) := by
  intro x y hxy
  exact rationalFunctionPlaceEmbedding_injective F .infinite (congr_fun hxy .infinite)

/-- Family of local Brauer-class carriers for `F(t)`. -/
noncomputable def rationalFunctionLocalBrauerClasses (F : Type u) [Field F] [Finite F] :=
  (v : RationalFunctionPlace F) → BrauerGroup (rationalFunctionCompletion F v)

/-- Pointwise Brauer-group structure on rational-function-field local Brauer families. -/
noncomputable instance rationalFunctionLocalBrauerClassesAddCommGroup
    (F : Type u) [Field F] [Finite F] :
    AddCommGroup (rationalFunctionLocalBrauerClasses F) :=
  show AddCommGroup ((v : RationalFunctionPlace F) →
    BrauerGroup (rationalFunctionCompletion F v)) from inferInstance

/-- Finite-support condition for the local Brauer term of the function-field ABHN sequence. -/
def RationalFunctionHasFiniteNonSplitSupport (F : Type u) [Field F] [Finite F]
    (x : rationalFunctionLocalBrauerClasses F) : Prop :=
  {v | x v ≠ brauerSplitClass (rationalFunctionCompletion F v)}.Finite

/-- Carrier of finite-support local Brauer families for `F(t)`. -/
structure RationalFunctionRestrictedLocalBrauerClasses (F : Type u) [Field F] [Finite F] where
  toLocalBrauerClasses : rationalFunctionLocalBrauerClasses F
  finite_nonSplit_support : RationalFunctionHasFiniteNonSplitSupport F toLocalBrauerClasses

/-- Extensionality for finite-support local Brauer families of `F(t)`. -/
@[ext]
theorem RationalFunctionRestrictedLocalBrauerClasses.ext
    {F : Type u} [Field F] [Finite F]
    {x y : RationalFunctionRestrictedLocalBrauerClasses F}
    (h : x.toLocalBrauerClasses = y.toLocalBrauerClasses) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Everywhere-split local Brauer family for `F(t)`. -/
noncomputable def rationalFunctionRestrictedSplitClass (F : Type u) [Field F] [Finite F] :
    RationalFunctionRestrictedLocalBrauerClasses F where
  toLocalBrauerClasses := fun v => brauerSplitClass (rationalFunctionCompletion F v)
  finite_nonSplit_support := by simp [RationalFunctionHasFiniteNonSplitSupport]

end GaloisForLFunctions.HTGeometry.ABHN
