import GaloisForLFunctions.HTGeometry.ABHN.BrauerGroupStructure
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Number-field places for Albert--Brauer--Hasse--Noether

This file unifies Mathlib's finite and infinite number-field places.  It packages their
completions, canonical embeddings, the diagonal embedding, and the finite-support carrier for
the local Brauer classes in the ABHN sequence.  No local invariant or scalar-extension map is
postulated here; those need the next Brauer-algebra layer.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open NumberField

universe u

/-- All finite and infinite places of a number field. -/
inductive NumberFieldPlace (K : Type u) [Field K] [NumberField K] where
  | finite : FinitePlace K → NumberFieldPlace K
  | infinite : InfinitePlace K → NumberFieldPlace K

/-- Completion of a number field at an arbitrary place. -/
noncomputable def completion (K : Type u) [Field K] [NumberField K] :
    NumberFieldPlace K → Type u
  | .finite v => (FinitePlace.maximalIdeal v).adicCompletion K
  | .infinite v => v.Completion

/-- Every packaged completion is a field. -/
noncomputable instance completionField (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) : Field (completion K v) := by
  cases v with
  | finite v =>
      change Field (v.maximalIdeal.adicCompletion K)
      infer_instance
  | infinite v =>
      change Field v.Completion
      infer_instance

/-- Each packaged completion carries its canonical `K`-algebra structure. -/
noncomputable instance completionAlgebra (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) : Algebra K (completion K v) := by
  cases v with
  | finite v =>
      change Algebra K (v.maximalIdeal.adicCompletion K)
      infer_instance
  | infinite v =>
      change Algebra K v.Completion
      infer_instance

/-- Canonical embedding into the completion at a finite or infinite place. -/
noncomputable def placeEmbedding (K : Type u) [Field K] [NumberField K] :
    (v : NumberFieldPlace K) → K →+* completion K v
  | .finite v => FinitePlace.embedding (FinitePlace.maximalIdeal v)
  | .infinite v => algebraMap K v.Completion

/-- Every local completion embedding of a field is injective. -/
theorem placeEmbedding_injective (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) : Function.Injective (placeEmbedding K v) := by
  exact (placeEmbedding K v).injective

/-- The diagonal map to the family of all number-field completions. -/
noncomputable def placeDiagonal (K : Type u) [Field K] [NumberField K] :
    K → ((v : NumberFieldPlace K) → completion K v) :=
  fun x v => placeEmbedding K v x

/-- A fixed archimedean place, used only to prove diagonal injectivity. -/
noncomputable def witnessPlace (K : Type u) [Field K] [NumberField K] : NumberFieldPlace K :=
  .infinite (Classical.choice (inferInstance : Nonempty (InfinitePlace K)))

/-- A global element is determined by all of its local images. -/
theorem placeDiagonal_injective (K : Type u) [Field K] [NumberField K] :
    Function.Injective (placeDiagonal K) := by
  intro x y hxy
  exact placeEmbedding_injective K (witnessPlace K) (congr_fun hxy (witnessPlace K))

/-- The family of local Brauer-class carriers. -/
noncomputable def localBrauerClasses (K : Type u) [Field K] [NumberField K] :=
  (v : NumberFieldPlace K) → BrauerGroup (completion K v)

/-- Pointwise Brauer-group structure on families indexed by number-field places. -/
noncomputable instance localBrauerClassesAddCommGroup (K : Type u) [Field K] [NumberField K] :
    AddCommGroup (localBrauerClasses K) :=
  show AddCommGroup ((v : NumberFieldPlace K) → BrauerGroup (completion K v)) from inferInstance

/-- A local family has ABHN finite support when only finitely many classes are nonsplit. -/
def HasFiniteNonSplitSupport (K : Type u) [Field K] [NumberField K]
    (x : localBrauerClasses K) : Prop :=
  {v | x v ≠ brauerSplitClass (completion K v)}.Finite

/-- Carrier of the finite-support local term in the future ABHN exact sequence. -/
structure RestrictedLocalBrauerClasses (K : Type u) [Field K] [NumberField K] where
  toLocalBrauerClasses : localBrauerClasses K
  finite_nonSplit_support : HasFiniteNonSplitSupport K toLocalBrauerClasses

/-- Extensionality for finite-support local Brauer families. -/
@[ext]
theorem RestrictedLocalBrauerClasses.ext {K : Type u} [Field K] [NumberField K]
    {x y : RestrictedLocalBrauerClasses K}
    (h : x.toLocalBrauerClasses = y.toLocalBrauerClasses) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The everywhere-split local family is finite-supported. -/
noncomputable def restrictedSplitClass (K : Type u) [Field K] [NumberField K] :
    RestrictedLocalBrauerClasses K where
  toLocalBrauerClasses := fun v => brauerSplitClass (completion K v)
  finite_nonSplit_support := by simp [HasFiniteNonSplitSupport]

end GaloisForLFunctions.HTGeometry.ABHN
