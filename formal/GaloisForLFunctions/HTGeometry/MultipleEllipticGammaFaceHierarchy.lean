import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaReindex

/-!
# Intrinsic faces of the genuine multiple elliptic gamma hierarchy

The all-order hierarchy is indexed here by an unordered finite set of deleted parameters.  This
removes the nested-subtype artefact produced by repeated applications of the one-coordinate
hierarchy theorem.  Every coface relation is an equality in the actual global meromorphic field,
and therefore does not depend on a chosen deletion order.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Parameter labels surviving after deleting the finite face `J`. -/
abbrev MultipleEllipticGammaFaceIndex (J : Finset ι) := {i : ι // i ∉ J}

/-- The parameter family on the complement of a deleted face. -/
def multipleEllipticGammaFaceParameters
    (τ : ι → ℂ) (J : Finset ι) : MultipleEllipticGammaFaceIndex J → ℂ :=
  fun i => τ i

/-- The raw multiple elliptic-gamma function on the face obtained by deleting `J`. -/
def multipleEllipticGammaFaceMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    meroField (Set.univ : Set ℂ) :=
  multipleEllipticGammaMero
    (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i)

/-- The actual logarithmic-derivative coordinate on the face obtained by deleting `J`. -/
def multipleEllipticGammaLogDerivFaceMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    meroField (Set.univ : Set ℂ) :=
  multipleEllipticGammaLogDerivMero
    (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i)

/-- Deleting `q` after deleting `J` is canonically the same finite index type as deleting
`insert q J` at once. -/
def multipleEllipticGammaFaceInsertEquiv
    (J : Finset ι) (q : ι) (hq : q ∉ J) :
    MultipleEllipticGammaFaceIndex (insert q J) ≃
      {i : MultipleEllipticGammaFaceIndex J // i ≠ ⟨q, hq⟩} where
  toFun i :=
    ⟨⟨i.1, fun hiJ => i.2 (Finset.mem_insert_of_mem hiJ)⟩, by
      intro hiq
      apply i.2
      rw [Finset.mem_insert]
      exact Or.inl (congrArg Subtype.val hiq)⟩
  invFun i :=
    ⟨i.1.1, by
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun hiq => i.2 (Subtype.ext hiq), i.1.2⟩⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- **Intrinsic all-order coface equation.** Translating the genuine face coordinate in any
surviving structural direction and taking its defect deletes precisely that parameter.  The right
side is indexed by the unordered face `insert q J`, not by a nested deletion type. -/
theorem multipleEllipticGammaLogDerivFaceMero_addTranslation_sub
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) (q : ι) (hq : q ∉ J) :
    addTranslationMeroEquiv (τ q)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) -
      multipleEllipticGammaLogDerivFaceMero τ hτ J =
    multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J) := by
  let qJ : MultipleEllipticGammaFaceIndex J := ⟨q, hq⟩
  let τJ := multipleEllipticGammaFaceParameters τ J
  let hτJ : ∀ i, 0 < (τJ i).im := fun i => hτ i
  change addTranslationMeroEquiv (τJ qJ)
      (multipleEllipticGammaLogDerivMero τJ hτJ) -
        multipleEllipticGammaLogDerivMero τJ hτJ = _
  rw [multipleEllipticGammaLogDerivMero_addTranslation_sub τJ hτJ qJ]
  let e := multipleEllipticGammaFaceInsertEquiv J q hq
  symm
  exact multipleEllipticGammaLogDerivMero_reindex e
    (fun i : {i : MultipleEllipticGammaFaceIndex J // i ≠ qJ} => τJ i)
    (fun i => hτJ i)

/-- Two successive coface deletions commute at the level of the genuine global meromorphic
hierarchy. -/
theorem multipleEllipticGammaLogDerivFaceMero_insert_comm
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) (q r : ι) :
    multipleEllipticGammaLogDerivFaceMero τ hτ (insert q (insert r J)) =
      multipleEllipticGammaLogDerivFaceMero τ hτ (insert r (insert q J)) := by
  rw [Finset.insert_comm q r]

end

end GaloisForLFunctions
