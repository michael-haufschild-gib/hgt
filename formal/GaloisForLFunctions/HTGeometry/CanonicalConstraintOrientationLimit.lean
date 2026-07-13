import Mathlib.Tactic

/-!
# Canonical inverse limit of finite constraint--orientation stages

A coherent family of downward-closed constraint geometries on all finite vertex sets and Boolean
orientations on all finite label sets is reconstructed uniquely from one global abstract
constraint geometry and one global Boolean sequence.  The two finite index sets are independent;
this is the exact set-level inverse limit behind the constraint--orientation product.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- A possibly empty abstract simplicial constraint geometry. -/
structure AbstractConstraintGeometry (α : Type*) [DecidableEq α] where
  IsFace : Finset α → Prop
  downward : ∀ {I J : Finset α}, I ⊆ J → IsFace J → IsFace I

@[ext]
theorem AbstractConstraintGeometry.ext
    {α : Type*} [DecidableEq α]
    {K L : AbstractConstraintGeometry α}
    (h : ∀ J, K.IsFace J ↔ L.IsFace J) : K = L := by
  cases K with
  | mk k hk =>
    cases L with
    | mk l hl =>
      simp only [mk.injEq]
      funext J
      exact propext (h J)

/-- A coherent thread through every finite constraint stage and every finite orientation stage. -/
structure FiniteConstraintOrientationThread
    (α β : Type*) [DecidableEq α] [DecidableEq β] where
  face : (S : Finset α) → Finset α → Prop
  face_supported : ∀ {S J}, face S J → J ⊆ S
  face_downward : ∀ {S I J}, I ⊆ J → face S J → face S I
  negative : (T : Finset β) → Finset β
  negative_supported : ∀ T, negative T ⊆ T
  face_compatible : ∀ {S T}, S ⊆ T → ∀ {J}, J ⊆ S → (face S J ↔ face T J)
  negative_compatible : ∀ {S T}, S ⊆ T → ∀ {p}, p ∈ S →
    (p ∈ negative S ↔ p ∈ negative T)

@[ext]
theorem FiniteConstraintOrientationThread.ext
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {X Y : FiniteConstraintOrientationThread α β}
    (hface : ∀ S J, X.face S J ↔ Y.face S J)
    (hnegative : ∀ S, X.negative S = Y.negative S) : X = Y := by
  cases X with
  | mk xf xfs xfd xn xns xfc xnc =>
    cases Y with
    | mk yf yfs yfd yn yns yfc ync =>
      have hf : xf = yf := by
        funext S J
        exact propext (hface S J)
      have hn : xn = yn := by
        funext S
        exact hnegative S
      subst yf
      subst yn
      rfl

/-- The explicit global model of the finite constraint--orientation inverse limit. -/
abbrev CanonicalConstraintOrientationLimit
    (α β : Type*) [DecidableEq α] [DecidableEq β] :=
  AbstractConstraintGeometry α × (β → Bool)

def canonicalLimitToThread
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : CanonicalConstraintOrientationLimit α β) :
    FiniteConstraintOrientationThread α β := by
  classical
  exact {
  face S J := J ⊆ S ∧ X.1.IsFace J
  face_supported h := h.1
  face_downward hIJ hJ := ⟨hIJ.trans hJ.1, X.1.downward hIJ hJ.2⟩
  negative S := S.filter fun p => X.2 p = true
  negative_supported S := Finset.filter_subset _ _
  face_compatible hST := by
    intro J hJS
    constructor
    · exact fun h => ⟨hJS.trans hST, h.2⟩
    · exact fun h => ⟨hJS, h.2⟩
  negative_compatible hST := by
    intro p hpS
    simp [hpS, hST hpS]
  }

def threadToCanonicalLimit
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : FiniteConstraintOrientationThread α β) :
    CanonicalConstraintOrientationLimit α β :=
  ({ IsFace := fun J => X.face J J
     downward := by
       intro I J hIJ hJ
       have hJI : X.face J I := X.face_downward hIJ hJ
       exact (X.face_compatible hIJ (Finset.Subset.rfl)).mpr hJI },
   fun p => decide (p ∈ X.negative {p}))

theorem threadToCanonicalLimit_toThread
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : CanonicalConstraintOrientationLimit α β) :
    threadToCanonicalLimit (canonicalLimitToThread X) = X := by
  classical
  apply Prod.ext
  · apply AbstractConstraintGeometry.ext
    intro J
    change (J ⊆ J ∧ X.1.IsFace J) ↔ X.1.IsFace J
    simp
  · ext p
    cases hp : X.2 p <;> simp [threadToCanonicalLimit, canonicalLimitToThread, hp]

theorem canonicalLimitToThread_threadToCanonicalLimit
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : FiniteConstraintOrientationThread α β) :
    canonicalLimitToThread (threadToCanonicalLimit X) = X := by
  classical
  apply FiniteConstraintOrientationThread.ext
  · intro S J
    change (J ⊆ S ∧ X.face J J) ↔ X.face S J
    constructor
    · intro h
      exact (X.face_compatible h.1 (Finset.Subset.rfl)).mp h.2
    · intro h
      have hJS := X.face_supported h
      exact ⟨hJS, (X.face_compatible hJS (Finset.Subset.rfl)).mpr h⟩
  · intro S
    ext p
    simp only [canonicalLimitToThread, Finset.mem_filter]
    change (p ∈ S ∧ decide (p ∈ X.negative {p}) = true) ↔ p ∈ X.negative S
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hpS, hpneg⟩
      exact (X.negative_compatible (by simpa using hpS) (by simp)).mp hpneg
    · intro hpneg
      have hpS := X.negative_supported S hpneg
      exact ⟨hpS,
        (X.negative_compatible (by simpa using hpS) (by simp)).mpr hpneg⟩

/-- **Canonical inverse-limit identification.** Restriction to all finite stages is equivalent to
one global downward-closed constraint geometry and one global Boolean orientation sequence. -/
def canonicalConstraintOrientationLimitEquiv
    (α β : Type*) [DecidableEq α] [DecidableEq β] :
    CanonicalConstraintOrientationLimit α β ≃ FiniteConstraintOrientationThread α β where
  toFun := canonicalLimitToThread
  invFun := threadToCanonicalLimit
  left_inv := threadToCanonicalLimit_toThread
  right_inv := canonicalLimitToThread_threadToCanonicalLimit

end
end GaloisForLFunctions.HTGeometry
