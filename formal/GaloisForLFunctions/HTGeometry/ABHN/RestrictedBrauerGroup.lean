import GaloisForLFunctions.HTGeometry.ABHN.Places
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces

/-!
# Restricted local Brauer groups

The ABHN local term is a restricted product: a local Brauer family must be split at all but
finitely many places.  Tensor product and opposite preserve that condition, so the already
defined restricted-family carriers inherit commutative group structures.  This is independent of
the still-missing finite-ramification theorem that sends a global class into this subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Finite nonsplit support is closed under pointwise Brauer addition over a number field. -/
theorem hasFiniteNonSplitSupport_add (K : Type u) [Field K] [NumberField K]
    (x y : localBrauerClasses K)
    (hx : HasFiniteNonSplitSupport K x) (hy : HasFiniteNonSplitSupport K y) :
    HasFiniteNonSplitSupport K (x + y) := by
  apply (hx.union hy).subset
  intro v hv
  simp only [Set.mem_setOf_eq, Set.mem_union] at hv ⊢
  by_contra h
  push Not at h
  obtain ⟨hxv, hyv⟩ := h
  apply hv
  change x v + y v = brauerSplitClass (completion K v)
  rw [hxv, hyv]
  change (0 : BrauerGroup (completion K v)) + 0 = 0
  exact add_zero 0

/-- Finite nonsplit support is closed under pointwise Brauer inverse over a number field. -/
theorem hasFiniteNonSplitSupport_neg (K : Type u) [Field K] [NumberField K]
    (x : localBrauerClasses K) (hx : HasFiniteNonSplitSupport K x) :
    HasFiniteNonSplitSupport K (-x) := by
  apply hx.subset
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  intro hxv
  apply hv
  change -x v = brauerSplitClass (completion K v)
  rw [hxv]
  change -0 = 0
  exact neg_zero

/-- The restricted product of number-field local Brauer groups is a commutative group. -/
noncomputable instance restrictedLocalBrauerClassesAddCommGroup
    (K : Type u) [Field K] [NumberField K] :
    AddCommGroup (RestrictedLocalBrauerClasses K) := by
  let localZero : Zero (RestrictedLocalBrauerClasses K) := ⟨restrictedSplitClass K⟩
  let localAdd : Add (RestrictedLocalBrauerClasses K) := ⟨fun x y ↦
    { toLocalBrauerClasses := x.toLocalBrauerClasses + y.toLocalBrauerClasses
      finite_nonSplit_support := hasFiniteNonSplitSupport_add K x.toLocalBrauerClasses
        y.toLocalBrauerClasses x.finite_nonSplit_support y.finite_nonSplit_support }⟩
  let localNeg : Neg (RestrictedLocalBrauerClasses K) := ⟨fun x ↦
    { toLocalBrauerClasses := -x.toLocalBrauerClasses
      finite_nonSplit_support := hasFiniteNonSplitSupport_neg K x.toLocalBrauerClasses
        x.finite_nonSplit_support }⟩
  letI : Zero (RestrictedLocalBrauerClasses K) := localZero
  letI : Add (RestrictedLocalBrauerClasses K) := localAdd
  let localMonoid : AddCommMonoid (RestrictedLocalBrauerClasses K) :=
    { add := localAdd.add
      add_assoc := by
        intro x y z
        apply RestrictedLocalBrauerClasses.ext
        funext v
        exact add_assoc _ _ _
      zero := localZero.zero
      zero_add := by
        intro x
        apply RestrictedLocalBrauerClasses.ext
        funext v
        exact zero_add _
      add_zero := by
        intro x
        apply RestrictedLocalBrauerClasses.ext
        funext v
        exact add_zero _
      nsmul := nsmulRec
      add_comm := by
        intro x y
        apply RestrictedLocalBrauerClasses.ext
        funext v
        exact add_comm _ _ }
  letI : AddCommMonoid (RestrictedLocalBrauerClasses K) := localMonoid
  letI : Neg (RestrictedLocalBrauerClasses K) := localNeg
  exact
    { toAddCommMonoid := localMonoid
      neg := localNeg.neg
      zsmul := zsmulRec
      neg_add_cancel := by
        intro x
        apply RestrictedLocalBrauerClasses.ext
        funext v
        exact neg_add_cancel _ }

/-- Finite nonsplit support is closed under pointwise Brauer addition for `F(t)`. -/
theorem rationalFunctionHasFiniteNonSplitSupport_add (F : Type u) [Field F] [Finite F]
    (x y : rationalFunctionLocalBrauerClasses F)
    (hx : RationalFunctionHasFiniteNonSplitSupport F x)
    (hy : RationalFunctionHasFiniteNonSplitSupport F y) :
    RationalFunctionHasFiniteNonSplitSupport F (x + y) := by
  apply (hx.union hy).subset
  intro v hv
  simp only [Set.mem_setOf_eq, Set.mem_union] at hv ⊢
  by_contra h
  push Not at h
  obtain ⟨hxv, hyv⟩ := h
  apply hv
  change x v + y v = brauerSplitClass (rationalFunctionCompletion F v)
  rw [hxv, hyv]
  change (0 : BrauerGroup (rationalFunctionCompletion F v)) + 0 = 0
  exact add_zero 0

/-- Finite nonsplit support is closed under pointwise Brauer inverse for `F(t)`. -/
theorem rationalFunctionHasFiniteNonSplitSupport_neg (F : Type u) [Field F] [Finite F]
    (x : rationalFunctionLocalBrauerClasses F)
    (hx : RationalFunctionHasFiniteNonSplitSupport F x) :
    RationalFunctionHasFiniteNonSplitSupport F (-x) := by
  apply hx.subset
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  intro hxv
  apply hv
  change -x v = brauerSplitClass (rationalFunctionCompletion F v)
  rw [hxv]
  change -0 = 0
  exact neg_zero

/-- The restricted product of rational-function-field local Brauer groups is a commutative
group. -/
noncomputable instance rationalFunctionRestrictedLocalBrauerClassesAddCommGroup
    (F : Type u) [Field F] [Finite F] :
    AddCommGroup (RationalFunctionRestrictedLocalBrauerClasses F) := by
  let localZero : Zero (RationalFunctionRestrictedLocalBrauerClasses F) :=
    ⟨rationalFunctionRestrictedSplitClass F⟩
  let localAdd : Add (RationalFunctionRestrictedLocalBrauerClasses F) := ⟨fun x y ↦
    { toLocalBrauerClasses := x.toLocalBrauerClasses + y.toLocalBrauerClasses
      finite_nonSplit_support := rationalFunctionHasFiniteNonSplitSupport_add F
        x.toLocalBrauerClasses y.toLocalBrauerClasses x.finite_nonSplit_support
          y.finite_nonSplit_support }⟩
  let localNeg : Neg (RationalFunctionRestrictedLocalBrauerClasses F) := ⟨fun x ↦
    { toLocalBrauerClasses := -x.toLocalBrauerClasses
      finite_nonSplit_support := rationalFunctionHasFiniteNonSplitSupport_neg F
        x.toLocalBrauerClasses x.finite_nonSplit_support }⟩
  letI : Zero (RationalFunctionRestrictedLocalBrauerClasses F) := localZero
  letI : Add (RationalFunctionRestrictedLocalBrauerClasses F) := localAdd
  let localMonoid : AddCommMonoid (RationalFunctionRestrictedLocalBrauerClasses F) :=
    { add := localAdd.add
      add_assoc := by
        intro x y z
        apply RationalFunctionRestrictedLocalBrauerClasses.ext
        funext v
        exact add_assoc _ _ _
      zero := localZero.zero
      zero_add := by
        intro x
        apply RationalFunctionRestrictedLocalBrauerClasses.ext
        funext v
        exact zero_add _
      add_zero := by
        intro x
        apply RationalFunctionRestrictedLocalBrauerClasses.ext
        funext v
        exact add_zero _
      nsmul := nsmulRec
      add_comm := by
        intro x y
        apply RationalFunctionRestrictedLocalBrauerClasses.ext
        funext v
        exact add_comm _ _ }
  letI : AddCommMonoid (RationalFunctionRestrictedLocalBrauerClasses F) := localMonoid
  letI : Neg (RationalFunctionRestrictedLocalBrauerClasses F) := localNeg
  exact
    { toAddCommMonoid := localMonoid
      neg := localNeg.neg
      zsmul := zsmulRec
      neg_add_cancel := by
        intro x
        apply RationalFunctionRestrictedLocalBrauerClasses.ext
        funext v
        exact neg_add_cancel _ }

end GaloisForLFunctions.HTGeometry.ABHN
