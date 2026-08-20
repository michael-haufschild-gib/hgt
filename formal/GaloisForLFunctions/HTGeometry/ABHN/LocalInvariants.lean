import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import GaloisForLFunctions.HTGeometry.ABHN.LocalScalarExtension
import GaloisForLFunctions.HTGeometry.ABHN.Specification
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Algebraically closed local Brauer invariants

This is the archimedean complex piece of the ABHN local theory.  A finite-dimensional central
simple algebra over an algebraically closed field is a matrix algebra, hence its Brauer class is
split.  Consequently its local invariant has image `{0}`.  This is applied to every complex
infinite completion of a number field.  Nonarchimedean local fields require the separate
local-class-field-theory theorem `Br(K_v) ≃ ℚ/ℤ`, which is not yet in Mathlib.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-- Algebraic closedness transports along a field equivalence even when its source and target
live in different Lean universes. -/
theorem isAlgClosed_of_ringEquiv {F : Type u} {E : Type v} [Field F] [Field E]
    (e : F ≃+* E) [IsAlgClosed F] : IsAlgClosed E := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := F) (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  use e x
  rw [Polynomial.IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

/-- Every central simple algebra over an algebraically closed field has split Brauer class. -/
theorem brauerClass_eq_split_of_isAlgClosed (F : Type u) [Field F] [IsAlgClosed F]
    (A : CSA.{u, u} F) : brauerClass A = brauerSplitClass F := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed F A.carrier
  calc
    brauerClass A = brauerClass (matrixFinCSA (scalarCSA F) n) :=
      brauerClass_eq_of_algEquiv _ _ e
    _ = brauerSplitClass F := brauerClass_matrixFinCSA_scalar_eq n

/-- The Brauer quotient of an algebraically closed field is trivial. -/
theorem brauerGroup_eq_split_of_isAlgClosed (F : Type u) [Field F] [IsAlgClosed F]
    (x : BrauerGroup.{u, u} F) : x = brauerSplitClass F := by
  refine Quotient.inductionOn x ?_
  exact brauerClass_eq_split_of_isAlgClosed F

/-- The algebraically closed local Brauer group has one element. -/
theorem brauerGroup_subsingleton_of_isAlgClosed (F : Type u) [Field F] [IsAlgClosed F] :
    Subsingleton (BrauerGroup.{u, u} F) where
  allEq x y := (brauerGroup_eq_split_of_isAlgClosed F x).trans
    (brauerGroup_eq_split_of_isAlgClosed F y).symm

/-- The local Brauer quotient over an algebraically closed field is canonically equivalent to
the one-point type. -/
noncomputable def algClosedBrauerEquivPUnit (F : Type u) [Field F] [IsAlgClosed F] :
    BrauerGroup.{u, u} F ≃ PUnit := by
  letI : Subsingleton (BrauerGroup.{u, u} F) := brauerGroup_subsingleton_of_isAlgClosed F
  letI : Nonempty (BrauerGroup.{u, u} F) := ⟨brauerSplitClass F⟩
  exact Equiv.punitOfNonemptyOfSubsingleton

/-- The local invariant at an algebraically closed place is zero. -/
noncomputable def algClosedLocalInvariant (F : Type u) [Field F] [IsAlgClosed F] :
    BrauerGroup.{u, u} F → RatModInt := fun _ => 0

/-- The algebraically closed local invariant as an additive homomorphism. -/
noncomputable def algClosedLocalInvariantAddHom (F : Type u) [Field F] [IsAlgClosed F] :
    BrauerGroup.{u, u} F →+ RatModInt where
  toFun := algClosedLocalInvariant F
  map_zero' := rfl
  map_add' := by intros; simp [algClosedLocalInvariant]

theorem algClosedLocalInvariant_eq_zero (F : Type u) [Field F] [IsAlgClosed F]
    (x : BrauerGroup.{u, u} F) : algClosedLocalInvariant F x = 0 := rfl

theorem algClosedLocalInvariant_injective (F : Type u) [Field F] [IsAlgClosed F] :
    Function.Injective (algClosedLocalInvariant F) := by
  letI : Subsingleton (BrauerGroup.{u, u} F) := brauerGroup_subsingleton_of_isAlgClosed F
  intro x y _
  exact Subsingleton.elim _ _

/-- The only local invariant realized over an algebraically closed field is zero. -/
theorem algClosedLocalInvariant_range (F : Type u) [Field F] [IsAlgClosed F] :
    Set.range (algClosedLocalInvariant F) = {0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨brauerSplitClass F, rfl⟩

/-- At an algebraically closed local field, the local invariant is an isomorphism onto the
singleton subgroup `{0} ⊂ ℚ/ℤ`. -/
noncomputable def algClosedLocalInvariantEquivZero (F : Type u) [Field F] [IsAlgClosed F] :
    BrauerGroup.{u, u} F ≃ {q : RatModInt | q = 0} :=
  Equiv.ofBijective (fun x ↦ ⟨algClosedLocalInvariant F x,
    algClosedLocalInvariant_eq_zero F x⟩) ⟨
    (fun x y h ↦ algClosedLocalInvariant_injective F (Subtype.ext_iff.mp h)),
    (by
      rintro ⟨q, hq⟩
      subst q
      refine ⟨brauerSplitClass F, ?_⟩
      exact Subtype.ext (algClosedLocalInvariant_eq_zero F (brauerSplitClass F)))⟩

/-- At a complex infinite place of a number field, the completed local Brauer quotient is
trivial. -/
theorem complexInfiniteCompletion_brauer_subsingleton (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex) :
    Subsingleton (BrauerGroup.{u, u} v.Completion) := by
  letI : IsAlgClosed v.Completion := isAlgClosed_of_ringEquiv
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  exact brauerGroup_subsingleton_of_isAlgClosed v.Completion

/-- The complex infinite-place local invariant. -/
noncomputable def complexInfiniteCompletionLocalInvariant (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (_ : v.IsComplex) :
    BrauerGroup.{u, u} v.Completion → RatModInt := fun _ => 0

/-- The complex infinite-place invariant as an additive homomorphism. -/
noncomputable def complexInfiniteCompletionLocalInvariantAddHom
    (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex) :
    BrauerGroup.{u, u} v.Completion →+ RatModInt where
  toFun := complexInfiniteCompletionLocalInvariant K v hv
  map_zero' := rfl
  map_add' := by intros; simp [complexInfiniteCompletionLocalInvariant]

theorem complexInfiniteCompletion_localInvariant_eq_zero (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex)
    (x : BrauerGroup.{u, u} v.Completion) :
    complexInfiniteCompletionLocalInvariant K v hv x = 0 := rfl

theorem complexInfiniteCompletion_localInvariant_injective (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex) :
    Function.Injective (complexInfiniteCompletionLocalInvariant K v hv) := by
  letI : Subsingleton (BrauerGroup.{u, u} v.Completion) :=
    complexInfiniteCompletion_brauer_subsingleton K v hv
  intro x y _
  exact Subsingleton.elim _ _

/-- At a complex infinite place, the local invariant is an isomorphism onto `{0} ⊂ ℚ/ℤ`. -/
noncomputable def complexInfiniteCompletionLocalInvariantEquivZero
    (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex) :
    BrauerGroup.{u, u} v.Completion ≃ {q : RatModInt | q = 0} := by
  letI : IsAlgClosed v.Completion := isAlgClosed_of_ringEquiv
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  exact algClosedLocalInvariantEquivZero v.Completion

/-- This complex-place invariant equivalence is induced by the defined local-invariant map. -/
theorem complexInfiniteCompletionLocalInvariantEquivZero_apply
    (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex)
    (x : BrauerGroup.{u, u} v.Completion) :
    (complexInfiniteCompletionLocalInvariantEquivZero K v hv x).1 =
      complexInfiniteCompletionLocalInvariant K v hv x := rfl

/-- Scalar extension of a global central simple algebra is split at every complex infinite place.
Thus these places make no contribution to the ABHN local class family. -/
theorem complexInfiniteLocalBrauerClass_eq_split (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex) (A : CSA.{u, u} K) :
    brauerClass (numberFieldLocalCSA K (.infinite v) A) = brauerSplitClass v.Completion := by
  letI : IsAlgClosed (completion K (.infinite v)) := by
    change IsAlgClosed v.Completion
    exact isAlgClosed_of_ringEquiv
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  exact brauerClass_eq_split_of_isAlgClosed (completion K (.infinite v))
    (numberFieldLocalCSA K (.infinite v) A)

/-- The local invariant of a scalar-extended global central simple algebra vanishes at every
complex infinite place. -/
theorem complexInfiniteLocalBrauerClass_invariant_eq_zero
    (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex) (A : CSA.{u, u} K) :
    complexInfiniteCompletionLocalInvariant K v hv
      (brauerClass (numberFieldLocalCSA K (.infinite v) A)) = 0 := by
  exact complexInfiniteCompletion_localInvariant_eq_zero K v hv _

/-- Every global Brauer class becomes split at a complex infinite completion.  This is the
quotient-level form of the fact that complex places contribute zero to ABHN reciprocity. -/
theorem complexInfiniteLocalBrauerMap_eq_split (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex) (x : BrauerGroup.{u, u} K) :
    numberFieldLocalBrauerMap K x (.infinite v) = brauerSplitClass v.Completion := by
  refine Quotient.inductionOn x ?_
  intro A
  change brauerClass (numberFieldLocalCSA K (.infinite v) A) = brauerSplitClass v.Completion
  exact complexInfiniteLocalBrauerClass_eq_split K v hv A

/-- The local invariant of every global Brauer class vanishes at a complex infinite completion. -/
theorem complexInfiniteLocalBrauerMap_invariant_eq_zero (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (hv : v.IsComplex) (x : BrauerGroup.{u, u} K) :
    complexInfiniteCompletionLocalInvariant K v hv (numberFieldLocalBrauerMap K x (.infinite v)) =
      0 := by
  exact complexInfiniteCompletion_localInvariant_eq_zero K v hv _

/-- The contribution of one infinite place to the complex part of the ABHN invariant sum.
Real places contribute zero here by definition; complex places use their actual local invariant. -/
noncomputable def complexInfiniteInvariantContribution (K : Type u) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x : BrauerGroup.{u, u} K) : RatModInt := by
  classical
  exact if hv : v.IsComplex then
    complexInfiniteCompletionLocalInvariant K v hv
      (scalarExtensionBrauerMap K v.Completion x)
  else 0

/-- The complex archimedean summand of global reciprocity vanishes.  This is a closed fragment
of ABHN reciprocity; real and nonarchimedean summands require their local invariant theories. -/
theorem sum_complexInfiniteInvariantContribution_eq_zero
    (K : Type u) [Field K] [NumberField K] (x : BrauerGroup.{u, u} K) :
    ∑ v : NumberField.InfinitePlace K, complexInfiniteInvariantContribution K v x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v.IsComplex
  · simp only [complexInfiniteInvariantContribution, dif_pos hv]
    exact complexInfiniteLocalBrauerMap_invariant_eq_zero K v hv x
  · simp [complexInfiniteInvariantContribution, hv]

/-- The nonsplit support of a global Brauer class contains no complex infinite place.  Thus the
only possible archimedean contribution to ABHN finite ramification is at real places. -/
theorem numberFieldLocalBrauerMap_nonSplitSupport_subset_notComplexInfinite
    (K : Type u) [Field K] [NumberField K] (x : BrauerGroup.{u, u} K) :
    {w | numberFieldLocalBrauerMap K x w ≠ brauerSplitClass (completion K w)} ⊆
      {w | ∀ v : NumberField.InfinitePlace K, v.IsComplex → w ≠ .infinite v} := by
  rintro w hw v hv rfl
  exact hw (complexInfiniteLocalBrauerMap_eq_split K v hv x)

/-- The infinite-place nonsplit support of a global Brauer class is contained in the real
places. -/
theorem numberFieldLocalBrauerMap_infiniteNonSplitSupport_subset_notComplex
    (K : Type u) [Field K] [NumberField K] (x : BrauerGroup.{u, u} K) :
    {v : NumberField.InfinitePlace K |
      numberFieldLocalBrauerMap K x (.infinite v) ≠ brauerSplitClass v.Completion} ⊆
      {v | ¬v.IsComplex} := by
  intro v hv hvc
  exact hv (complexInfiniteLocalBrauerMap_eq_split K v hvc x)

/-- The infinite-place contribution to nonsplit support is finite.  Thus the only unresolved
part of the ABHN finite-ramification theorem is the nonarchimedean contribution. -/
theorem numberFieldLocalBrauerMap_infiniteNonSplitSupport_finite
    (K : Type u) [Field K] [NumberField K] (x : BrauerGroup.{u, u} K) :
    {v : NumberField.InfinitePlace K |
      numberFieldLocalBrauerMap K x (.infinite v) ≠ brauerSplitClass v.Completion}.Finite :=
  Set.finite_univ.subset fun _ _ ↦ Set.mem_univ _

end GaloisForLFunctions.HTGeometry.ABHN
