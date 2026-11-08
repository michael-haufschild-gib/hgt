import DifferentialGeometry.Topology.Homology.Relative.Excision
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.FiniteConeComplexesHaveSphereBouquets
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Singular Euler characteristic of finite face realizations

Excision gives Euler additivity for open covers and finite inclusion-exclusion.
The positive-coordinate stars of a finite face complex form a good cover:
each nonempty intersection contracts to its face barycenter. Thus actual
singular homology is finite and its Euler characteristic equals the
alternating count of nonempty faces.
-/
noncomputable section


open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties
open DifferentialGeometry.Homology

/-- Flatten a relative intersection subtype to the actual intersection. -/
def openCoverIntersectionHomeomorph (X : TopCat.{0}) (s t : Set X) :
    {x : s // (x:X)∈t} ≃ₜ (s∩t : Set X) where
  toFun x := ⟨x.val.val,x.val.property,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Finite homology transfers through actual excision isomorphisms. -/
theorem finiteRelativeType_of_openCover (X : TopCat.{0}) (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) (hcover : s∪t=Set.univ)
    (hfs : finiteHomologyType ℚ (TopCat.of s))
    (hfi : finiteHomologyType ℚ (TopCat.of (s∩t : Set X))) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex X t (ModuleCat.of ℚ ℚ)) := by
  have hi := (finiteHomologyType_iff_of_homeomorph ℚ
    (X := TopCat.of {x : s | (x:X)∈t}) (Y := TopCat.of (s∩t : Set X))
    (openCoverIntersectionHomeomorph X s t)).mpr hfi
  have hr := finiteHomologyType_relativeChainComplex (TopCat.of s) {x : s | (x:X)∈t} ℚ hi hfs
  constructor
  · intro n
    letI : FiniteDimensional ℚ (relativeHomology (TopCat.of s)
      {x : s | (x:X)∈t} (ModuleCat.of ℚ ℚ) n) := hr.1 n
    change FiniteDimensional ℚ (relativeHomology X t (ModuleCat.of ℚ ℚ) n)
    exact (relativeExcisionIso X s t (ModuleCat.of ℚ ℚ) hs ht hcover n).toLinearEquiv.finiteDimensional
  · obtain ⟨N,hN⟩ := hr.2
    exact ⟨N,fun n hn => (hN n hn).of_iso
      (relativeExcisionIso X s t (ModuleCat.of ℚ ℚ) hs ht hcover n).symm⟩

/-- A two-set open cover with finite-homology pieces and intersection has finite homology. -/
theorem finiteHomologyType_of_openCover (X : TopCat.{0}) (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) (hcover : s∪t=Set.univ)
    (hfs : finiteHomologyType ℚ (TopCat.of s))
    (hft : finiteHomologyType ℚ (TopCat.of t))
    (hfi : finiteHomologyType ℚ (TopCat.of (s∩t : Set X))) : finiteHomologyType ℚ X :=
  DifferentialGeometry.HomologicalComplex.finiteHomologyType_middle
    (relativeShortComplex X t (ModuleCat.of ℚ ℚ)) (relativeShortExact X t (ModuleCat.of ℚ ℚ))
    hft (finiteRelativeType_of_openCover X s t hs ht hcover hfs hfi)

/-- Euler additivity comes from excision and the actual relative singular-homology sequence. -/
theorem eulerChar_openCover (X : TopCat.{0}) (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) (hcover : s∪t=Set.univ)
    (hfs : finiteHomologyType ℚ (TopCat.of s))
    (hft : finiteHomologyType ℚ (TopCat.of t))
    (hfi : finiteHomologyType ℚ (TopCat.of (s∩t : Set X))) :
    eulerChar ℚ X=eulerChar ℚ (TopCat.of s)+eulerChar ℚ (TopCat.of t)-
      eulerChar ℚ (TopCat.of (s∩t : Set X)) := by
  have hi := (finiteHomologyType_iff_of_homeomorph ℚ
    (X := TopCat.of {x : s | (x:X)∈t}) (Y := TopCat.of (s∩t : Set X))
    (openCoverIntersectionHomeomorph X s t)).mpr hfi
  have hX := finiteHomologyType_of_openCover X s t hs ht hcover hfs hft hfi
  have hr : relativeEulerChar (TopCat.of s) {x : s | (x:X)∈t} ℚ=relativeEulerChar X t ℚ := by
    apply finsum_congr
    intro n
    exact congrArg (fun r : ℕ => ((ComplexShape.down ℕ).χ n : ℤ)*(r:ℤ))
      (relativeExcisionIso X s t (ModuleCat.of ℚ ℚ) hs ht hcover n).toLinearEquiv.finrank_eq
  have hl := relativeEulerChar_eq_sub (TopCat.of s) {x : s | (x:X)∈t} ℚ hi hfs
  have htgt := relativeEulerChar_eq_sub X t ℚ hft hX
  have he := eulerChar_eq_of_homeomorph ℚ (X := TopCat.of {x : s | (x:X)∈t})
    (Y := TopCat.of (s∩t : Set X)) (openCoverIntersectionHomeomorph X s t)
  omega

#print axioms finiteHomologyType_of_openCover
#print axioms eulerChar_openCover

/-- Restricting the ambient space to a larger subset does not change a subspace. -/
def subsetAmbientHomeomorph {X : Type*} [TopologicalSpace X] (s u : Set X) (hsu : s⊆u) :
    {x : u // (x:X)∈s} ≃ₜ s where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,hsu x.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The same comparison for intersections inside a union. -/
def unionIntersectionHomeomorph {X : Type*} [TopologicalSpace X] (s t : Set X) :
    ({x : (s∪t : Set X) | (x:X)∈s} ∩ {x : (s∪t : Set X) | (x:X)∈t} : Set ↥(s∪t : Set X)) ≃ₜ (s∩t : Set X) where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,Or.inl x.property.1⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Finiteness and Euler additivity for two open subspaces, without an ambient finiteness assumption. -/
theorem finiteHomologyType_eulerChar_union (X : TopCat.{0}) (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t)
    (hfs : finiteHomologyType ℚ (TopCat.of s))
    (hft : finiteHomologyType ℚ (TopCat.of t))
    (hfi : finiteHomologyType ℚ (TopCat.of (s∩t : Set X))) :
    finiteHomologyType ℚ (TopCat.of (s∪t : Set X)) ∧
    eulerChar ℚ (TopCat.of (s∪t : Set X))=
      eulerChar ℚ (TopCat.of s)+eulerChar ℚ (TopCat.of t)-eulerChar ℚ (TopCat.of (s∩t : Set X)) := by
  let Y := TopCat.of (s∪t : Set X)
  let U : Set Y := {x | (x:X)∈s}
  let V : Set Y := {x | (x:X)∈t}
  have hU : IsOpen U := hs.preimage continuous_subtype_val
  have hV : IsOpen V := ht.preimage continuous_subtype_val
  have hcov : U∪V=Set.univ := by
    ext x
    exact iff_true_intro x.property
  let eU : U ≃ₜ s := subsetAmbientHomeomorph s (s∪t) Set.subset_union_left
  let eV : V ≃ₜ t := subsetAmbientHomeomorph t (s∪t) Set.subset_union_right
  let eI : (U∩V : Set Y) ≃ₜ (s∩t : Set X) := unionIntersectionHomeomorph s t
  have hfU := (finiteHomologyType_iff_of_homeomorph ℚ (X := TopCat.of U) (Y := TopCat.of s) eU).mpr hfs
  have hfV := (finiteHomologyType_iff_of_homeomorph ℚ (X := TopCat.of V) (Y := TopCat.of t) eV).mpr hft
  have hfI := (finiteHomologyType_iff_of_homeomorph ℚ (X := TopCat.of (U∩V : Set Y))
    (Y := TopCat.of (s∩t : Set X)) eI).mpr hfi
  refine ⟨finiteHomologyType_of_openCover Y U V hU hV hcov hfU hfV hfI,?_⟩
  have he := eulerChar_openCover Y U V hU hV hcov hfU hfV hfI
  rw [eulerChar_eq_of_homeomorph ℚ (X := TopCat.of U) (Y := TopCat.of s) eU,
    eulerChar_eq_of_homeomorph ℚ (X := TopCat.of V) (Y := TopCat.of t) eV,
    eulerChar_eq_of_homeomorph ℚ (X := TopCat.of (U∩V : Set Y))
      (Y := TopCat.of (s∩t : Set X)) eI] at he
  exact he

#print axioms finiteHomologyType_eulerChar_union


/-- A contractible local block has relative Euler characteristic one minus that of its exit model. -/
theorem relativeEuler_contractible_exit (X Y : TopCat.{0}) (A : Set X)
    [ContractibleSpace X] (e : A ≃ₕ Y) (hY : finiteHomologyType ℚ Y) :
    relativeEulerChar X A ℚ=1-eulerChar ℚ Y := by
  have hA := (finiteHomologyType_iff_of_homotopyEquiv ℚ (X := TopCat.of A) (Y := Y) e).mpr hY
  have hX := finiteHomologyType_of_contractible ℚ (X := X)
  calc
    relativeEulerChar X A ℚ=eulerChar ℚ X-eulerChar ℚ (TopCat.of A) :=
      relativeEulerChar_eq_sub X A ℚ hA hX
    _=1-eulerChar ℚ Y := by
      rw [eulerChar_of_contractible,eulerChar_eq_of_homotopyEquiv ℚ (X := TopCat.of A) (Y := Y) e]

/-- An empty ambient space has zero relative singular Euler characteristic. -/
theorem relativeEuler_empty (X : TopCat.{0}) (A : Set X) [IsEmpty X] :
    relativeEulerChar X A ℚ=0 := by
  have hA := finiteHomologyType_of_subsingleton ℚ (X := TopCat.of A)
  have hX := finiteHomologyType_of_subsingleton ℚ (X := X)
  rw [relativeEulerChar_eq_sub X A ℚ hA hX,eulerChar_of_isEmpty,eulerChar_of_isEmpty,sub_self]

#print axioms relativeEuler_contractible_exit
#print axioms relativeEuler_empty

end GaloisForLFunctions.HodgeTheoryWithoutVarieties


open Finset
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties
open DifferentialGeometry.Homology
variable {ι : Type} [DecidableEq ι]

def finiteCoverUnion {X : Type} (U : ι → Set X) (I : Finset ι) : Set X :=
  ⋃ i∈I,U i

def finiteCoverIntersection {X : Type} (U : ι → Set X) (S : Finset ι) : Set X :=
  {x | ∀i∈S,x∈U i}

omit [DecidableEq ι] in
theorem finiteCoverIntersection_singleton {X : Type} (U : ι → Set X) (i : ι) :
    finiteCoverIntersection U {i}=U i := by
  ext x
  simp only [finiteCoverIntersection,Set.mem_setOf_eq,mem_singleton,forall_eq]

theorem finiteCoverIntersection_adjoin {X : Type} (U : ι → Set X) (a : ι)
    (S : Finset ι) (hS : S.Nonempty) :
    finiteCoverIntersection (fun i => U a∩U i) S=finiteCoverIntersection U (insert a S) := by
  ext x
  constructor
  · intro h
    obtain ⟨j,hj⟩ := hS
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact (h j hj).1
    · exact (h i hi).2
  · intro h i hi
    exact ⟨h a (mem_insert_self a S),h i (mem_insert_of_mem hi)⟩

def finiteCoverEulerSummand (X : TopCat.{0}) (U : ι → Set X) (S : Finset ι) : ℤ :=
  if S=∅ then 0 else (-1)^(S.card+1)*eulerChar ℚ (TopCat.of (finiteCoverIntersection U S))

def finiteCoverEulerSum (X : TopCat.{0}) (U : ι → Set X) (I : Finset ι) : ℤ :=
  ∑S∈I.powerset,finiteCoverEulerSummand X U S

/-- Inserting one open set gives the same recursion as two-set Euler additivity. -/
theorem finiteCoverEulerSum_insert (X : TopCat.{0}) (U : ι → Set X) (I : Finset ι)
    (a : ι) (ha : a∉I) :
    finiteCoverEulerSum X U (insert a I)=eulerChar ℚ (TopCat.of (U a))+
      finiteCoverEulerSum X U I-finiteCoverEulerSum X (fun i => U a∩U i) I := by
  have hterm (S : Finset ι) (hS : S∈I.powerset) :
      finiteCoverEulerSummand X U (insert a S)=
        (if S=∅ then eulerChar ℚ (TopCat.of (U a)) else 0)-
          finiteCoverEulerSummand X (fun i => U a∩U i) S := by
    have haS : a∉S := fun h => ha (mem_powerset.mp hS h)
    by_cases he : S=∅
    · subst S
      simp only [finiteCoverEulerSummand,insert_empty_eq,Finset.singleton_ne_empty,if_false,
        card_singleton,show (1:ℕ)+1=2 from rfl,neg_one_sq,one_mul,
        ite_true,sub_zero]
      exact congrArg (fun A : Set X => eulerChar ℚ (TopCat.of A))
        (finiteCoverIntersection_singleton U a)
    · unfold finiteCoverEulerSummand
      rw [if_neg (insert_nonempty a S).ne_empty,if_neg he,if_neg he,
        ←finiteCoverIntersection_adjoin U a S (nonempty_iff_ne_empty.mpr he),card_insert_of_notMem haS]
      simp only [pow_succ]
      ring
  unfold finiteCoverEulerSum
  rw [sum_powerset_insert ha]
  have hs : (∑S∈I.powerset,finiteCoverEulerSummand X U (insert a S))=
      eulerChar ℚ (TopCat.of (U a))-∑S∈I.powerset,finiteCoverEulerSummand X (fun i => U a∩U i) S := by
    rw [sum_congr rfl hterm,sum_sub_distrib]
    simp only [sum_ite_eq',empty_mem_powerset,ite_true]
  rw [hs]
  ring

/-- Finite open inclusion-exclusion, proved on actual singular homology. -/
theorem finiteCover_homology_euler (X : TopCat.{0}) (I : Finset ι) (U : ι → Set X)
    (hopen : ∀i∈I,IsOpen (U i))
    (hfinite : ∀S⊆I,S.Nonempty → finiteHomologyType ℚ (TopCat.of (finiteCoverIntersection U S))) :
    finiteHomologyType ℚ (TopCat.of (finiteCoverUnion U I)) ∧
    eulerChar ℚ (TopCat.of (finiteCoverUnion U I))=finiteCoverEulerSum X U I := by
  induction I using Finset.induction_on generalizing U with
  | empty =>
    have he : finiteCoverUnion U ∅=∅ := by
      ext x
      simp only [finiteCoverUnion,Set.mem_iUnion,Set.mem_empty_iff_false]
      constructor
      · rintro ⟨i,hi,_⟩
        exact (Finset.notMem_empty i hi).elim
      · intro hx
        exact hx.elim
    rw [he]
    constructor
    · exact finiteHomologyType_of_subsingleton ℚ
    · rw [eulerChar_of_isEmpty]
      simp only [finiteCoverEulerSum,powerset_empty,sum_singleton,finiteCoverEulerSummand,ite_true]
  | @insert a I ha ih =>
    have hrest := ih U (fun i hi => hopen i (mem_insert_of_mem hi))
      (fun S hSI hS => hfinite S (hSI.trans (subset_insert a I)) hS)
    have hUa : finiteHomologyType ℚ (TopCat.of (U a)) := by
      have h := hfinite {a} (singleton_subset_iff.mpr (mem_insert_self a I)) (singleton_nonempty a)
      rwa [finiteCoverIntersection_singleton] at h
    have hinter := ih (fun i => U a∩U i)
      (fun i hi => (hopen a (mem_insert_self a I)).inter (hopen i (mem_insert_of_mem hi))) (by
        intro S hSI hS
        rw [finiteCoverIntersection_adjoin U a S hS]
        exact hfinite (insert a S) (insert_subset_insert a hSI) (insert_nonempty a S))
    have hInter : finiteCoverUnion (fun i => U a∩U i) I=U a∩finiteCoverUnion U I := by
      ext x
      simp only [finiteCoverUnion,Set.mem_iUnion,Set.mem_inter_iff]
      constructor
      · rintro ⟨i,hi,hxa,hxi⟩
        exact ⟨hxa,i,hi,hxi⟩
      · rintro ⟨hxa,i,hi,hxi⟩
        exact ⟨i,hi,hxa,hxi⟩
    have hUnion : finiteCoverUnion U (insert a I)=U a∪finiteCoverUnion U I := by
      ext x
      simp only [finiteCoverUnion,Set.mem_iUnion,mem_insert,Set.mem_union]
      constructor
      · rintro ⟨i,hi,hx⟩
        rcases hi with rfl | hi
        · exact Or.inl hx
        · exact Or.inr ⟨i,hi,hx⟩
      · rintro (hx | ⟨i,hi,hx⟩)
        · exact ⟨a,Or.inl rfl,hx⟩
        · exact ⟨i,Or.inr hi,hx⟩
    have hOpenRest : IsOpen (finiteCoverUnion U I) :=
      isOpen_iUnion (fun i => isOpen_iUnion (fun hi : i∈I => hopen i (mem_insert_of_mem hi)))
    have hInterFinite : finiteHomologyType ℚ (TopCat.of (U a∩finiteCoverUnion U I : Set X)) := by
      rw [←hInter]
      exact hinter.1
    have h := finiteHomologyType_eulerChar_union X (U a) (finiteCoverUnion U I)
      (hopen a (mem_insert_self a I)) hOpenRest hUa hrest.1 hInterFinite
    rw [hUnion]
    refine ⟨h.1,?_⟩
    rw [h.2,hrest.2,←hInter,hinter.2,finiteCoverEulerSum_insert X U I a ha]

#print axioms finiteCoverEulerSum_insert
#print axioms finiteCover_homology_euler
end GaloisForLFunctions.HodgeTheoryWithoutVarieties


open Finset ContinuousMap
open DifferentialGeometry.Simplex
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties
open HodgeTheoryWithoutVarieties
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The actual positive-coordinate star intersection. -/
def faceStarIntersection (K : Finset (Finset V)) (S : Finset V) : Set (faceFamilySpace K) :=
  {x | ∀q∈S,0<x.val.val q}

/-- Equal barycentric mass on a prescribed nonempty face. -/
def finiteFaceBarycenter (S : Finset V) (hS : S.Nonempty) : stdSimplex ℝ V :=
  ⟨fun q => if q∈S then (S.card:ℝ)⁻¹ else 0,by
    have hc : 0<(S.card:ℝ) := Nat.cast_pos.mpr hS.card_pos
    constructor
    · intro q
      dsimp only
      split_ifs <;> positivity
    · change (∑ q,if q∈S then (S.card:ℝ)⁻¹ else 0)=1
      rw [sum_ite]
      have he : univ.filter (fun q => q∈S)=S := by ext q; simp only [mem_filter,mem_univ,true_and]
      rw [he]
      simp only [sum_const,nsmul_eq_mul,mul_zero,add_zero]
      exact mul_inv_cancel₀ hc.ne'⟩

theorem finiteFaceBarycenter_pos {S : Finset V} (hS : S.Nonempty) {q : V} (hq : q∈S) :
    0<(finiteFaceBarycenter S hS).val q := by
  change 0<(if q∈S then (S.card:ℝ)⁻¹ else 0)
  rw [if_pos hq]
  exact inv_pos.mpr (Nat.cast_pos.mpr hS.card_pos)

theorem finiteFaceBarycenter_support (S : Finset V) (hS : S.Nonempty) :
    finiteFaceBarycenter S hS∈supportFace S := by
  intro q hq
  change (if q∈S then (S.card:ℝ)⁻¹ else 0)=0
  rw [if_neg hq]

/-- Positive coordinates force the prescribed face into every containing support. -/
theorem faceStarIntersection_subset_support {K : Finset (Finset V)} {S T : Finset V}
    (x : faceStarIntersection K S) (hxT : x.val.val∈supportFace T) : S⊆T := by
  intro q hq
  by_contra hn
  exact (ne_of_gt (x.property q hq)) (hxT q hn)

/-- Nonempty intersections can occur only at actual faces. -/
theorem faceStarIntersection_face {K : Finset (Finset V)}
    (hdown : ∀T∈K,∀S⊆T,S∈K) {S : Finset V} (x : faceStarIntersection K S) : S∈K := by
  obtain ⟨T,hT,hxT⟩ := mem_faceFamilySpace.mp x.val.property
  exact hdown T hT S (faceStarIntersection_subset_support x hxT)

def faceStarBarycenter {K : Finset (Finset V)} (S : Finset V) (hS : S.Nonempty) (hSK : S∈K) :
    faceStarIntersection K S :=
  ⟨⟨finiteFaceBarycenter S hS,mem_faceFamilySpace.mpr ⟨S,hSK,finiteFaceBarycenter_support S hS⟩⟩,
    fun q hq => finiteFaceBarycenter_pos hS (q := q) hq⟩

/-- Straight interpolation of actual simplex points. -/
def faceBarycentricInterpolation (t : unitInterval) (x b : stdSimplex ℝ V) : stdSimplex ℝ V :=
  ⟨fun q => (1-(t:ℝ))*x.val q+(t:ℝ)*b.val q,by
    constructor
    · intro q
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (x.property.1 q))
        (mul_nonneg t.property.1 (b.property.1 q))
    · change (∑ q, ((1-(t:ℝ))*x.val q+(t:ℝ)*b.val q))=1
      rw [sum_add_distrib,←mul_sum,←mul_sum,x.property.2,b.property.2,mul_one,mul_one]
      ring⟩

def faceStarContractionPoint {K : Finset (Finset V)} (S : Finset V)
    (hS : S.Nonempty) (t : unitInterval) (x : faceStarIntersection K S) : faceStarIntersection K S := by
  let z := faceBarycentricInterpolation t x.val.val (finiteFaceBarycenter S hS)
  have hz : z∈faceFamilySpace K := by
    obtain ⟨T,hT,hxT⟩ := mem_faceFamilySpace.mp x.val.property
    have hST := faceStarIntersection_subset_support x hxT
    refine mem_faceFamilySpace.mpr ⟨T,hT,?_⟩
    intro q hq
    have hx0 : x.val.val.val q=0 := hxT q hq
    have hb0 : (finiteFaceBarycenter S hS).val q=0 :=
      finiteFaceBarycenter_support S hS q (fun h => hq (hST h))
    change (1-(t:ℝ))*x.val.val.val q+(t:ℝ)*(finiteFaceBarycenter S hS).val q=0
    simp only [hx0,hb0,mul_zero,add_zero]
  refine ⟨⟨z,hz⟩,?_⟩
  intro q hq
  change 0<(1-(t:ℝ))*x.val.val.val q+(t:ℝ)*(finiteFaceBarycenter S hS).val q
  have hx := x.property q hq
  have hb := finiteFaceBarycenter_pos hS hq
  by_cases ht : (t:ℝ)=1
  · rw [ht,sub_self,zero_mul,one_mul,zero_add]
    exact hb
  · have htt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 ht
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr htt) hx) (mul_nonneg t.property.1 hb.le)

/-- Each actual nonempty face intersection contracts inside every original containing face. -/
def faceStarIntersectionContraction {K : Finset (Finset V)} (S : Finset V) (hS : S.Nonempty) (hSK : S∈K) :
    (ContinuousMap.id (faceStarIntersection K S)).Homotopy
      (ContinuousMap.const _ (faceStarBarycenter S hS hSK)) where
  toFun z := faceStarContractionPoint S hS z.1 z.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro q
    change Continuous (fun z : unitInterval × faceStarIntersection K S =>
      (1-(z.1:ℝ))*z.2.val.val.val q+(z.1:ℝ)*(finiteFaceBarycenter S hS).val q)
    have ht : Continuous (fun z : unitInterval × faceStarIntersection K S => (z.1:ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun z : unitInterval × faceStarIntersection K S => z.2.val.val.val q) :=
      (continuous_apply q).comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
    exact ((continuous_const.sub ht).mul hx).add (ht.mul continuous_const)
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext q
    change (1-((0:unitInterval):ℝ))*x.val.val.val q+((0:unitInterval):ℝ)*
      (finiteFaceBarycenter S hS).val q=x.val.val.val q
    simp only [show ((0:unitInterval):ℝ)=0 from rfl,sub_zero,one_mul,zero_mul,add_zero]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext q
    change (1-((1:unitInterval):ℝ))*x.val.val.val q+((1:unitInterval):ℝ)*
      (finiteFaceBarycenter S hS).val q=(finiteFaceBarycenter S hS).val q
    simp only [show ((1:unitInterval):ℝ)=1 from rfl,sub_self,zero_mul,one_mul,zero_add]

/-- Every nonempty star intersection has finite singular homology and Euler number zero or one. -/
theorem faceStarIntersection_finite_euler (K : Finset (Finset V))
    (hdown : ∀T∈K,∀S⊆T,S∈K) (S : Finset V) (hS : S.Nonempty) :
    DifferentialGeometry.Homology.finiteHomologyType ℚ (TopCat.of (faceStarIntersection K S)) ∧
    DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of (faceStarIntersection K S))=
      if S∈K then 1 else 0 := by
  by_cases hSK : S∈K
  · letI : ContractibleSpace (faceStarIntersection K S) :=
      (contractible_iff_id_nullhomotopic _).mpr
        ⟨faceStarBarycenter S hS hSK,⟨faceStarIntersectionContraction S hS hSK⟩⟩
    rw [if_pos hSK]
    exact ⟨DifferentialGeometry.Homology.finiteHomologyType_of_contractible ℚ,
      DifferentialGeometry.Homology.eulerChar_of_contractible ℚ⟩
  · letI : IsEmpty (faceStarIntersection K S) :=
      ⟨fun x => hSK (faceStarIntersection_face hdown x)⟩
    rw [if_neg hSK]
    exact ⟨DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton ℚ,
      DifferentialGeometry.Homology.eulerChar_of_isEmpty ℚ⟩

#print axioms faceStarIntersectionContraction
#print axioms faceStarIntersection_finite_euler

omit [DecidableEq V] in
/-- Finite intersections of positive-coordinate stars are open in the realization. -/
theorem isOpen_faceStarIntersection (K : Finset (Finset V)) (S : Finset V) :
    IsOpen (faceStarIntersection K S) := by
  unfold faceStarIntersection
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite (fun q => isOpen_iInter_of_finite (fun _ : q∈S =>
    isOpen_lt continuous_const ((continuous_apply q).comp
      (continuous_subtype_val.comp continuous_subtype_val))))

omit [DecidableEq V] in
/-- Every actual simplex point has a positive coordinate, so vertex stars cover the complex. -/
theorem faceVertexStars_cover (K : Finset (Finset V)) :
    (⋃q,faceStarIntersection K {q})=Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hex : ∃q,0<x.val.val q := by
    by_contra h
    push Not at h
    have hz (q : V) : x.val.val q=0 := le_antisymm (h q) (x.val.property.1 q)
    have hs := x.val.property.2
    simp only [hz,sum_const_zero] at hs
    exact zero_ne_one hs
  obtain ⟨q,hq⟩ := hex
  exact Set.mem_iUnion.mpr ⟨q,by
    intro r hr
    rw [mem_singleton] at hr
    simpa only [hr] using hq⟩

#print axioms isOpen_faceStarIntersection
#print axioms faceVertexStars_cover

end GaloisForLFunctions.HodgeTheoryWithoutVarieties


open Finset
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties
open HodgeTheoryWithoutVarieties DifferentialGeometry.Homology
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Coordinate-star intersections coincide with the literal finite-cover intersections. -/
theorem faceStars_coverIntersection (K : Finset (Finset V)) (S : Finset V) :
    finiteCoverIntersection (fun q => faceStarIntersection K {q}) S=faceStarIntersection K S := by
  ext x
  simp only [finiteCoverIntersection,faceStarIntersection,Set.mem_setOf_eq,mem_singleton,forall_eq]

/-- Finite face realizations have finite singular homology, with Euler characteristic given by cells. -/
theorem finiteFace_singular_euler (K : Finset (Finset V))
    (hdown : ∀T∈K,∀S⊆T,S∈K) :
    finiteHomologyType ℚ (TopCat.of (faceFamilySpace K)) ∧
    eulerChar ℚ (TopCat.of (faceFamilySpace K))=
      ∑S∈K.erase ∅,-((-1:ℤ)^S.card) := by
  let X := TopCat.of (faceFamilySpace K)
  let U : V → Set X := fun q => faceStarIntersection K {q}
  have hcov := finiteCover_homology_euler X univ U
    (fun q _ => isOpen_faceStarIntersection K {q}) (by
      intro S _ hS
      rw [show finiteCoverIntersection U S=faceStarIntersection K S from faceStars_coverIntersection K S]
      exact (faceStarIntersection_finite_euler K hdown S hS).1)
  have hunion : finiteCoverUnion U univ=Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x∈⋃q,faceStarIntersection K {q} := by rw [faceVertexStars_cover]; trivial
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨q,Set.mem_iUnion.mpr ⟨mem_univ q,hq⟩⟩
  let e : finiteCoverUnion U univ ≃ₜ X := {
    toFun := Subtype.val
    invFun := fun x => ⟨x,by rw [hunion]; trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := continuous_subtype_val
    continuous_invFun := continuous_id.subtype_mk (fun x => by rw [hunion]; trivial) }
  refine ⟨(finiteHomologyType_iff_of_homeomorph ℚ e).mp hcov.1,?_⟩
  change eulerChar ℚ X = _
  rw [←eulerChar_eq_of_homeomorph ℚ (X := TopCat.of (finiteCoverUnion U univ)) (Y := X) e,hcov.2]
  have hterm (S : Finset V) : finiteCoverEulerSummand X U S=
      if S∈K.erase ∅ then -((-1:ℤ)^S.card) else 0 := by
    by_cases he : S=∅
    · subst S
      simp only [finiteCoverEulerSummand,ite_true]
      rw [if_neg (fun h => (mem_erase.mp h).1 rfl)]
    · have hS := nonempty_iff_ne_empty.mpr he
      unfold finiteCoverEulerSummand
      rw [if_neg he,show finiteCoverIntersection U S=faceStarIntersection K S from faceStars_coverIntersection K S,
        (faceStarIntersection_finite_euler K hdown S hS).2]
      by_cases hSK : S∈K
      · rw [if_pos hSK,if_pos (mem_erase.mpr ⟨he,hSK⟩),mul_one,pow_succ]
        ring
      · rw [if_neg hSK,if_neg (fun h => hSK (mem_erase.mp h).2),mul_zero]
  unfold finiteCoverEulerSum
  simp_rw [hterm]
  rw [←sum_filter]
  have hf : univ.powerset.filter (fun S => S∈K.erase ∅)=K.erase ∅ := by
    ext S
    simp only [mem_filter,mem_powerset,subset_univ,true_and]
  rw [hf]

#print axioms finiteFace_singular_euler
end GaloisForLFunctions.HodgeTheoryWithoutVarieties