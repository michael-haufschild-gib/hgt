import GaloisForLFunctions.GaloisTheoryOfZeros.TheFiniteSourceCompositaOfTheZeros

/-!
# The cofinal height tower of the whole zero field

Complete ordinate fibres with absolute height at most a natural number give
finite source splitting fields. Their union is the entire centered zero field,
and compatible automorphisms of these actual source stages extend uniquely.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- All occupied ordinate fibres in the closed height slab. -/
def heightFibreOrdinates (n : ℕ) : Finset ℝ := by
  classical
  exact (xiZeroCopyClosedRectangle (⟨-(n : ℝ),-1/2⟩ : ℂ)
    (⟨(n : ℝ),1/2⟩ : ℂ)).image fun q => (xiSpectralPoint q).re

private theorem height_rectangle_mem (n : ℕ) (q : XiZeroCopy) :
    q ∈ xiZeroCopyClosedRectangle (⟨-(n : ℝ),-1/2⟩ : ℂ) (⟨(n : ℝ),1/2⟩ : ℂ) ↔
      |(xiSpectralPoint q).re| ≤ (n : ℝ) := by
  rw [mem_xiZeroCopyClosedRectangle,Complex.mem_reProdIm]
  change ((xiSpectralPoint q).re ∈ uIcc (-(n : ℝ)) (n : ℝ) ∧
    (xiSpectralPoint q).im ∈ uIcc (-1/2 : ℝ) (1/2 : ℝ)) ↔ _
  rw [uIcc_of_le (neg_le_self (Nat.cast_nonneg n)),
    uIcc_of_le (show (-1/2 : ℝ) ≤ 1/2 by norm_num)]
  constructor
  · intro h
    exact abs_le.mpr h.1
  · intro h
    have hs := xiSpectralPoint_im_mem_openHalf q
    exact ⟨abs_le.mp h,hs.1.le,hs.2.le⟩

/-- Height selection includes a whole fibre precisely when it is occupied and lies in the slab. -/
theorem mem_heightFibreOrdinates (n : ℕ) (t : ℝ) :
    t ∈ heightFibreOrdinates n ↔
      (∃ q : XiZeroCopy, (xiSpectralPoint q).re = t) ∧ |t| ≤ (n : ℝ) := by
  classical
  constructor
  · intro ht
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp ht
    exact ⟨⟨q,he⟩,he ▸ (height_rectangle_mem n q).mp hq⟩
  · rintro ⟨⟨q,he⟩,ht⟩
    apply Finset.mem_image.mpr
    refine ⟨q,(height_rectangle_mem n q).mpr ?_,he⟩
    rwa [he]

/-- The height selections increase and never truncate an occupied fibre. -/
theorem heightFibreOrdinates_mono {n m : ℕ} (hnm : n ≤ m) :
    heightFibreOrdinates n ⊆ heightFibreOrdinates m := by
  intro t ht
  obtain ⟨hq,ht⟩ := (mem_heightFibreOrdinates n t).mp ht
  exact (mem_heightFibreOrdinates m t).mpr ⟨hq,ht.trans (by exact_mod_cast hnm)⟩

/-- Every zero belongs to one of the complete height stages. -/
theorem exists_heightFibreOrdinate (q : XiZeroCopy) :
    ∃ n : ℕ, (xiSpectralPoint q).re ∈ heightFibreOrdinates n := by
  obtain ⟨n,hn⟩ := exists_nat_ge |(xiSpectralPoint q).re|
  exact ⟨n,(mem_heightFibreOrdinates n _).mpr ⟨⟨q,rfl⟩,hn⟩⟩

/-- The source splitting field of all complete fibres through height `n`. -/
def heightFibreField (n : ℕ) : IntermediateField fullFibreSourceField fullFibreZeroExtension :=
  finiteFibreField (heightFibreOrdinates n)

instance heightFibreField_finite (n : ℕ) :
    FiniteDimensional fullFibreSourceField (heightFibreField n) :=
  finiteFibreField_finite (heightFibreOrdinates n)

instance heightFibreField_normal (n : ℕ) : Normal fullFibreSourceField (heightFibreField n) :=
  finiteFibreField_normal (heightFibreOrdinates n)

instance heightFibreField_isGalois (n : ℕ) : IsGalois fullFibreSourceField (heightFibreField n) :=
  finiteFibreField_isGalois (heightFibreOrdinates n)

/-- These finite source splitting fields form an increasing tower. -/
theorem heightFibreField_mono {n m : ℕ} (hnm : n ≤ m) :
    heightFibreField n ≤ heightFibreField m :=
  finiteFibreField_mono (heightFibreOrdinates_mono hnm)

private theorem finite_ordinate_height_bound (S : Finset ℝ) :
    ∃ n : ℕ, ∀ t ∈ S, |t| ≤ (n : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert t S ht ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨m,hm⟩ := exists_nat_ge |t|
    refine ⟨max n m,fun u hu => ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hm.trans (by exact_mod_cast Nat.le_max_right n m)
    · exact (hn u hu).trans (by exact_mod_cast Nat.le_max_left n m)

/-- The countable height tower is cofinal among all finite complete-fibre source composita. -/
theorem finiteFibreField_le_height (S : Finset ℝ) :
    ∃ n : ℕ, finiteFibreField S ≤ heightFibreField n := by
  classical
  obtain ⟨n,hn⟩ := finite_ordinate_height_bound S
  refine ⟨n,?_⟩
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply (singleFibreField_le_iff t (heightFibreField n)).mpr
  intro z
  obtain ⟨q,hq,hqz⟩ := Finset.mem_image.mp z.property
  have hqt := (mem_ordinateFibreCopies t q).mp hq
  have htH : t ∈ heightFibreOrdinates n :=
    (mem_heightFibreOrdinates n t).mpr ⟨⟨q,hqt⟩,hn t ht⟩
  exact fibreRootInField_mem_finite htH z

/-- The cofinal height tower exhausts the entire infinite centered zero field. -/
theorem iSup_heightFibreField : (⨆ n : ℕ, heightFibreField n) = ⊤ := by
  apply top_unique
  rw [← iSup_finiteFibreField]
  apply iSup_le
  intro S
  obtain ⟨n,hn⟩ := finiteFibreField_le_height S
  exact hn.trans (le_iSup heightFibreField n)

namespace SourceTower

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (T : ℕ → IntermediateField K L) (hT : Monotone T)

/-- The specified inclusions of an increasing sequence of intermediate fields. -/
def inclusion {n m : ℕ} (h : n ≤ m) : T n →ₐ[K] T m :=
  IntermediateField.inclusion (hT h)

/-- Stage automorphisms agree under the specified inclusions. -/
def Compatible (τ : ∀ n, T n ≃ₐ[K] T n) : Prop :=
  ∀ (n m : ℕ) (h : n ≤ m) (x : T n),
    (τ m (inclusion T hT h x) : L) = (τ n x : L)

/-- Compatible stage automorphisms form the inverse-limit group. -/
def limit : Subgroup (∀ n, T n ≃ₐ[K] T n) where
  carrier := {τ | Compatible T hT τ}
  one_mem' := by intro n m h x; rfl
  mul_mem' {a b} ha hb := by
    intro n m h x
    have hb' : b m (inclusion T hT h x) = inclusion T hT h (b n x) :=
      Subtype.ext (hb n m h x)
    change (a m (b m (inclusion T hT h x)) : L) = (a n (b n x) : L)
    rw [hb']
    exact ha n m h (b n x)
  inv_mem' {a} ha := by
    intro n m h x
    have hf : a m (inclusion T hT h ((a n).symm x)) = inclusion T hT h x := by
      apply Subtype.ext
      rw [ha n m h ((a n).symm x),(a n).apply_symm_apply]
      rfl
    have he := congrArg (a m).symm hf
    rw [(a m).symm_apply_apply] at he
    exact congrArg (fun y : T m => (y : L)) he.symm

variable [∀ n, Normal K (T n)]

private theorem restriction_coe (σ : L ≃ₐ[K] L) (n : ℕ) (x : T n) :
    ((σ.restrictNormal (T n)) x : L) = σ (x : L) :=
  AlgEquiv.restrictNormal_commutes σ (T n) x

/-- Restriction into an increasing sequence of normal intermediate fields. -/
def restriction : (L ≃ₐ[K] L) →* limit T hT where
  toFun σ := ⟨fun n => σ.restrictNormal (T n),by
    intro n m h x
    rw [restriction_coe,restriction_coe]
    rfl⟩
  map_one' := by
    apply Subtype.ext
    funext n
    exact (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) (T n)).map_one
  map_mul' σ τ := by
    apply Subtype.ext
    funext n
    exact (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) (T n)).map_mul σ τ

/-- The ambient value of a stage restriction is the original automorphism's value. -/
theorem restriction_apply (σ : L ≃ₐ[K] L) (n : ℕ) (x : T n) :
    ((restriction T hT σ).val n x : L) = σ (x : L) :=
  restriction_coe T σ n x

private theorem finite_natural_bound (S : Finset ℕ) : ∃ N : ℕ, ∀ n ∈ S, n ≤ N := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert n S hn ih =>
    obtain ⟨N,hN⟩ := ih
    refine ⟨max n N,fun m hm => ?_⟩
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact Nat.le_max_left _ _
    · exact (hN m hm).trans (Nat.le_max_right n N)

/-- Compactness extends a compatible family of normal-stage automorphisms. -/
theorem restriction_surjective [IsGalois K L] : Function.Surjective (restriction T hT) := by
  intro τ
  let C : ℕ → Set (L ≃ₐ[K] L) := fun n => {σ | σ.restrictNormal (T n) = τ.val n}
  have hclosed : ∀ n, IsClosed (C n) := by
    intro n
    exact isClosed_eq (InfiniteGalois.restrictNormalHom_continuous (T n)) continuous_const
  have hfinite : ∀ S : Finset ℕ, (⋂ n ∈ S, C n).Nonempty := by
    intro S
    obtain ⟨N,hN⟩ := finite_natural_bound S
    obtain ⟨σ,hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := T N) L (τ.val N)
    change σ.restrictNormal (T N) = τ.val N at hσ
    refine ⟨σ,?_⟩
    apply Set.mem_iInter.mpr
    intro n
    apply Set.mem_iInter.mpr
    intro hn
    change σ.restrictNormal (T n) = τ.val n
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [restriction_coe]
    have he := DFunLike.congr_fun hσ (inclusion T hT (hN n hn) x)
    have hv := congrArg (fun y : T N => (y : L)) he
    rw [restriction_coe] at hv
    exact hv.trans (τ.property n N (hN n hn) x)
  obtain ⟨σ,hσ⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨σ,?_⟩
  apply Subtype.ext
  funext n
  exact Set.mem_iInter.mp hσ n

/-- The inverse-limit restriction respects the Krull topologies. -/
theorem restriction_continuous : Continuous (restriction T hT) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun n => InfiniteGalois.restrictNormalHom_continuous (T n)

end SourceTower

/-- Inclusion of an earlier source height stage into a later one. -/
abbrev heightFibreInclusion {n m : ℕ} (hnm : n ≤ m) :
    heightFibreField n →ₐ[fullFibreSourceField] heightFibreField m :=
  SourceTower.inclusion heightFibreField (fun _ _ h => heightFibreField_mono h) hnm

/-- Compatibility in the actual inclusions of the height tower. -/
abbrev HeightGaloisCompatible
    (τ : ∀ n : ℕ, heightFibreField n ≃ₐ[fullFibreSourceField] heightFibreField n) : Prop :=
  SourceTower.Compatible heightFibreField (fun _ _ h => heightFibreField_mono h) τ

/-- The inverse limit of the finite source Galois groups along complete height stages. -/
abbrev heightSourceGaloisLimit :=
  SourceTower.limit heightFibreField (fun _ _ h => heightFibreField_mono h)

/-- Restriction of a full source automorphism to every complete height stage. -/
abbrev heightSourceRestriction :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      heightSourceGaloisLimit :=
  SourceTower.restriction heightFibreField (fun _ _ h => heightFibreField_mono h)

/-- All height restrictions determine the action on every zero, hence on the entire field. -/
theorem heightSourceRestriction_injective : Function.Injective heightSourceRestriction := by
  classical
  intro σ τ hστ
  apply allFibreAction_injective
  funext t
  apply Equiv.ext
  intro z
  obtain ⟨q,hq,hqz⟩ := Finset.mem_image.mp z.property
  obtain ⟨n,hn⟩ := exists_heightFibreOrdinate q
  have ht : t ∈ heightFibreOrdinates n := by
    rwa [(mem_ordinateFibreCopies t q).mp hq] at hn
  let x : heightFibreField n := fibreRootAtStage (heightFibreOrdinates n) t ht z
  have he := congrArg (fun f : heightSourceGaloisLimit => (f.val n x : fullFibreZeroExtension)) hστ
  rw [SourceTower.restriction_apply,SourceTower.restriction_apply] at he
  apply Subtype.ext
  exact congrArg (fun y : fullFibreZeroExtension => (y : ℂ)) he

/-- Compatible automorphisms of the actual finite source stages extend to the whole zero field. -/
theorem heightSourceRestriction_surjective : Function.Surjective heightSourceRestriction := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  exact SourceTower.restriction_surjective heightFibreField (fun _ _ h => heightFibreField_mono h)

/-- The full source Galois group is the inverse limit of its countable complete-height tower. -/
def heightSourceGaloisEquiv :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) ≃*
      heightSourceGaloisLimit :=
  MulEquiv.ofBijective heightSourceRestriction
    ⟨heightSourceRestriction_injective,heightSourceRestriction_surjective⟩

/-- The countable inverse-limit coordinates respect the Krull topology. -/
theorem heightSourceRestriction_continuous : Continuous heightSourceRestriction :=
  SourceTower.restriction_continuous heightFibreField (fun _ _ h => heightFibreField_mono h)


/-- The height inverse-limit equivalence also recovers the full Krull topology. -/
def heightSourceGaloisHomeomorph :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) ≃ₜ
      heightSourceGaloisLimit := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := heightSourceGaloisEquiv.toEquiv) heightSourceRestriction_continuous

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.finiteFibreField_le_height
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.iSup_heightFibreField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.heightSourceRestriction_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.heightSourceRestriction_surjective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.heightSourceGaloisEquiv

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.heightSourceGaloisHomeomorph
