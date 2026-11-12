import GaloisForLFunctions.GaloisTheoryOfZeros.TheFieldOfCompleteFibreTraces
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysDivisibleExtension
import Mathlib.GroupTheory.Goursat
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# The integral zero motive

The integer span of the complete centered zero divisor embeds faithfully in
its ordinate and width coordinate groups. Their common gluing quotient is
killed by two, and the span is exactly their fibre product. Every complex
character lifts to a pair of coordinate characters; the ambiguity consists
of opposite characters of the common quotient. The full source Galois group
acts faithfully, and conjugation fixes ordinates while reversing widths.

Restoring the central half-weight relates this centered motive to the integer
span of the original zeros. The resulting central quotient is cyclic and
killed by two. Character extensions obey a square-root law at the half-weight,
and the normalized exponential flow recovers the original flow exactly.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- The integer span of the complete centered zero divisor, with its actual additive relations. -/
def zeroRelationGroup : AddSubgroup fullFibreZeroExtension :=
  AddSubgroup.closure (Set.range centeredZeroInFibreExtension)

/-- Each divisor copy defines a generator of the integral zero relation group. -/
def zeroRelationRoot (q : XiZeroCopy) : zeroRelationGroup :=
  ⟨centeredZeroInFibreExtension q,AddSubgroup.subset_closure ⟨q,rfl⟩⟩

/-- The integral relation group embeds in the complex numbers. -/
def zeroRelationEmbedding : zeroRelationGroup →+ ℂ :=
  (IntermediateField.val fullFibreZeroExtension).toAddMonoidHom.comp zeroRelationGroup.subtype

theorem zeroRelationEmbedding_injective : Function.Injective zeroRelationEmbedding :=
  (IntermediateField.val fullFibreZeroExtension).injective.comp Subtype.val_injective

private theorem zeroRelation_aut_mem
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    {z : fullFibreZeroExtension} (hz : z ∈ zeroRelationGroup) : σ z ∈ zeroRelationGroup := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨q,rfl⟩ := hx
    obtain ⟨r,_,hr⟩ := fullFibre_aut_preserves_ordinate σ q
    have he : σ (centeredZeroInFibreExtension q) = centeredZeroInFibreExtension r := Subtype.ext hr
    rw [he]
    exact AddSubgroup.subset_closure ⟨r,rfl⟩
  | zero =>
    rw [map_zero]
    exact zeroRelationGroup.zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact zeroRelationGroup.add_mem hx hy
  | neg x _ hx =>
    rw [map_neg]
    exact zeroRelationGroup.neg_mem hx

/-- Every source automorphism acts on the full integral relation group. -/
def zeroRelationAction
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    zeroRelationGroup ≃+ zeroRelationGroup where
  toFun z := ⟨σ z,zeroRelation_aut_mem σ z.property⟩
  invFun z := ⟨σ.symm z,zeroRelation_aut_mem σ.symm z.property⟩
  left_inv z := Subtype.ext (σ.symm_apply_apply z)
  right_inv z := Subtype.ext (σ.apply_symm_apply z)
  map_add' x y := Subtype.ext (map_add σ (x : fullFibreZeroExtension) (y : fullFibreZeroExtension))

/-- Conjugation of the centered zero motive. -/
def zeroRelationConjugation : zeroRelationGroup ≃+ zeroRelationGroup :=
  zeroRelationAction fullFibreZeroConjugation

/-- The ordinate projection on the integral zero motive. -/
def zeroRelationReal : zeroRelationGroup →+ ℝ :=
  Complex.reAddGroupHom.comp zeroRelationEmbedding

/-- The width projection on the integral zero motive. -/
def zeroRelationImag : zeroRelationGroup →+ ℝ :=
  Complex.imAddGroupHom.comp zeroRelationEmbedding

private theorem zeroRelationReal_conj (z : zeroRelationGroup) :
    zeroRelationReal (zeroRelationConjugation z) = zeroRelationReal z := rfl

private theorem zeroRelationImag_conj (z : zeroRelationGroup) :
    zeroRelationImag (zeroRelationConjugation z) = -zeroRelationImag z := rfl


/-- The entire source Galois group acts on the integral zero motive. -/
def zeroRelationRepresentation :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      Multiplicative (AddAut zeroRelationGroup) where
  toFun σ := Multiplicative.ofAdd (zeroRelationAction σ)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro z
    rfl
  map_mul' σ τ := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro z
    rfl

/-- Passing to the actual integral relation group loses no source automorphism. -/
theorem zeroRelationRepresentation_injective : Function.Injective zeroRelationRepresentation := by
  intro σ τ h
  have h' := congrArg Multiplicative.toAdd h
  have hzero (q : XiZeroCopy) :
      σ (centeredZeroInFibreExtension q) = τ (centeredZeroInFibreExtension q) :=
    congrArg (fun z : zeroRelationGroup => (z : fullFibreZeroExtension))
      (DFunLike.congr_fun h' (zeroRelationRoot q))
  have he := IntermediateField.algHom_ext_of_eq_adjoin fullFibreSourceField
    (S := fullFibreZeroExtension) rfl (φ₁ := σ.toAlgHom) (φ₂ := τ.toAlgHom)
    (by rintro _ ⟨q,rfl⟩; exact hzero q)
  apply AlgEquiv.ext
  intro z
  exact DFunLike.congr_fun he z

/-- Every arithmetic automorphism fixes the ordinate projection of every integral zero combination. -/
theorem zeroRelationReal_source_invariant
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (z : zeroRelationGroup) : zeroRelationReal (zeroRelationAction σ z) = zeroRelationReal z := by
  have hfix (x : fullFibreZeroExtension) (hx : x ∈ zeroRelationGroup) :
      ((σ x : fullFibreZeroExtension) : ℂ).re = (x : ℂ).re := by
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q,rfl⟩ := hx
      obtain ⟨r,hr,hσ⟩ := fullFibre_aut_preserves_ordinate σ q
      rw [hσ]
      exact (mem_ordinateFibreCopies (xiSpectralPoint q).re r).mp hr
    | zero => rw [map_zero]
    | add x y _ _ hx hy =>
      rw [map_add]
      change ((σ x : fullFibreZeroExtension) : ℂ).re+
        ((σ y : fullFibreZeroExtension) : ℂ).re = (x : ℂ).re+(y : ℂ).re
      rw [hx,hy]
    | neg x _ hx =>
      rw [map_neg]
      change -((σ x : fullFibreZeroExtension) : ℂ).re = -(x : ℂ).re
      rw [hx]
  exact hfix z z.property

/-- Integral combinations of zeros with zero imaginary part. -/
def zeroPureReal : AddSubgroup zeroRelationGroup := zeroRelationImag.ker

/-- Integral combinations of zeros with zero real part. -/
def zeroPureImaginary : AddSubgroup zeroRelationGroup := zeroRelationReal.ker

/-- Pure real and imaginary combinations have trivial intersection. -/
theorem zeroPureReal_inf_imaginary : zeroPureReal ⊓ zeroPureImaginary = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  change z = 0
  apply zeroRelationEmbedding_injective
  apply Complex.ext
  · exact hz.2
  · exact hz.1

/-- Twice every integral zero combination splits into pure real and imaginary combinations. -/
theorem zeroRelation_double_mem_axes (z : zeroRelationGroup) :
    (2 : ℕ) • z ∈ zeroPureReal ⊔ zeroPureImaginary := by
  have hr : z+zeroRelationConjugation z ∈ zeroPureReal := by
    change zeroRelationImag (z+zeroRelationConjugation z) = 0
    rw [map_add,zeroRelationImag_conj,add_neg_cancel]
  have hi : z-zeroRelationConjugation z ∈ zeroPureImaginary := by
    change zeroRelationReal (z-zeroRelationConjugation z) = 0
    rw [map_sub,zeroRelationReal_conj,sub_self]
  have he : (2 : ℕ) • z = (z+zeroRelationConjugation z)+(z-zeroRelationConjugation z) := by
    rw [two_nsmul]
    abel
  rw [he]
  have hR : zeroPureReal ≤ zeroPureReal ⊔ zeroPureImaginary := le_sup_left
  have hI : zeroPureImaginary ≤ zeroPureReal ⊔ zeroPureImaginary := le_sup_right
  exact (zeroPureReal ⊔ zeroPureImaginary).add_mem (hR hr) (hI hi)

/-- The exact integral obstruction to separating ordinate and width coordinates. -/
abbrev ZeroIntegralGluing := zeroRelationGroup ⧸ (zeroPureReal ⊔ zeroPureImaginary)

/-- The full integral gluing obstruction is killed by two. -/
theorem zeroIntegralGluing_two (x : ZeroIntegralGluing) : (2 : ℕ) • x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    change (2 : ℕ) • (QuotientAddGroup.mk' (zeroPureReal ⊔ zeroPureImaginary) z) = 0
    rw [← map_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr (zeroRelation_double_mem_axes z)

/-- The group of all integral ordinate combinations. -/
abbrev zeroOrdinateGroup : AddSubgroup ℝ := zeroRelationReal.range

/-- The group of all integral width combinations. -/
abbrev zeroWidthAdditiveGroup : AddSubgroup ℝ := zeroRelationImag.range

/-- The joint coordinate embedding, with each coordinate restricted to its actual image. -/
def zeroCoordinateMap : zeroRelationGroup →+ zeroOrdinateGroup × zeroWidthAdditiveGroup :=
  zeroRelationReal.rangeRestrict.prod zeroRelationImag.rangeRestrict

/-- Actual pairs of integral ordinate and width coordinates. -/
abbrev zeroCoordinateImage : AddSubgroup (zeroOrdinateGroup × zeroWidthAdditiveGroup) :=
  zeroCoordinateMap.range

theorem zeroCoordinateMap_injective : Function.Injective zeroCoordinateMap := by
  intro z w h
  apply zeroRelationEmbedding_injective
  apply Complex.ext
  · exact congrArg (fun p : zeroOrdinateGroup × zeroWidthAdditiveGroup => (p.1 : ℝ)) h
  · exact congrArg (fun p : zeroOrdinateGroup × zeroWidthAdditiveGroup => (p.2 : ℝ)) h

private theorem zeroCoordinateImage_fst_surjective :
    Function.Surjective (Prod.fst ∘ zeroCoordinateImage.subtype) := by
  intro t
  obtain ⟨z,hz⟩ := t.property
  refine ⟨⟨zeroCoordinateMap z,⟨z,rfl⟩⟩,?_⟩
  exact Subtype.ext hz

private theorem zeroCoordinateImage_snd_surjective :
    Function.Surjective (Prod.snd ∘ zeroCoordinateImage.subtype) := by
  intro b
  obtain ⟨z,hz⟩ := b.property
  refine ⟨⟨zeroCoordinateMap z,⟨z,rfl⟩⟩,?_⟩
  exact Subtype.ext hz

/-- Ordinate combinations which occur with zero width. -/
abbrev pureOrdinateGroup : AddSubgroup zeroOrdinateGroup := zeroCoordinateImage.goursatFst

/-- Width combinations which occur with zero ordinate. -/
abbrev pureWidthGroup : AddSubgroup zeroWidthAdditiveGroup := zeroCoordinateImage.goursatSnd

/-- The two coordinate quotients are canonically matched by the full zero relation group. -/
def zeroCoordinateGluing :
    (zeroOrdinateGroup ⧸ pureOrdinateGroup) ≃+ (zeroWidthAdditiveGroup ⧸ pureWidthGroup) :=
  Classical.choose (AddSubgroup.goursat_surjective zeroCoordinateImage_fst_surjective
    zeroCoordinateImage_snd_surjective)

private theorem zeroCoordinateGluing_graph :
    (((QuotientAddGroup.mk' pureOrdinateGroup).prodMap (QuotientAddGroup.mk' pureWidthGroup)).comp
      zeroCoordinateImage.subtype).range = zeroCoordinateGluing.toAddMonoidHom.graph :=
  Classical.choose_spec (AddSubgroup.goursat_surjective zeroCoordinateImage_fst_surjective
    zeroCoordinateImage_snd_surjective)

private theorem subgroup_mem_iff_gluing {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (H : AddSubgroup (A × B))
    (e : (A ⧸ H.goursatFst) ≃+ (B ⧸ H.goursatSnd))
    (he : (((QuotientAddGroup.mk' H.goursatFst).prodMap
      (QuotientAddGroup.mk' H.goursatSnd)).comp H.subtype).range = e.toAddMonoidHom.graph)
    (t : A) (b : B) :
    (t,b) ∈ H ↔ e (QuotientAddGroup.mk' H.goursatFst t) =
      QuotientAddGroup.mk' H.goursatSnd b := by
  constructor
  · intro h
    change (QuotientAddGroup.mk' H.goursatFst t,
      QuotientAddGroup.mk' H.goursatSnd b) ∈ e.toAddMonoidHom.graph
    rw [← he]
    exact ⟨⟨(t,b),h⟩,rfl⟩
  · intro h
    have hh : (QuotientAddGroup.mk' H.goursatFst t,
        QuotientAddGroup.mk' H.goursatSnd b) ∈ e.toAddMonoidHom.graph := h
    rw [← he] at hh
    obtain ⟨⟨⟨u,v⟩,huv⟩,hpair⟩ := hh
    have ht : t-u ∈ H.goursatFst := QuotientAddGroup.eq_iff_sub_mem.mp
      (congrArg Prod.fst hpair).symm
    have hb : b-v ∈ H.goursatSnd := QuotientAddGroup.eq_iff_sub_mem.mp
      (congrArg Prod.snd hpair).symm
    have hpure : (t-u,b-v) ∈ H := H.goursatFst_prod_goursatSnd_le ⟨ht,hb⟩
    have hs := H.add_mem huv hpure
    have hp : (u,v)+(t-u,b-v) = (t,b) := by ext <;> dsimp <;> abel
    rwa [hp] at hs

/-- Exact integral reconstruction: a pair of coordinates is realized precisely when its gluing classes agree. -/
theorem zeroRelationGroup_full_gluing (t : zeroOrdinateGroup) (b : zeroWidthAdditiveGroup) :
    (t,b) ∈ zeroCoordinateImage ↔
      zeroCoordinateGluing (QuotientAddGroup.mk' pureOrdinateGroup t) =
        QuotientAddGroup.mk' pureWidthGroup b :=
  subgroup_mem_iff_gluing zeroCoordinateImage zeroCoordinateGluing zeroCoordinateGluing_graph t b

private theorem doubled_ordinate_pure (t : zeroOrdinateGroup) :
    (2 : ℕ) • t ∈ pureOrdinateGroup := by
  apply AddSubgroup.mem_goursatFst.mpr
  obtain ⟨z,hz⟩ := t.property
  refine ⟨z+zeroRelationConjugation z,?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change zeroRelationReal (z+zeroRelationConjugation z) = (2 : ℕ) • (t : ℝ)
    rw [map_add,zeroRelationReal_conj,hz,two_nsmul]
  · apply Subtype.ext
    change zeroRelationImag (z+zeroRelationConjugation z) = 0
    rw [map_add,zeroRelationImag_conj,add_neg_cancel]

private theorem doubled_width_pure (b : zeroWidthAdditiveGroup) :
    (2 : ℕ) • b ∈ pureWidthGroup := by
  apply AddSubgroup.mem_goursatSnd.mpr
  obtain ⟨z,hz⟩ := b.property
  refine ⟨z-zeroRelationConjugation z,?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change zeroRelationReal (z-zeroRelationConjugation z) = 0
    rw [map_sub,zeroRelationReal_conj,sub_self]
  · apply Subtype.ext
    change zeroRelationImag (z-zeroRelationConjugation z) = (2 : ℕ) • (b : ℝ)
    rw [map_sub,zeroRelationImag_conj,hz,sub_neg_eq_add,two_nsmul]

/-- Each coordinate quotient is an elementary two-group, even for the infinite divisor. -/
theorem zeroOrdinateGluing_two (x : zeroOrdinateGroup ⧸ pureOrdinateGroup) :
    (2 : ℕ) • x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    change (2 : ℕ) • (QuotientAddGroup.mk' pureOrdinateGroup t) = 0
    rw [← map_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr (doubled_ordinate_pure t)

/-- Every doubled pair of actual coordinate combinations belongs to the zero relation group. -/
theorem zeroCoordinate_double_mem_image (p : zeroOrdinateGroup × zeroWidthAdditiveGroup) :
    (2 : ℕ) • p ∈ zeroCoordinateImage :=
  zeroCoordinateImage.goursatFst_prod_goursatSnd_le
    ⟨doubled_ordinate_pure p.1,doubled_width_pure p.2⟩

/-- The common gluing class of an integral combination of zeros. -/
def zeroGluingProjection : zeroRelationGroup →+ (zeroOrdinateGroup ⧸ pureOrdinateGroup) :=
  (QuotientAddGroup.mk' pureOrdinateGroup).comp zeroRelationReal.rangeRestrict

private theorem zeroGluingProjection_real (z : zeroRelationGroup) (hz : z ∈ zeroPureReal) :
    zeroGluingProjection z = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.mem_goursatFst.mpr
  refine ⟨z,?_⟩
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact hz

private theorem zeroGluingProjection_imaginary (z : zeroRelationGroup)
    (hz : z ∈ zeroPureImaginary) : zeroGluingProjection z = 0 := by
  have he : zeroRelationReal.rangeRestrict z = 0 := Subtype.ext hz
  change QuotientAddGroup.mk' pureOrdinateGroup (zeroRelationReal.rangeRestrict z) = 0
  rw [he,map_zero]

/-- The kernel of either coordinate gluing map is exactly the sum of the two pure subgroups. -/
theorem zeroGluingProjection_ker :
    zeroGluingProjection.ker = zeroPureReal ⊔ zeroPureImaginary := by
  apply le_antisymm
  · intro z hz
    have ht : zeroRelationReal.rangeRestrict z ∈ pureOrdinateGroup :=
      (QuotientAddGroup.eq_zero_iff _).mp hz
    obtain ⟨w,hw⟩ := AddSubgroup.mem_goursatFst.mp ht
    have hre : zeroRelationReal w = zeroRelationReal z :=
      congrArg (fun p : zeroOrdinateGroup × zeroWidthAdditiveGroup => (p.1 : ℝ)) hw
    have him : zeroRelationImag w = 0 :=
      congrArg (fun p : zeroOrdinateGroup × zeroWidthAdditiveGroup => (p.2 : ℝ)) hw
    apply AddSubgroup.mem_sup.mpr
    refine ⟨w,him,z-w,?_,?_⟩
    · change zeroRelationReal (z-w) = 0
      rw [map_sub,hre,sub_self]
    · abel
  · apply sup_le
    · intro z hz
      exact zeroGluingProjection_real z hz
    · intro z hz
      exact zeroGluingProjection_imaginary z hz

private theorem zeroGluingProjection_surjective : Function.Surjective zeroGluingProjection := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    obtain ⟨z,hz⟩ := t.property
    refine ⟨z,?_⟩
    change QuotientAddGroup.mk' pureOrdinateGroup (zeroRelationReal.rangeRestrict z) =
      QuotientAddGroup.mk' pureOrdinateGroup t
    exact congrArg (QuotientAddGroup.mk' pureOrdinateGroup) (Subtype.ext hz)

/-- The intrinsic integral gluing quotient is the quotient seen by ordinate projection. -/
def zeroIntegralGluingEquiv : ZeroIntegralGluing ≃+ (zeroOrdinateGroup ⧸ pureOrdinateGroup) :=
  (QuotientAddGroup.quotientAddEquivOfEq zeroGluingProjection_ker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective zeroGluingProjection zeroGluingProjection_surjective)

/-- The same intrinsic quotient is seen by the width projection. -/
def zeroIntegralWidthGluingEquiv : ZeroIntegralGluing ≃+ (zeroWidthAdditiveGroup ⧸ pureWidthGroup) :=
  zeroIntegralGluingEquiv.trans zeroCoordinateGluing

/-- Complex points of the centered zero motive: multiplicative characters of its integral relation group. -/
abbrev ZeroMotivePoint := zeroRelationGroup →+ Additive ℂˣ

/-- Restriction from the ordinate and width character groups to the actual centered zero motive. -/
def zeroMotiveRestriction :
    ((zeroOrdinateGroup →+ Additive ℂˣ) × (zeroWidthAdditiveGroup →+ Additive ℂˣ)) →+ ZeroMotivePoint where
  toFun χ := χ.1.comp zeroRelationReal.rangeRestrict + χ.2.comp zeroRelationImag.rangeRestrict
  map_zero' := by
    apply AddMonoidHom.ext
    intro z
    change (0 : Additive ℂˣ)+0 = 0
    exact zero_add 0
  map_add' χ ψ := by
    apply AddMonoidHom.ext
    intro z
    change (χ.1 (zeroRelationReal.rangeRestrict z)+ψ.1 (zeroRelationReal.rangeRestrict z))+
      (χ.2 (zeroRelationImag.rangeRestrict z)+ψ.2 (zeroRelationImag.rangeRestrict z)) =
      (χ.1 (zeroRelationReal.rangeRestrict z)+χ.2 (zeroRelationImag.rangeRestrict z))+
      (ψ.1 (zeroRelationReal.rangeRestrict z)+ψ.2 (zeroRelationImag.rangeRestrict z))
    abel

/-- Every complex point of the infinite centered zero motive lifts to a pair of coordinate characters. -/
theorem zeroMotiveRestriction_surjective : Function.Surjective zeroMotiveRestriction := by
  intro χ
  letI := deningerDivisibleByInt ℂˣ
  obtain ⟨F,hF⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    zeroCoordinateMap zeroCoordinateMap_injective χ
  let f : zeroOrdinateGroup →+ Additive ℂˣ :=
    { toFun := fun t => F (t,0)
      map_zero' := map_zero F
      map_add' := fun t u => by simpa only [Prod.mk_add_mk,add_zero] using map_add F (t,0) (u,0) }
  let g : zeroWidthAdditiveGroup →+ Additive ℂˣ :=
    { toFun := fun b => F (0,b)
      map_zero' := map_zero F
      map_add' := fun b c => by simpa only [Prod.mk_add_mk,add_zero] using map_add F (0,b) (0,c) }
  refine ⟨(f,g),?_⟩
  apply AddMonoidHom.ext
  intro z
  change F (zeroRelationReal.rangeRestrict z,0)+F (0,zeroRelationImag.rangeRestrict z) = χ z
  rw [← map_add]
  simpa only [AddMonoidHom.comp_apply,zeroCoordinateMap,AddMonoidHom.prod_apply,
    Prod.mk_add_mk,add_zero,zero_add] using DFunLike.congr_fun hF z

/-- Two-torsion is the only ambiguity in extending characters to both coordinates. -/
theorem zeroMotiveRestriction_kernel_two
    (χ : (zeroOrdinateGroup →+ Additive ℂˣ) × (zeroWidthAdditiveGroup →+ Additive ℂˣ))
    (hχ : zeroMotiveRestriction χ = 0) : (2 : ℕ) • χ = 0 := by
  have hpair (t : zeroOrdinateGroup) (b : zeroWidthAdditiveGroup)
      (h : (t,b) ∈ zeroCoordinateImage) : χ.1 t+χ.2 b = 0 := by
    obtain ⟨z,hz⟩ := h
    have he := DFunLike.congr_fun hχ z
    change χ.1 (zeroCoordinateMap z).1+χ.2 (zeroCoordinateMap z).2 = 0 at he
    rwa [hz] at he
  rw [two_nsmul]
  apply Prod.ext
  · apply AddMonoidHom.ext
    intro t
    change χ.1 t+χ.1 t = 0
    have he := hpair ((2 : ℕ) • t) 0 (AddSubgroup.mem_goursatFst.mp (doubled_ordinate_pure t))
    simpa only [map_nsmul,map_zero,add_zero,two_nsmul,map_add] using he
  · apply AddMonoidHom.ext
    intro b
    change χ.2 b+χ.2 b = 0
    have he := hpair 0 ((2 : ℕ) • b) (AddSubgroup.mem_goursatSnd.mp (doubled_width_pure b))
    simpa only [map_nsmul,map_zero,zero_add,two_nsmul,map_add] using he

/-- The extension ambiguity consists exactly of opposite characters of the common gluing quotient. -/
theorem zeroMotiveRestriction_kernel_iff
    (χ : (zeroOrdinateGroup →+ Additive ℂˣ) × (zeroWidthAdditiveGroup →+ Additive ℂˣ)) :
    zeroMotiveRestriction χ = 0 ↔
      ∃! η : (zeroOrdinateGroup ⧸ pureOrdinateGroup) →+ Additive ℂˣ,
        χ.1 = η.comp (QuotientAddGroup.mk' pureOrdinateGroup) ∧
        χ.2 = -((η.comp zeroCoordinateGluing.symm.toAddMonoidHom).comp
          (QuotientAddGroup.mk' pureWidthGroup)) := by
  constructor
  · intro h
    have hT : pureOrdinateGroup ≤ χ.1.ker := by
      intro t ht
      obtain ⟨z,hz⟩ := AddSubgroup.mem_goursatFst.mp ht
      have he := DFunLike.congr_fun h z
      change χ.1 (zeroCoordinateMap z).1+χ.2 (zeroCoordinateMap z).2 = 0 at he
      rw [hz,map_zero,add_zero] at he
      exact he
    let η := QuotientAddGroup.lift pureOrdinateGroup χ.1 hT
    refine ⟨η,⟨rfl,?_⟩,?_⟩
    · apply AddMonoidHom.ext
      intro b
      obtain ⟨z,hz⟩ := b.property
      have hb : zeroRelationImag.rangeRestrict z = b := Subtype.ext hz
      have hglue := (zeroRelationGroup_full_gluing
        (zeroRelationReal.rangeRestrict z) (zeroRelationImag.rangeRestrict z)).mp ⟨z,rfl⟩
      rw [hb] at hglue
      have he := DFunLike.congr_fun h z
      change χ.1 (zeroRelationReal.rangeRestrict z)+χ.2 (zeroRelationImag.rangeRestrict z) = 0 at he
      rw [hb] at he
      change χ.2 b = -η (zeroCoordinateGluing.symm (QuotientAddGroup.mk' pureWidthGroup b))
      rw [← hglue,zeroCoordinateGluing.symm_apply_apply]
      change χ.2 b = -χ.1 (zeroRelationReal.rangeRestrict z)
      exact eq_neg_of_add_eq_zero_right he
    · intro θ hθ
      apply AddMonoidHom.ext
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H t =>
        have ht := DFunLike.congr_fun hθ.1 t
        change χ.1 t = θ (QuotientAddGroup.mk' pureOrdinateGroup t) at ht
        exact ht.symm
  · rintro ⟨η,⟨hT,hB⟩,_⟩
    apply AddMonoidHom.ext
    intro z
    have hglue := (zeroRelationGroup_full_gluing
      (zeroRelationReal.rangeRestrict z) (zeroRelationImag.rangeRestrict z)).mp ⟨z,rfl⟩
    change χ.1 (zeroRelationReal.rangeRestrict z)+χ.2 (zeroRelationImag.rangeRestrict z) = 0
    rw [hT,hB]
    change η (QuotientAddGroup.mk' pureOrdinateGroup (zeroRelationReal.rangeRestrict z))+
      -η (zeroCoordinateGluing.symm
        (QuotientAddGroup.mk' pureWidthGroup (zeroRelationImag.rangeRestrict z))) = 0
    rw [← hglue,zeroCoordinateGluing.symm_apply_apply,add_neg_cancel]

/-- Conjugation fixes the ordinate character factor and inverts the width character factor. -/
theorem zeroMotiveRestriction_conjugation
    (χ : (zeroOrdinateGroup →+ Additive ℂˣ) × (zeroWidthAdditiveGroup →+ Additive ℂˣ)) :
    (zeroMotiveRestriction χ).comp zeroRelationConjugation.toAddMonoidHom =
      zeroMotiveRestriction (χ.1,-χ.2) := by
  apply AddMonoidHom.ext
  intro z
  have hr : zeroRelationReal.rangeRestrict (zeroRelationConjugation z) =
      zeroRelationReal.rangeRestrict z := Subtype.ext (zeroRelationReal_conj z)
  have hi : zeroRelationImag.rangeRestrict (zeroRelationConjugation z) =
      -zeroRelationImag.rangeRestrict z := Subtype.ext (zeroRelationImag_conj z)
  change χ.1 (zeroRelationReal.rangeRestrict (zeroRelationConjugation z))+
      χ.2 (zeroRelationImag.rangeRestrict (zeroRelationConjugation z)) =
    χ.1 (zeroRelationReal.rangeRestrict z)+ -χ.2 (zeroRelationImag.rangeRestrict z)
  rw [hr,hi,map_neg]

private def complexScalarMap (a : ℂ) : ℂ →+ ℂ where
  toFun z := a*z
  map_zero' := mul_zero a
  map_add' x y := mul_add a x y

private def complexExponentialCharacter {A : Type*} [AddGroup A]
    (f : A →+ ℂ) : A →+ Additive ℂˣ where
  toFun z := Additive.ofMul (Units.mk0 (Complex.exp (f z)) (Complex.exp_ne_zero (f z)))
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    change Complex.exp (f 0) = 1
    rw [map_zero,Complex.exp_zero]
  map_add' x y := by
    apply Additive.toMul.injective
    apply Units.ext
    change Complex.exp (f (x+y)) = Complex.exp (f x)*Complex.exp (f y)
    rw [map_add,Complex.exp_add]

/-- The normalized exponential flow on the whole zero motive; prime time is `u=log p`. -/
def zeroMotiveFlow : ℝ →+ ZeroMotivePoint where
  toFun u := complexExponentialCharacter ((complexScalarMap (I*(u : ℂ))).comp zeroRelationEmbedding)
  map_zero' := by
    apply AddMonoidHom.ext
    intro z
    apply Additive.toMul.injective
    apply Units.ext
    change Complex.exp (I*((0 : ℝ) : ℂ)*zeroRelationEmbedding z) = 1
    simp only [Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero]
  map_add' u v := by
    apply AddMonoidHom.ext
    intro z
    apply Additive.toMul.injective
    apply Units.ext
    change Complex.exp (I*((u+v : ℝ) : ℂ)*zeroRelationEmbedding z) =
      Complex.exp (I*(u : ℂ)*zeroRelationEmbedding z)*Complex.exp (I*(v : ℂ)*zeroRelationEmbedding z)
    rw [Complex.ofReal_add,mul_add,add_mul,Complex.exp_add]

/-- The ordinate factor of the normalized flow. -/
def zeroOrdinateFlow (u : ℝ) : zeroOrdinateGroup →+ Additive ℂˣ :=
  complexExponentialCharacter ((complexScalarMap (I*(u : ℂ))).comp
    ((algebraMap ℝ ℂ).toAddMonoidHom.comp zeroOrdinateGroup.subtype))

/-- The real exponential width factor of the normalized flow. -/
def zeroWidthFlow (u : ℝ) : zeroWidthAdditiveGroup →+ Additive ℂˣ :=
  complexExponentialCharacter ((complexScalarMap (-(u : ℂ))).comp
    ((algebraMap ℝ ℂ).toAddMonoidHom.comp zeroWidthAdditiveGroup.subtype))

/-- The normalized flow has a canonical coordinate lift despite possible integral gluing. -/
theorem zeroMotiveFlow_coordinate_lift (u : ℝ) :
    zeroMotiveRestriction (zeroOrdinateFlow u,zeroWidthFlow u) = zeroMotiveFlow u := by
  apply AddMonoidHom.ext
  intro z
  apply Additive.toMul.injective
  apply Units.ext
  change Complex.exp (I*(u : ℂ)*(zeroRelationReal z : ℂ))*
    Complex.exp (-(u : ℂ)*(zeroRelationImag z : ℂ)) =
      Complex.exp (I*(u : ℂ)*zeroRelationEmbedding z)
  rw [← Complex.exp_add]
  congr 1
  have he : zeroRelationEmbedding z = (zeroRelationReal z : ℂ)+(zeroRelationImag z : ℂ)*I :=
    (Complex.re_add_im (zeroRelationEmbedding z)).symm
  rw [he]
  symm
  calc
    I*(u : ℂ)*((zeroRelationReal z : ℂ)+(zeroRelationImag z : ℂ)*I) =
        I*(u : ℂ)*(zeroRelationReal z : ℂ)+((u : ℂ)*(zeroRelationImag z : ℂ))*(I*I) := by ring
    _ = I*(u : ℂ)*(zeroRelationReal z : ℂ)+ -(u : ℂ)*(zeroRelationImag z : ℂ) := by
      rw [I_mul_I]
      ring

/-- On each actual zero the flow is the original exponential with its central weight removed. -/
theorem zeroMotiveFlow_at_zero (u : ℝ) (q : XiZeroCopy) :
    ((zeroMotiveFlow u (zeroRelationRoot q)).toMul : ℂ) =
      Complex.exp ((u : ℂ)*((q.1 : ℂ)-1/2)) := by
  change Complex.exp (I*(u : ℂ)*xiSpectralPoint q) = _
  congr 1
  unfold xiSpectralPoint
  calc
    I*(u : ℂ)*(((q.1 : ℂ)-1/2)*(-I)) =
        (u : ℂ)*((q.1 : ℂ)-1/2)*(-(I*I)) := by ring
    _ = (u : ℂ)*((q.1 : ℂ)-1/2) := by rw [I_mul_I,neg_neg,mul_one]

/-- The integer span of the original zeros, before centering or division by `i`. -/
def rawZeroRelationGroup : AddSubgroup ℂ :=
  AddSubgroup.closure (Set.range fun q : XiZeroCopy => (q.1 : ℂ))

/-- An original zero as a generator of its integral relation group. -/
def rawZeroRelationRoot (q : XiZeroCopy) : rawZeroRelationGroup :=
  ⟨(q.1 : ℂ),AddSubgroup.subset_closure ⟨q,rfl⟩⟩

/-- Functional-equation pairing puts the central unit in the original integral relation group. -/
theorem one_mem_rawZeroRelationGroup : (1 : ℂ) ∈ rawZeroRelationGroup := by
  obtain ⟨ρ,hρ⟩ := xiDivisorSupport_infinite.nonempty
  let q : XiZeroCopy := ⟨⟨ρ,hρ⟩,⟨0,by
    have hp := xi_divisor_pos_on_support ⟨ρ,hρ⟩
    omega⟩⟩
  have hq : (q.1 : ℂ) ∈ rawZeroRelationGroup := (rawZeroRelationRoot q).property
  have hr : ((xiZeroCopyReflectEquiv q).1 : ℂ) ∈ rawZeroRelationGroup :=
    (rawZeroRelationRoot (xiZeroCopyReflectEquiv q)).property
  have he : (q.1 : ℂ)+((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 := by
    change (q.1 : ℂ)+(1-(q.1 : ℂ)) = 1
    ring
  exact he ▸ rawZeroRelationGroup.add_mem hq hr

/-- Restoring the central half-weight to the original zero relation group. -/
def halfWeightedZeroGroup : AddSubgroup ℂ :=
  rawZeroRelationGroup ⊔ AddSubgroup.zmultiples (1/2 : ℂ)

private theorem rawZero_le_halfWeighted : rawZeroRelationGroup ≤ halfWeightedZeroGroup := le_sup_left
private theorem halves_le_halfWeighted : AddSubgroup.zmultiples (1/2 : ℂ) ≤ halfWeightedZeroGroup := le_sup_right

/-- Inclusion of the original integral zero motive into its half-weight extension. -/
def rawZeroInclusion : rawZeroRelationGroup →+ halfWeightedZeroGroup where
  toFun z := ⟨z,rawZero_le_halfWeighted z.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem rawZeroInclusion_injective : Function.Injective rawZeroInclusion := by
  intro z w h
  exact Subtype.ext (congrArg (fun x : halfWeightedZeroGroup => (x : ℂ)) h)

/-- The central half-weight. -/
def halfWeight : halfWeightedZeroGroup :=
  ⟨1/2,halves_le_halfWeighted (AddSubgroup.mem_zmultiples _)⟩

private theorem centered_original_identity (q : XiZeroCopy) :
    I*xiSpectralPoint q = (q.1 : ℂ)-1/2 := by
  unfold xiSpectralPoint
  calc
    I*(((q.1 : ℂ)-1/2)*(-I)) = ((q.1 : ℂ)-1/2)*(-(I*I)) := by ring
    _ = (q.1 : ℂ)-1/2 := by rw [I_mul_I,neg_neg,mul_one]

/-- Rotation back from spectral coordinates to centered original-zero coordinates. -/
def centeredRelationRotation : zeroRelationGroup →+ ℂ :=
  (complexScalarMap I).comp zeroRelationEmbedding

private theorem centeredRotation_mem_halfWeighted (z : zeroRelationGroup) :
    centeredRelationRotation z ∈ halfWeightedZeroGroup := by
  have hm (x : fullFibreZeroExtension) (hx : x ∈ zeroRelationGroup) :
      I*(x : ℂ) ∈ halfWeightedZeroGroup := by
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q,rfl⟩ := hx
      change I*xiSpectralPoint q ∈ halfWeightedZeroGroup
      rw [centered_original_identity]
      exact halfWeightedZeroGroup.sub_mem
        (rawZero_le_halfWeighted (rawZeroRelationRoot q).property) halfWeight.property
    | zero =>
      change I*(0 : ℂ) ∈ halfWeightedZeroGroup
      rw [mul_zero]
      exact halfWeightedZeroGroup.zero_mem
    | add x y _ _ hx hy =>
      change I*((x : ℂ)+(y : ℂ)) ∈ halfWeightedZeroGroup
      rw [mul_add]
      exact halfWeightedZeroGroup.add_mem hx hy
    | neg x _ hx =>
      change I*(-(x : ℂ)) ∈ halfWeightedZeroGroup
      rw [mul_neg]
      exact halfWeightedZeroGroup.neg_mem hx
  exact hm z z.property

/-- The centered relation group maps into the half-weight extension. -/
def centeredZeroInclusion : zeroRelationGroup →+ halfWeightedZeroGroup where
  toFun z := ⟨centeredRelationRotation z,centeredRotation_mem_halfWeighted z⟩
  map_zero' := Subtype.ext (map_zero centeredRelationRotation)
  map_add' z w := Subtype.ext (map_add centeredRelationRotation z w)

/-- Centering becomes exact after the central half-weight is restored. -/
theorem halfWeightedZeroGroup_eq :
    halfWeightedZeroGroup = AddSubgroup.zmultiples (1/2 : ℂ) ⊔ centeredRelationRotation.range := by
  apply le_antisymm
  · apply sup_le
    · apply (AddSubgroup.closure_le _).mpr
      rintro _ ⟨q,rfl⟩
      change (q.1 : ℂ) ∈ AddSubgroup.zmultiples (1/2 : ℂ) ⊔ centeredRelationRotation.range
      have hh : (1/2 : ℂ) ∈ AddSubgroup.zmultiples (1/2 : ℂ) ⊔ centeredRelationRotation.range :=
        (show AddSubgroup.zmultiples (1/2 : ℂ) ≤ _ from le_sup_left) (AddSubgroup.mem_zmultiples _)
      have hb : I*xiSpectralPoint q ∈ AddSubgroup.zmultiples (1/2 : ℂ) ⊔ centeredRelationRotation.range :=
        (show centeredRelationRotation.range ≤ _ from le_sup_right) ⟨zeroRelationRoot q,rfl⟩
      have he : (q.1 : ℂ) = 1/2+I*xiSpectralPoint q := by rw [centered_original_identity]; ring
      rw [he]
      exact (AddSubgroup.zmultiples (1/2 : ℂ) ⊔ centeredRelationRotation.range).add_mem hh hb
    · exact le_sup_left
  · apply sup_le halves_le_halfWeighted
    rintro _ ⟨z,rfl⟩
    exact centeredRotation_mem_halfWeighted z

/-- The original generators are exactly central half-weight plus rotated centered generators. -/
theorem rawZeroInclusion_root (q : XiZeroCopy) :
    rawZeroInclusion (rawZeroRelationRoot q) = halfWeight+centeredZeroInclusion (zeroRelationRoot q) := by
  apply Subtype.ext
  change (q.1 : ℂ) = 1/2+I*xiSpectralPoint q
  rw [centered_original_identity]
  ring

/-- The original integral subgroup inside the half-weight extension. -/
abbrev rawZeroInsideHalfWeighted : AddSubgroup halfWeightedZeroGroup :=
  rawZeroRelationGroup.comap halfWeightedZeroGroup.subtype

/-- The sole possible central obstruction to removing the half-weight. -/
abbrev RawCentralGluing := halfWeightedZeroGroup ⧸ rawZeroInsideHalfWeighted

/-- The class of the half-weight generates the entire central gluing group. -/
theorem rawCentralGluing_cyclic (x : RawCentralGluing) :
    ∃ n : ℤ, x = n • (QuotientAddGroup.mk' rawZeroInsideHalfWeighted halfWeight) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    obtain ⟨r,hr,h,hh,he⟩ := AddSubgroup.mem_sup.mp z.property
    obtain ⟨n,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hh
    refine ⟨n,?_⟩
    rw [← map_zsmul]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change (z : ℂ)-n • (1/2 : ℂ) ∈ rawZeroRelationGroup
    rw [← he]
    simpa only [add_sub_cancel_right] using hr

/-- The half-weight is an element of order at most two modulo original zeros. -/
theorem rawCentralGluing_half_two :
    (2 : ℕ) • (QuotientAddGroup.mk' rawZeroInsideHalfWeighted halfWeight) = 0 := by
  rw [← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  change (2 : ℕ) • (1/2 : ℂ) ∈ rawZeroRelationGroup
  have he : (2 : ℕ) • (1/2 : ℂ) = 1 := by norm_num
  rw [he]
  exact one_mem_rawZeroRelationGroup

/-- The central quotient is cyclic and killed by two; it need not be assumed trivial. -/
theorem rawCentralGluing_two (x : RawCentralGluing) : (2 : ℕ) • x = 0 := by
  obtain ⟨n,hn⟩ := rawCentralGluing_cyclic x
  rw [hn,two_nsmul,← zsmul_add,← two_nsmul,rawCentralGluing_half_two,zsmul_zero]

/-- Complex points of the original, uncentered zero motive. -/
abbrev RawZeroMotivePoint := rawZeroRelationGroup →+ Additive ℂˣ

/-- Complex points after restoring the central half-weight. -/
abbrev HalfWeightedZeroMotivePoint := halfWeightedZeroGroup →+ Additive ℂˣ

/-- Forgetting the central half-weight restricts a character to the original zeros. -/
def rawMotiveRestriction : HalfWeightedZeroMotivePoint →+ RawZeroMotivePoint where
  toFun χ := χ.comp rawZeroInclusion
  map_zero' := by apply AddMonoidHom.ext; intro z; rfl
  map_add' χ ψ := by apply AddMonoidHom.ext; intro z; rfl

/-- Every original-zero character admits a half-weight extension. -/
theorem rawMotiveRestriction_surjective : Function.Surjective rawMotiveRestriction := by
  intro χ
  letI := deningerDivisibleByInt ℂˣ
  exact (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    rawZeroInclusion rawZeroInclusion_injective χ

/-- A half-weight extension is determined by its original character and its central half-weight value. -/
theorem rawMotive_extension_unique_from_half (χ ψ : HalfWeightedZeroMotivePoint)
    (hraw : rawMotiveRestriction χ = rawMotiveRestriction ψ)
    (hhalf : χ halfWeight = ψ halfWeight) : χ = ψ := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨r,hr,h,hh,he⟩ := AddSubgroup.mem_sup.mp z.property
  obtain ⟨n,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hh
  have hz : z = rawZeroInclusion ⟨r,hr⟩+n • halfWeight := Subtype.ext he.symm
  have hχr := DFunLike.congr_fun hraw ⟨r,hr⟩
  change χ (rawZeroInclusion ⟨r,hr⟩) = ψ (rawZeroInclusion ⟨r,hr⟩) at hχr
  rw [hz]
  simp only [map_add,map_zsmul,hχr,hhalf]

/-- The central half-weight value is a square root of the original unit-weight value. -/
theorem rawMotive_half_square (χ : HalfWeightedZeroMotivePoint) :
    (χ halfWeight).toMul^2 =
      ((rawMotiveRestriction χ) ⟨1,one_mem_rawZeroRelationGroup⟩).toMul := by
  have hd : (2 : ℕ) • halfWeight = rawZeroInclusion ⟨1,one_mem_rawZeroRelationGroup⟩ := by
    apply Subtype.ext
    change (2 : ℕ) • (1/2 : ℂ) = 1
    norm_num
  have he := congrArg χ hd
  rw [map_nsmul,two_nsmul] at he
  have hm := congrArg Additive.toMul he
  change (χ halfWeight).toMul*(χ halfWeight).toMul = _ at hm
  have hr : (rawMotiveRestriction χ) ⟨1,one_mem_rawZeroRelationGroup⟩ =
      χ (rawZeroInclusion ⟨1,one_mem_rawZeroRelationGroup⟩) := rfl
  rw [hr,pow_two]
  exact hm

/-- A character trivial on original zeros has only a sign left at the central half-weight. -/
theorem rawMotiveRestriction_kernel_sign (χ : HalfWeightedZeroMotivePoint)
    (hχ : rawMotiveRestriction χ = 0) :
    (χ halfWeight).toMul = 1 ∨ (χ halfWeight).toMul = -1 := by
  have hs := rawMotive_half_square χ
  rw [hχ] at hs
  have hc := congrArg (fun u : ℂˣ => (u : ℂ)) hs
  have he : ((χ halfWeight).toMul : ℂ)^2 = (1 : ℂ)^2 := by
    simpa using hc
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

/-- Every original-zero character factors on generators into a central value and coordinate characters. -/
theorem rawMotive_coordinate_factorization (χ : RawZeroMotivePoint) :
    ∃ h : Additive ℂˣ,
      ∃ ψ : (zeroOrdinateGroup →+ Additive ℂˣ) × (zeroWidthAdditiveGroup →+ Additive ℂˣ),
        ∀ q : XiZeroCopy, χ (rawZeroRelationRoot q) =
          h+ψ.1 (zeroRelationReal.rangeRestrict (zeroRelationRoot q))+
            ψ.2 (zeroRelationImag.rangeRestrict (zeroRelationRoot q)) := by
  obtain ⟨α,hα⟩ := rawMotiveRestriction_surjective χ
  obtain ⟨ψ,hψ⟩ := zeroMotiveRestriction_surjective (α.comp centeredZeroInclusion)
  refine ⟨α halfWeight,ψ,?_⟩
  intro q
  have hroot := DFunLike.congr_fun hα (rawZeroRelationRoot q)
  have hcenter := DFunLike.congr_fun hψ (zeroRelationRoot q)
  change ψ.1 (zeroRelationReal.rangeRestrict (zeroRelationRoot q))+
    ψ.2 (zeroRelationImag.rangeRestrict (zeroRelationRoot q)) =
      α (centeredZeroInclusion (zeroRelationRoot q)) at hcenter
  rw [← hroot]
  change α (rawZeroInclusion (rawZeroRelationRoot q)) = _
  rw [rawZeroInclusion_root,map_add,← hcenter,add_assoc]

/-- The ordinary exponential flow on the original integral zero motive. -/
def rawZeroMotiveFlow (u : ℝ) : RawZeroMotivePoint :=
  complexExponentialCharacter ((complexScalarMap (u : ℂ)).comp rawZeroRelationGroup.subtype)

/-- Its canonical lift to the half-weight extension. -/
def halfWeightedZeroMotiveFlow (u : ℝ) : HalfWeightedZeroMotivePoint :=
  complexExponentialCharacter ((complexScalarMap (u : ℂ)).comp halfWeightedZeroGroup.subtype)

/-- The lifted exponential restricts to the original-zero flow. -/
theorem rawMotiveFlow_lift (u : ℝ) :
    rawMotiveRestriction (halfWeightedZeroMotiveFlow u) = rawZeroMotiveFlow u := by
  apply AddMonoidHom.ext
  intro z
  rfl

/-- The same lift restricts to the normalized centered flow under rotation by `i`. -/
theorem centeredMotiveFlow_lift (u : ℝ) :
    (halfWeightedZeroMotiveFlow u).comp centeredZeroInclusion = zeroMotiveFlow u := by
  apply AddMonoidHom.ext
  intro z
  apply Additive.toMul.injective
  apply Units.ext
  change Complex.exp ((u : ℂ)*(I*zeroRelationEmbedding z)) =
    Complex.exp (I*(u : ℂ)*zeroRelationEmbedding z)
  congr 1
  ring

/-- Restoring the half-weight recovers the original exponential exactly at every zero. -/
theorem rawZeroMotiveFlow_at_zero (u : ℝ) (q : XiZeroCopy) :
    ((rawZeroMotiveFlow u (rawZeroRelationRoot q)).toMul : ℂ) =
      Complex.exp ((u : ℂ)/2)*((zeroMotiveFlow u (zeroRelationRoot q)).toMul : ℂ) := by
  change Complex.exp ((u : ℂ)*(q.1 : ℂ)) = _
  rw [zeroMotiveFlow_at_zero,← Complex.exp_add]
  congr 1
  ring

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroIntegralGluing_two
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroCoordinateGluing

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroRelationGroup_full_gluing
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroGluingProjection_ker
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroIntegralGluingEquiv
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroCoordinate_double_mem_image

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRestriction_surjective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRestriction_kernel_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRestriction_kernel_two
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRestriction_conjugation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveFlow_coordinate_lift
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveFlow_at_zero

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroRelationRepresentation_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroRelationReal_source_invariant

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.halfWeightedZeroGroup_eq
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawCentralGluing_cyclic
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawCentralGluing_two

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.one_mem_rawZeroRelationGroup
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawMotiveRestriction_surjective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawMotive_extension_unique_from_half
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawMotive_half_square
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawMotiveRestriction_kernel_sign
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawMotive_coordinate_factorization
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.centeredMotiveFlow_lift
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawZeroMotiveFlow_at_zero
