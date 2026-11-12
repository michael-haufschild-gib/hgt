import GaloisForLFunctions.GaloisTheoryOfZeros.TheBiquadraticDiagramOfTheZeroField
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Complement

/-!
# Descent of the global width square class

All nonzero zero widths determine one square class over the field of their
pairwise products. Its descent to the complete-fibre source field controls
splitting of the entire width-field Galois extension.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped IntermediateField
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Nonzero square classes of a field, with their quotient-group structure. -/
abbrev SourceSquareClass (A : Type*) [Field A] := Aˣ ⧸ (powMonoidHom (α := Aˣ) 2).range

/-- Projection from nonzero elements to their square classes. -/
def sourceSquareClassProjection (A : Type*) [Field A] : Aˣ →* SourceSquareClass A :=
  QuotientGroup.mk' (powMonoidHom (α := Aˣ) 2).range

/-- Equality of square classes is witnessed by a nonzero square factor. -/
theorem sourceSquareClass_eq_iff {A : Type*} [Field A] (a b : Aˣ) :
    sourceSquareClassProjection A a = sourceSquareClassProjection A b ↔
      ∃ u : Aˣ, a = b*u^2 := by
  change (a : Aˣ ⧸ (powMonoidHom (α := Aˣ) 2).range) = b ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  constructor
  · rintro ⟨u,hu⟩
    change u^2 = a/b at hu
    refine ⟨u,?_⟩
    calc
      a = (a/b)*b := (div_mul_cancel a b).symm
      _ = u^2*b := by rw [← hu]
      _ = b*u^2 := mul_comm _ _
  · rintro ⟨u,rfl⟩
    refine ⟨u,?_⟩
    change u^2 = (b*u^2)/b
    simp only [mul_div_cancel_left]

/-- A square class is trivial precisely when its representative is a square unit. -/
theorem sourceSquareClass_eq_one_iff {A : Type*} [Field A] (a : Aˣ) :
    sourceSquareClassProjection A a = 1 ↔ ∃ u : Aˣ, a = u^2 := by
  rw [← (sourceSquareClassProjection A).map_one,sourceSquareClass_eq_iff]
  simp only [one_mul]

/-- A field homomorphism transports square classes. -/
def sourceSquareClassMap {A B : Type*} [Field A] [Field B] (f : A →+* B) :
    SourceSquareClass A →* SourceSquareClass B :=
  QuotientGroup.map (powMonoidHom (α := Aˣ) 2).range
    (powMonoidHom (α := Bˣ) 2).range (Units.map f.toMonoidHom) (by
      rintro x ⟨u,rfl⟩
      exact ⟨Units.map f.toMonoidHom u,(map_pow (Units.map f.toMonoidHom) u 2).symm⟩)

@[simp] theorem sourceSquareClassMap_projection {A B : Type*} [Field A] [Field B]
    (f : A →+* B) (u : Aˣ) :
    sourceSquareClassMap f (sourceSquareClassProjection A u) =
      sourceSquareClassProjection B (Units.map f.toMonoidHom u) := rfl

/-- The even-width field as an actual intermediate field of the full real width extension. -/
def evenWidthInReal : IntermediateField fullFibreSourceField realWidthField :=
  evenWidthField.comap (IntermediateField.val realWidthField)

/-- This internal presentation is canonically the original even-width field in the complex numbers. -/
def evenWidthInRealEquiv : evenWidthInReal ≃ₐ[fullFibreSourceField] evenWidthField :=
  HTGeometry.comapValEquiv evenWidthField_le_realWidthField

instance evenWidthInReal_normal : Normal fullFibreSourceField evenWidthInReal :=
  Normal.of_algEquiv evenWidthInRealEquiv.symm

private theorem evenWidthInReal_mem (z : realWidthField) :
    z ∈ evenWidthInReal ↔ (z : ℂ) ∈ evenWidthField := Iff.rfl

/-- Every ratio of signed widths belongs to the even-width field, including zero denominators. -/
theorem zeroWidth_div_mem_evenWidthField (q r : XiZeroCopy) :
    zeroWidth q / zeroWidth r ∈ evenWidthField := by
  by_cases hr : zeroWidth r = 0
  · rw [hr,div_zero]
    exact evenWidthField.zero_mem
  · have he : zeroWidth q / zeroWidth r =
        (zeroWidth r*zeroWidth q)/(zeroWidth r*zeroWidth r) := by
      field_simp
    rw [he]
    exact evenWidthField.div_mem (zeroWidth_mul_mem_evenWidthField r q)
      (zeroWidth_mul_mem_evenWidthField r r)

/-- The square of a width as an element of the internal even-width field. -/
def widthSquareInEven (q : XiZeroCopy) : evenWidthInReal :=
  ⟨(zeroWidthInField q)^2,by
    change zeroWidth q^2 ∈ evenWidthField
    rw [pow_two]
    exact zeroWidth_mul_mem_evenWidthField q q⟩

private theorem widthSquareInEven_coe (q : XiZeroCopy) :
    (((widthSquareInEven q : evenWidthInReal) : realWidthField) : ℂ) = zeroWidth q^2 := rfl

/-- A nonzero width square determines a unit of the even-width field. -/
def widthSquareUnit (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) : evenWidthInRealˣ :=
  Units.mk0 (widthSquareInEven q) (by
    intro h
    have he := congrArg (fun a : evenWidthInReal => ((a : realWidthField) : ℂ)) h
    exact (pow_ne_zero 2 hq) he)

/-- The intrinsic square class associated to any nonzero zero width. -/
def widthSquareClass (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) : SourceSquareClass evenWidthInReal :=
  sourceSquareClassProjection evenWidthInReal (widthSquareUnit q hq)

private def widthRatioInEven (q r : XiZeroCopy) : evenWidthInReal :=
  ⟨zeroWidthInField q / zeroWidthInField r,zeroWidth_div_mem_evenWidthField q r⟩

private def widthRatioUnit (q r : XiZeroCopy) (hq : zeroWidth q ≠ 0) (hr : zeroWidth r ≠ 0) :
    evenWidthInRealˣ :=
  Units.mk0 (widthRatioInEven q r) (by
    intro h
    have he := congrArg (fun a : evenWidthInReal => ((a : realWidthField) : ℂ)) h
    exact (div_ne_zero hq hr) he)

/-- Changing a nonzero width anchor changes its square by an explicit square of a width ratio. -/
theorem widthSquareUnit_change_anchor (q r : XiZeroCopy)
    (hq : zeroWidth q ≠ 0) (hr : zeroWidth r ≠ 0) :
    widthSquareUnit q hq = widthSquareUnit r hr * (widthRatioUnit q r hq hr)^2 := by
  apply Units.ext
  apply Subtype.ext
  apply Subtype.ext
  change zeroWidth q^2 = zeroWidth r^2*(zeroWidth q/zeroWidth r)^2
  field_simp

/-- All nonzero widths define one square class over the entire even-width field. -/
theorem widthSquareClass_anchor_independent (q r : XiZeroCopy)
    (hq : zeroWidth q ≠ 0) (hr : zeroWidth r ≠ 0) :
    widthSquareClass q hq = widthSquareClass r hr :=
  (sourceSquareClass_eq_iff _ _).mpr ⟨widthRatioUnit q r hq hr,
    widthSquareUnit_change_anchor q r hq hr⟩

private theorem widthSquareClass_trivial_iff_mem (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    widthSquareClass q hq = 1 ↔ zeroWidth q ∈ evenWidthField := by
  rw [widthSquareClass,sourceSquareClass_eq_one_iff]
  constructor
  · rintro ⟨u,hu⟩
    have he := congrArg (fun v : evenWidthInRealˣ => (((v : evenWidthInReal) : realWidthField) : ℂ)) hu
    change zeroWidth q^2 = ((((u : evenWidthInReal) : realWidthField) : ℂ))^2 at he
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with h | h
    · rw [h]
      exact (u : evenWidthInReal).property
    · rw [h]
      exact evenWidthField.neg_mem (u : evenWidthInReal).property
  · intro hqE
    let a : evenWidthInReal := ⟨zeroWidthInField q,hqE⟩
    have ha : a ≠ 0 := by
      intro h
      exact hq (congrArg (fun v : evenWidthInReal => ((v : realWidthField) : ℂ)) h)
    refine ⟨Units.mk0 a ha,?_⟩
    apply Units.ext
    rfl

/-- The global signed-width extension collapses exactly when the common width class is trivial. -/
theorem widthSquareClass_trivial_iff (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    widthSquareClass q hq = 1 ↔ realWidthField = evenWidthField := by
  rw [widthSquareClass_trivial_iff_mem,realWidthField_eq_even_iff q hq]

/-- A nonzero width generates the full real width field over its internal even field. -/
theorem evenWidthInReal_adjoin_anchor_top (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    evenWidthInReal⟮zeroWidthInField q⟯ = ⊤ := by
  let H : IntermediateField evenWidthInReal realWidthField :=
    evenWidthInReal⟮zeroWidthInField q⟯
  have hroot (r : XiZeroCopy) : zeroWidthInField r ∈ H := by
    have hratio : zeroWidthInField r / zeroWidthInField q ∈ H :=
      H.algebraMap_mem (widthRatioInEven r q)
    have he : zeroWidthInField r =
        (zeroWidthInField r / zeroWidthInField q)*zeroWidthInField q := by
      apply Subtype.ext
      change zeroWidth r = (zeroWidth r/zeroWidth q)*zeroWidth q
      exact (div_mul_cancel₀ (zeroWidth r) hq).symm
    rw [he]
    exact H.mul_mem hratio (IntermediateField.mem_adjoin_simple_self _ _)
  have hle : realWidthField ≤
      (H.restrictScalars fullFibreSourceField).map (IntermediateField.val realWidthField) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨r,rfl⟩
    exact ⟨zeroWidthInField r,hroot r,rfl⟩
  apply top_unique
  intro z _
  obtain ⟨a,ha,he⟩ := hle z.property
  have haz : a = z := Subtype.ext he
  rwa [haz] at ha

/-- Restriction from all signed widths to all even products. -/
def widthEvenRestriction :
    (realWidthField ≃ₐ[fullFibreSourceField] realWidthField) →*
      (evenWidthInReal ≃ₐ[fullFibreSourceField] evenWidthInReal) :=
  AlgEquiv.restrictNormalHom evenWidthInReal

/-- Every even-field automorphism extends to the entire signed-width field. -/
theorem widthEvenRestriction_surjective : Function.Surjective widthEvenRestriction :=
  AlgEquiv.restrictNormalHom_surjective realWidthField

/-- Restriction respects the Krull topology on the entire extensions. -/
theorem widthEvenRestriction_continuous : Continuous widthEvenRestriction :=
  InfiniteGalois.restrictNormalHom_continuous evenWidthInReal

/-- Continuous splitting of the full width restriction map. -/
def WidthRestrictionSplits : Prop :=
  ∃ s : (evenWidthInReal ≃ₐ[fullFibreSourceField] evenWidthInReal) →*
      (realWidthField ≃ₐ[fullFibreSourceField] realWidthField),
    Continuous s ∧ ∀ σ, widthEvenRestriction (s σ) = σ

/-- Source descent of a nonzero width square, expressed by an actual square witness. -/
def WidthSquareDescends (q : XiZeroCopy) : Prop :=
  ∃ (a : fullFibreSourceFieldˣ) (u : evenWidthInRealˣ),
    widthSquareInEven q = (algebraMap fullFibreSourceField evenWidthInReal (a : fullFibreSourceField))*
      (u : evenWidthInReal)^2

private theorem section_range_index {G Q : Type*} [Group G] [Group Q]
    (r : G →* Q) (s : Q →* G) (hs : ∀ q, r (s q) = q) :
    s.range.index = Nat.card r.ker := by
  have hcomp : Subgroup.IsComplement' r.ker s.range := by
    apply Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mpr
    intro g
    refine ⟨⟨s (r g),⟨r g,rfl⟩⟩,?_,?_⟩
    · change r (g*(s (r g))⁻¹) = 1
      rw [map_mul,map_inv,hs,mul_inv_cancel]
    · intro t ht
      apply Subtype.ext
      obtain ⟨q,hq⟩ := t.property
      have he : r g = r (t : G) := by
        have ht' : r (g*(t : G)⁻¹) = 1 := ht
        rw [map_mul,map_inv] at ht'
        exact mul_inv_eq_one.mp ht'
      rw [← hq,hs] at he
      rw [← hq,he]
  exact hcomp.card_left.symm

private theorem width_restriction_square_coe
    (τ : realWidthField ≃ₐ[fullFibreSourceField] realWidthField) (q : XiZeroCopy) :
    ((widthEvenRestriction τ (widthSquareInEven q) : evenWidthInReal) : realWidthField) =
      (τ (zeroWidthInField q))^2 := by
  exact (AlgEquiv.restrictNormal_commutes τ evenWidthInReal (widthSquareInEven q)).trans
    (map_pow τ (zeroWidthInField q) 2)

private theorem width_field_mem_anchor (q : XiZeroCopy) (hq : zeroWidth q ≠ 0)
    (z : realWidthField) : (z : ℂ) ∈ evenWidthField⟮zeroWidth q⟯ := by
  have hm (u : ℂ) : u ∈ realWidthField ↔ u ∈ evenWidthField⟮zeroWidth q⟯ := by
    rw [realWidthField_eq_width_anchor q hq]
    rfl
  exact (hm (z : ℂ)).mp z.property

private theorem width_aut_not_mem_even
    (τ : realWidthField ≃ₐ[fullFibreSourceField] realWidthField)
    (q : XiZeroCopy) (hq : zeroWidth q ∉ evenWidthField) :
    (τ (zeroWidthInField q) : ℂ) ∉ evenWidthField := by
  intro hz
  let z : evenWidthInReal := ⟨τ (zeroWidthInField q),hz⟩
  have he : ((τ.symm.restrictNormal evenWidthInReal z : evenWidthInReal) : realWidthField) =
      zeroWidthInField q := by
    exact (AlgEquiv.restrictNormal_commutes τ.symm evenWidthInReal z).trans
      (τ.symm_apply_apply (zeroWidthInField q))
  have hm := (τ.symm.restrictNormal evenWidthInReal z).property
  change (((τ.symm.restrictNormal evenWidthInReal z : evenWidthInReal) : realWidthField) : ℂ)
    ∈ evenWidthField at hm
  rw [he] at hm
  exact hq hm

/-- The common nonzero width class is invariant under every automorphism of the entire even field. -/
theorem widthSquareClass_invariant (q : XiZeroCopy) (hq : zeroWidth q ≠ 0)
    (σ : evenWidthInReal ≃ₐ[fullFibreSourceField] evenWidthInReal) :
    sourceSquareClassMap σ.toRingHom (widthSquareClass q hq) = widthSquareClass q hq := by
  classical
  by_cases hqE : zeroWidth q ∈ evenWidthField
  · have hc : widthSquareClass q hq = 1 := (widthSquareClass_trivial_iff_mem q hq).mpr hqE
    rw [hc,map_one]
  · obtain ⟨τ,hτ⟩ := widthEvenRestriction_surjective σ
    let z : realWidthField := τ (zeroWidthInField q)
    have hzsq : (z : ℂ)*(z : ℂ) ∈ evenWidthField := by
      have he := congrArg (fun v : realWidthField => (v : ℂ)) (width_restriction_square_coe τ q)
      rw [hτ] at he
      change (((σ (widthSquareInEven q) : evenWidthInReal) : realWidthField) : ℂ) = (z : ℂ)^2 at he
      rw [← pow_two,← he]
      exact (σ (widthSquareInEven q)).property
    obtain ⟨a,ha⟩ : ∃ a : evenWidthField, (z : ℂ) = (a : ℂ)*zeroWidth q := by
      rcases quadratic_square_root_line evenWidthField.toSubfield
        (zeroWidth_mul_mem_evenWidthField q q) hqE (width_field_mem_anchor q hq z) hzsq with
        hz | hline
      · exact False.elim (width_aut_not_mem_even τ q hqE hz)
      · exact hline
    have hz0 : (z : ℂ) ≠ 0 := by
      intro hz
      have hzF : z = 0 := Subtype.ext hz
      have hqF : zeroWidthInField q = 0 := τ.injective (hzF.trans (map_zero τ).symm)
      exact hq (congrArg (fun v : realWidthField => (v : ℂ)) hqF)
    have ha0 : (a : ℂ) ≠ 0 := by
      intro h
      apply hz0
      rw [ha,h,zero_mul]
    let aE : evenWidthInReal := ⟨⟨a,evenWidthField_le_realWidthField a.property⟩,a.property⟩
    have haE : aE ≠ 0 := by
      intro h
      exact ha0 (congrArg (fun v : evenWidthInReal => ((v : realWidthField) : ℂ)) h)
    let u : evenWidthInRealˣ := Units.mk0 aE haE
    change sourceSquareClassMap σ.toRingHom
        (sourceSquareClassProjection evenWidthInReal (widthSquareUnit q hq)) = _
    rw [sourceSquareClassMap_projection]
    apply (sourceSquareClass_eq_iff _ _).mpr
    refine ⟨u,?_⟩
    apply Units.ext
    apply Subtype.ext
    apply Subtype.ext
    change (((σ (widthSquareInEven q) : evenWidthInReal) : realWidthField) : ℂ) =
      zeroWidth q^2*(a : ℂ)^2
    have he := congrArg (fun v : realWidthField => (v : ℂ)) (width_restriction_square_coe τ q)
    rw [hτ] at he
    rw [he]
    change (z : ℂ)^2 = zeroWidth q^2*(a : ℂ)^2
    rw [ha]
    ring

private theorem quadratic_degree_of_adjoin_top {A B : Type*} [Field A] [Field B] [Algebra A B]
    {b : B} {d : A} (hs : b*b = algebraMap A B d)
    (hb : b ∉ (⊥ : IntermediateField A B)) (htop : A⟮b⟯ = ⊤) :
    Module.finrank A B = 2 := by
  have hd := HTGeometry.finrank_adjoin_eq_two hs hb
  rwa [htop,IntermediateField.finrank_top'] at hd

/-- A width outside the even products makes the entire signed-width extension quadratic. -/
theorem widthEven_finrank_two (q : XiZeroCopy) (hq : zeroWidth q ∉ evenWidthField) :
    Module.finrank evenWidthInReal realWidthField = 2 := by
  have hq0 : zeroWidth q ≠ 0 := by
    intro h
    exact hq (h ▸ evenWidthField.zero_mem)
  apply quadratic_degree_of_adjoin_top
    (d := widthSquareInEven q)
    (show zeroWidthInField q*zeroWidthInField q =
      algebraMap evenWidthInReal realWidthField (widthSquareInEven q) by
        change zeroWidthInField q*zeroWidthInField q = (zeroWidthInField q)^2
        rw [pow_two])
    _ (evenWidthInReal_adjoin_anchor_top q hq0)
  intro h
  obtain ⟨a,ha⟩ := IntermediateField.mem_bot.mp h
  have he : (((a : evenWidthInReal) : realWidthField) : ℂ) = zeroWidth q :=
    congrArg (fun v : realWidthField => (v : ℂ)) ha
  exact hq (he ▸ a.property)

/-- The restriction kernel has exactly two elements in the nontrivial width regime. -/
theorem widthEvenRestriction_kernel_card (q : XiZeroCopy) (hq : zeroWidth q ∉ evenWidthField) :
    Nat.card widthEvenRestriction.ker = 2 := by
  letI : IsGalois fullFibreSourceField realWidthField := ⟨⟩
  letI : Algebra.IsQuadraticExtension evenWidthInReal realWidthField :=
    { toFree := inferInstance
      finrank_eq_two' := widthEven_finrank_two q hq }
  change Nat.card (AlgEquiv.restrictNormalHom evenWidthInReal).ker = 2
  rw [IntermediateField.restrictNormalHom_ker]
  rw [Nat.card_congr (IntermediateField.fixingSubgroupEquiv evenWidthInReal).toEquiv,
    IsGalois.card_aut_eq_finrank]
  exact widthEven_finrank_two q hq

private theorem continuous_bijective_hom_section {G Q : Type*} [Group G] [Group Q]
    [TopologicalSpace G] [TopologicalSpace Q] [CompactSpace G] [T2Space Q]
    (r : G →* Q) (hc : Continuous r) (hb : Function.Bijective r) :
    ∃ s : Q →* G, Continuous s ∧ ∀ q, r (s q) = q := by
  let e : G ≃* Q := MulEquiv.ofBijective r hb
  let he := Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) hc
  exact ⟨e.symm.toMonoidHom,he.continuous_invFun,e.apply_symm_apply⟩

/-- The restriction map splits when all signed widths already lie in the even field. -/
theorem widthRestrictionSplits_of_eq (h : realWidthField = evenWidthField) : WidthRestrictionSplits := by
  letI : IsGalois fullFibreSourceField realWidthField := ⟨⟩
  have htop : evenWidthInReal = ⊤ := by
    apply top_unique
    intro z _
    change (z : ℂ) ∈ evenWidthField
    rw [← h]
    exact z.property
  apply continuous_bijective_hom_section widthEvenRestriction widthEvenRestriction_continuous
  refine ⟨?_,widthEvenRestriction_surjective⟩
  apply (MonoidHom.ker_eq_bot_iff widthEvenRestriction).mp
  change (AlgEquiv.restrictNormalHom evenWidthInReal).ker = ⊥
  rw [IntermediateField.restrictNormalHom_ker,htop,IntermediateField.fixingSubgroup_top]

/-- Descent is precisely membership in the source square-class image. -/
theorem widthSquareDescends_iff_class_image (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    WidthSquareDescends q ↔
      widthSquareClass q hq ∈ Set.range
        (sourceSquareClassMap (algebraMap fullFibreSourceField evenWidthInReal)) := by
  constructor
  · rintro ⟨a,u,he⟩
    refine ⟨sourceSquareClassProjection fullFibreSourceField a,?_⟩
    rw [sourceSquareClassMap_projection]
    symm
    apply (sourceSquareClass_eq_iff _ _).mpr
    exact ⟨u,Units.ext he⟩
  · rintro ⟨v,hv⟩
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (α := fullFibreSourceFieldˣ) 2).range v
    change sourceSquareClassMap (algebraMap fullFibreSourceField evenWidthInReal)
      (sourceSquareClassProjection fullFibreSourceField a) = widthSquareClass q hq at hv
    rw [sourceSquareClassMap_projection] at hv
    obtain ⟨u,hu⟩ := (sourceSquareClass_eq_iff _ _).mp hv.symm
    exact ⟨a,u,congrArg (fun x : evenWidthInRealˣ => (x : evenWidthInReal)) hu⟩

private theorem fixing_adjoin_eq_stabilizer {K L : Type*} [Field K] [Field L] [Algebra K L]
    (b : L) :
    (K⟮b⟯).fixingSubgroup = MulAction.stabilizer (L ≃ₐ[K] L) b := by
  apply le_antisymm
  · intro σ hσ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ b
      (IntermediateField.mem_adjoin_simple_self K b)
  · apply (IntermediateField.le_iff_le _ _).mp
    apply IntermediateField.adjoin_simple_le_iff.mpr
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hσ

private theorem aut_square_root_image {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (b : L) (a : K) (hs : b^2 = algebraMap K L a) :
    σ b = b ∨ σ b = -b := by
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  calc
    (σ b)^2 = σ (b^2) := (map_pow σ b 2).symm
    _ = σ (algebraMap K L a) := congrArg σ hs
    _ = algebraMap K L a := σ.commutes a
    _ = b^2 := hs.symm

/-- A source square root complementary to a normal intermediate field supplies a continuous section. -/
private theorem quadratic_source_root_section {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (E : IntermediateField K L) [Normal K E]
    (b : L) (a : K) (hs : b^2 = algebraMap K L a) (hb : b ∉ E)
    (htop : E⟮b⟯ = ⊤) :
    ∃ s : (E ≃ₐ[K] E) →* (L ≃ₐ[K] L), Continuous s ∧
      ∀ σ, AlgEquiv.restrictNormalHom E (s σ) = σ := by
  classical
  let r : (L ≃ₐ[K] L) →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E
  let D : IntermediateField K L := K⟮b⟯
  let H : ClosedSubgroup (L ≃ₐ[K] L) :=
    ⟨D.fixingSubgroup,InfiniteGalois.fixingSubgroup_isClosed D⟩
  let rH : H →* (E ≃ₐ[K] E) := r.comp H.toSubgroup.subtype
  have hgen : E ⊔ D = ⊤ := by
    have h := congrArg (fun A : IntermediateField E L => A.restrictScalars K) htop
    rw [IntermediateField.restrictScalars_adjoin_eq_sup] at h
    exact h
  have hinj : Function.Injective rH := by
    intro σ τ hστ
    apply Subtype.ext
    have hker : (σ : L ≃ₐ[K] L)*(τ : L ≃ₐ[K] L)⁻¹ ∈ E.fixingSubgroup := by
      rw [← E.restrictNormalHom_ker]
      change r ((σ : L ≃ₐ[K] L)*(τ : L ≃ₐ[K] L)⁻¹) = 1
      rw [map_mul,map_inv]
      change rH σ*(rH τ)⁻¹ = 1
      rw [hστ,mul_inv_cancel]
    have hD : (σ : L ≃ₐ[K] L)*(τ : L ≃ₐ[K] L)⁻¹ ∈ D.fixingSubgroup :=
      D.fixingSubgroup.mul_mem σ.property (D.fixingSubgroup.inv_mem τ.property)
    have hz : (σ : L ≃ₐ[K] L)*(τ : L ≃ₐ[K] L)⁻¹ ∈ (E ⊔ D).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hker,hD⟩
    rw [hgen,IntermediateField.fixingSubgroup_top] at hz
    exact mul_inv_eq_one.mp hz
  have hsurj : Function.Surjective rH := by
    intro σ
    obtain ⟨τ,hτ⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    have hτ' : r τ = σ := hτ
    rcases aut_square_root_image τ b a hs with hplus | hminus
    · refine ⟨⟨τ,?_⟩,hτ'⟩
      change τ ∈ (K⟮b⟯).fixingSubgroup
      rw [fixing_adjoin_eq_stabilizer]
      exact hplus
    · have hbnot : b ∉ (⊥ : IntermediateField E L) := by
        rintro ⟨e,he⟩
        exact hb (he ▸ e.property)
      have hex : ∃ κ : L ≃ₐ[E] L, κ b ≠ b := by
        by_contra! hn
        exact hbnot ((InfiniteGalois.mem_bot_iff_fixed b).mpr hn)
      obtain ⟨κ,hκ⟩ := hex
      let κK : L ≃ₐ[K] L := κ.restrictScalars K
      have hκb : κK b = -b :=
        (aut_square_root_image κK b a hs).resolve_left hκ
      have hκr : r κK = 1 := by
        apply AlgEquiv.ext
        intro e
        apply Subtype.ext
        exact (AlgEquiv.restrictNormal_commutes κK E e).trans (κ.commutes e)
      have hfix : (τ*κK) b = b := by
        change τ (κK b) = b
        rw [hκb,map_neg,hminus,neg_neg]
      refine ⟨⟨τ*κK,?_⟩,?_⟩
      · change τ*κK ∈ (K⟮b⟯).fixingSubgroup
        rw [fixing_adjoin_eq_stabilizer]
        exact hfix
      · change r (τ*κK) = σ
        rw [map_mul,hκr,mul_one,hτ']
  have hc : Continuous rH :=
    (InfiniteGalois.restrictNormalHom_continuous E).comp continuous_subtype_val
  obtain ⟨s,hscont,hsright⟩ := continuous_bijective_hom_section rH hc ⟨hinj,hsurj⟩
  exact ⟨H.toSubgroup.subtype.comp s,continuous_subtype_val.comp hscont,hsright⟩

/-- A descended width square splits the whole restriction map by fixing its source square root. -/
theorem widthRestrictionSplits_of_descends (q : XiZeroCopy)
    (hq : zeroWidth q ∉ evenWidthField) (hd : WidthSquareDescends q) : WidthRestrictionSplits := by
  letI : IsGalois fullFibreSourceField realWidthField := ⟨⟩
  obtain ⟨a,u,hu⟩ := hd
  have hq0 : zeroWidth q ≠ 0 := by
    intro h
    exact hq (h ▸ evenWidthField.zero_mem)
  let v : realWidthField := algebraMap evenWidthInReal realWidthField (u : evenWidthInReal)
  have hv : v ≠ 0 := by
    intro h
    apply u.ne_zero
    apply (algebraMap evenWidthInReal realWidthField).injective
    simpa only [map_zero] using h
  let b : realWidthField := zeroWidthInField q/v
  have hdb : zeroWidthInField q = b*v := (div_mul_cancel₀ _ hv).symm
  have hsq : b^2 = algebraMap fullFibreSourceField realWidthField (a : fullFibreSourceField) := by
    have he := congrArg (algebraMap evenWidthInReal realWidthField) hu
    rw [map_mul,map_pow,← IsScalarTower.algebraMap_apply fullFibreSourceField
      evenWidthInReal realWidthField] at he
    change (zeroWidthInField q)^2 =
      algebraMap fullFibreSourceField realWidthField (a : fullFibreSourceField)*v^2 at he
    change (zeroWidthInField q/v)^2 = _
    rw [div_pow]
    exact (div_eq_iff (pow_ne_zero 2 hv)).mpr he
  have hb : b ∉ evenWidthInReal := by
    intro hbE
    have hδ : zeroWidthInField q ∈ evenWidthInReal := by
      rw [hdb]
      exact evenWidthInReal.mul_mem hbE (u : evenWidthInReal).property
    exact hq hδ
  have htop : evenWidthInReal⟮b⟯ = ⊤ := by
    apply top_unique
    rw [← evenWidthInReal_adjoin_anchor_top q hq0]
    apply IntermediateField.adjoin_simple_le_iff.mpr
    rw [hdb]
    exact (evenWidthInReal⟮b⟯).mul_mem
      (IntermediateField.mem_adjoin_simple_self evenWidthInReal b)
      ((evenWidthInReal⟮b⟯).algebraMap_mem (u : evenWidthInReal))
  exact quadratic_source_root_section evenWidthInReal b (a : fullFibreSourceField) hsq hb htop

/-- A continuous section with quadratic kernel cuts out a quadratic source field disjoint from the base stage. -/
private theorem section_quadratic_fixed_field {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (E : IntermediateField K L) [Normal K E]
    (s : (E ≃ₐ[K] E) →* (L ≃ₐ[K] L)) (hc : Continuous s)
    (hs : ∀ σ, AlgEquiv.restrictNormalHom E (s σ) = σ)
    (hk : Nat.card (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker = 2) :
    ∃ D : IntermediateField K L, Module.finrank K D = 2 ∧ D ⊓ E = ⊥ := by
  letI : IsGalois K E := ⟨⟩
  let H : ClosedSubgroup (L ≃ₐ[K] L) := ⟨s.range,(isCompact_range hc).isClosed⟩
  let D : IntermediateField K L := IntermediateField.fixedField H.toSubgroup
  have hdeg : Module.finrank K D = 2 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      InfiniteGalois.fixingSubgroup_fixedField H]
    change s.range.index = 2
    rw [section_range_index (AlgEquiv.restrictNormalHom E) s hs]
    exact hk
  refine ⟨D,hdeg,le_antisymm ?_ bot_le⟩
  intro x hx
  let xE : E := ⟨x,hx.2⟩
  have hfix : ∀ σ : E ≃ₐ[K] E, σ xE = xE := by
    intro σ
    apply Subtype.ext
    have hσx : s σ x = x :=
      (IntermediateField.mem_fixedField_iff _ _).mp hx.1 (s σ) ⟨σ,rfl⟩
    have hcomm := AlgEquiv.restrictNormal_commutes (s σ) E xE
    change algebraMap E L ((AlgEquiv.restrictNormalHom E (s σ)) xE) =
      s σ (algebraMap E L xE) at hcomm
    rw [hs σ] at hcomm
    exact hcomm.trans hσx
  obtain ⟨a,ha⟩ := IntermediateField.mem_bot.mp ((InfiniteGalois.mem_bot_iff_fixed xE).mpr hfix)
  apply IntermediateField.mem_bot.mpr
  refine ⟨a,?_⟩
  have he := congrArg (algebraMap E L) ha
  rwa [← IsScalarTower.algebraMap_apply K E L] at he

/-- A continuous section forces the common width square to descend to the source field. -/
theorem widthSquareDescends_of_splits (q : XiZeroCopy)
    (hq : zeroWidth q ∉ evenWidthField) (hs : WidthRestrictionSplits) : WidthSquareDescends q := by
  letI : IsGalois fullFibreSourceField realWidthField := ⟨⟩
  obtain ⟨s,hcont,hs⟩ := hs
  obtain ⟨D,hD,hDE⟩ := section_quadratic_fixed_field evenWidthInReal s hcont hs
    (widthEvenRestriction_kernel_card q hq)
  let N : IntermediateField fullFibreSourceField ℂ := D.map (IntermediateField.val realWidthField)
  have hN : Module.finrank fullFibreSourceField N = 2 :=
    (IntermediateField.equivMap D (IntermediateField.val realWidthField)).toLinearEquiv.finrank_eq.symm.trans hD
  obtain ⟨b,hbN,hbK,hbbK,_⟩ := quadratic_subfield_square_generator fullFibreSourceField N hN
  obtain ⟨β,hβD,hβ⟩ := hbN
  change (β : ℂ) = b at hβ
  have hβK : (β : ℂ) ∉ fullFibreSourceField := by rwa [hβ]
  have hβsquare : (β : ℂ)*(β : ℂ) ∈ fullFibreSourceField := by rwa [hβ]
  have hβE : (β : ℂ) ∉ evenWidthField := by
    intro h
    have hb0 : β ∈ (⊥ : IntermediateField fullFibreSourceField realWidthField) := by
      rw [← hDE]
      exact ⟨hβD,h⟩
    obtain ⟨a,ha⟩ := IntermediateField.mem_bot.mp hb0
    have he : (a : ℂ) = (β : ℂ) := congrArg (fun v : realWidthField => (v : ℂ)) ha
    exact hβK (he ▸ a.property)
  have hq0 : zeroWidth q ≠ 0 := by
    intro h
    exact hq (h ▸ evenWidthField.zero_mem)
  have hβsquareE : (β : ℂ)*(β : ℂ) ∈ evenWidthField :=
    evenWidthField.algebraMap_mem (⟨_,hβsquare⟩ : fullFibreSourceField)
  obtain ⟨a,ha⟩ : ∃ a : evenWidthField, (β : ℂ) = (a : ℂ)*zeroWidth q := by
    rcases quadratic_square_root_line evenWidthField.toSubfield
      (zeroWidth_mul_mem_evenWidthField q q) hq (width_field_mem_anchor q hq0 β) hβsquareE with
      h | hline
    · exact False.elim (hβE h)
    · exact hline
  have hβ0 : (β : ℂ) ≠ 0 := by
    intro h
    exact hβK (h ▸ fullFibreSourceField.zero_mem)
  have ha0 : (a : ℂ) ≠ 0 := by
    intro h
    apply hβ0
    rw [ha,h,zero_mul]
  let c : fullFibreSourceField := ⟨(β : ℂ)^2,by simpa only [pow_two] using hβsquare⟩
  have hc : c ≠ 0 := by
    intro h
    exact (pow_ne_zero 2 hβ0) (congrArg (fun k : fullFibreSourceField => (k : ℂ)) h)
  let uE : evenWidthInReal :=
    ⟨⟨(a : ℂ)⁻¹,evenWidthField_le_realWidthField (evenWidthField.inv_mem a.property)⟩,
      evenWidthField.inv_mem a.property⟩
  have huE : uE ≠ 0 := by
    intro h
    exact (inv_ne_zero ha0) (congrArg (fun v : evenWidthInReal => ((v : realWidthField) : ℂ)) h)
  refine ⟨Units.mk0 c hc,Units.mk0 uE huE,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change zeroWidth q^2 = (β : ℂ)^2*((a : ℂ)⁻¹)^2
  rw [ha]
  field_simp

private theorem widthSquareDescends_of_mem (q : XiZeroCopy)
    (hq0 : zeroWidth q ≠ 0) (hq : zeroWidth q ∈ evenWidthField) : WidthSquareDescends q := by
  let u : evenWidthInReal := ⟨zeroWidthInField q,hq⟩
  have hu : u ≠ 0 := by
    intro h
    exact hq0 (congrArg (fun v : evenWidthInReal => ((v : realWidthField) : ℂ)) h)
  refine ⟨1,Units.mk0 u hu,?_⟩
  rw [Units.val_one,map_one,one_mul]
  rfl

/-- The full width restriction splits continuously exactly when its common square class descends. -/
theorem widthRestrictionSplits_iff_descends (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    WidthRestrictionSplits ↔ WidthSquareDescends q := by
  by_cases hqE : zeroWidth q ∈ evenWidthField
  · exact ⟨fun _ => widthSquareDescends_of_mem q hq hqE,
      fun _ => widthRestrictionSplits_of_eq ((realWidthField_eq_even_iff q hq).mpr hqE)⟩
  · exact ⟨widthSquareDescends_of_splits q hqE,widthRestrictionSplits_of_descends q hqE⟩

/-- A topological splitting is equivalent to source-field descent of the invariant width square class. -/
theorem widthRestrictionSplits_iff_class_image (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    WidthRestrictionSplits ↔
      widthSquareClass q hq ∈ Set.range
        (sourceSquareClassMap (algebraMap fullFibreSourceField evenWidthInReal)) := by
  rw [widthRestrictionSplits_iff_descends q hq,widthSquareDescends_iff_class_image q hq]

/-- The common width class, with the identity class in the all-zero-width case. -/
def globalWidthSquareClass : SourceSquareClass evenWidthInReal := by
  classical
  exact if h : ∃ q : XiZeroCopy, zeroWidth q ≠ 0 then
    widthSquareClass h.choose h.choose_spec else 1

/-- Every nonzero width represents the global square class. -/
theorem globalWidthSquareClass_eq (q : XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    globalWidthSquareClass = widthSquareClass q hq := by
  classical
  have hex : ∃ r : XiZeroCopy, zeroWidth r ≠ 0 := ⟨q,hq⟩
  rw [globalWidthSquareClass,dif_pos hex]
  exact widthSquareClass_anchor_independent _ q hex.choose_spec hq

private theorem widthField_eq_even_of_no_anchor
    (h : ¬ ∃ q : XiZeroCopy, zeroWidth q ≠ 0) : realWidthField = evenWidthField := by
  apply le_antisymm _ evenWidthField_le_realWidthField
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨q,rfl⟩
  have hq : zeroWidth q = 0 := by by_contra hq; exact h ⟨q,hq⟩
  rw [hq]
  exact evenWidthField.zero_mem

/-- The global width class is trivial exactly when the signed and even width fields coincide. -/
theorem globalWidthSquareClass_trivial_iff :
    globalWidthSquareClass = 1 ↔ realWidthField = evenWidthField := by
  classical
  by_cases h : ∃ q : XiZeroCopy, zeroWidth q ≠ 0
  · obtain ⟨q,hq⟩ := h
    rw [globalWidthSquareClass_eq q hq,widthSquareClass_trivial_iff q hq]
  · rw [globalWidthSquareClass,dif_neg h]
    exact ⟨fun _ => widthField_eq_even_of_no_anchor h,fun _ => rfl⟩

/-- Every source automorphism of the whole even field fixes the global width class. -/
theorem globalWidthSquareClass_invariant
    (σ : evenWidthInReal ≃ₐ[fullFibreSourceField] evenWidthInReal) :
    sourceSquareClassMap σ.toRingHom globalWidthSquareClass = globalWidthSquareClass := by
  classical
  by_cases h : ∃ q : XiZeroCopy, zeroWidth q ≠ 0
  · obtain ⟨q,hq⟩ := h
    rw [globalWidthSquareClass_eq q hq]
    exact widthSquareClass_invariant q hq σ
  · rw [globalWidthSquareClass,dif_neg h,map_one]

/-- Continuous splitting of the whole infinite width action is exactly source descent of its global class. -/
theorem globalWidthSquareClass_descent_iff :
    WidthRestrictionSplits ↔
      globalWidthSquareClass ∈ Set.range
        (sourceSquareClassMap (algebraMap fullFibreSourceField evenWidthInReal)) := by
  classical
  by_cases h : ∃ q : XiZeroCopy, zeroWidth q ≠ 0
  · obtain ⟨q,hq⟩ := h
    rw [globalWidthSquareClass_eq q hq]
    exact widthRestrictionSplits_iff_class_image q hq
  · rw [globalWidthSquareClass,dif_neg h]
    exact ⟨fun _ => ⟨1,map_one _⟩,
      fun _ => widthRestrictionSplits_of_eq (widthField_eq_even_of_no_anchor h)⟩

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareClass_anchor_independent
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareClass_trivial_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.evenWidthInReal_adjoin_anchor_top
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareClass_invariant
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthEvenRestriction_kernel_card
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthRestrictionSplits_of_eq
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareDescends_iff_class_image
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthRestrictionSplits_of_descends
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquareDescends_of_splits
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.globalWidthSquareClass_trivial_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.globalWidthSquareClass_invariant
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.globalWidthSquareClass_descent_iff
