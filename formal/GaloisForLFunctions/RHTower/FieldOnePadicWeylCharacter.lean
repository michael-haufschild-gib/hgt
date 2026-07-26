import GaloisForLFunctions.RHTower.FieldOneLocallyConstantWeylMultiplier
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# A nontrivial locally constant Weyl character at every finite place

For every prime `p`, this file constructs unconditionally a complex additive
character of `ℚ_[p]` which

* vanishes on `ℤ_[p]`,
* is nontrivial on the class of `p⁻¹`,
* is locally constant, and
* therefore acts on compactly supported locally constant functions through the
  finite-place Weyl multiplier.

The construction is deliberately coordinate-free.  The class of `p⁻¹` in
`ℚ_[p] / ℤ_[p]` has exact additive order `p`.  Its cyclic subgroup maps to
`ℝ / ℤ` by `1 ↦ 1 / p`; divisibility of `ℝ / ℤ`, equivalently injectivity in
the category of abelian groups, extends this character to the whole quotient.

The extension is noncanonical beyond the prescribed cyclic subgroup.  Thus
this module proves existence of a conductor-`ℤ_[p]` character and its exact
normalization at depth one; it does not identify the standard all-depth
character or assemble the global finite-adele restricted product.

No numerical computation, positivity assumption, zero-spectrum datum, or
Riemann-hypothesis premise occurs.
-/

open CategoryTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Divisibility of the additive unit circle extends every homomorphism from
an additive subgroup of a type in the base universe. -/
def fieldOneUnitAddCircleExtension
    {G : Type} [AddCommGroup G] (H : AddSubgroup G)
    (f : H →+ UnitAddCircle) : G →+ UnitAddCircle := by
  let i := AddCommGrpCat.ofHom H.subtype
  letI : Mono i :=
    ConcreteCategory.mono_of_injective i H.subtype_injective
  exact (Injective.factorThru
    (AddCommGrpCat.ofHom f) i).hom

@[simp]
theorem fieldOneUnitAddCircleExtension_apply_subtype
    {G : Type} [AddCommGroup G] (H : AddSubgroup G)
    (f : H →+ UnitAddCircle) (x : H) :
    fieldOneUnitAddCircleExtension H f x = f x := by
  let i := AddCommGrpCat.ofHom H.subtype
  letI : Mono i :=
    ConcreteCategory.mono_of_injective i H.subtype_injective
  change (i ≫
    Injective.factorThru (AddCommGrpCat.ofHom f) i) x = f x
  rw [Injective.comp_factorThru]
  rfl

/-- An additive homomorphism is locally constant when its kernel contains an
open additive subgroup. -/
theorem AddMonoidHom.isLocallyConstant_of_open_addSubgroup_le_ker
    {A B : Type*} [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] [AddCommGroup B] (f : A →+ B)
    (H : AddSubgroup A) (hH : IsOpen (H : Set A))
    (hker : H ≤ f.ker) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen {y : A | y - x ∈ H} :=
    hH.preimage (continuous_id.sub continuous_const)
  have hx : x ∈ {y : A | y - x ∈ H} := by simp
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hzero : f (y - x) = 0 := hker hy
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ℤ_[p]` as an additive subgroup of `ℚ_[p]`. -/
abbrev fieldOnePadicIntegralAddSubgroup : AddSubgroup ℚ_[p] :=
  (PadicInt.subring p).toAddSubgroup

/-- The integral additive subgroup is open in `ℚ_[p]`. -/
theorem fieldOnePadicIntegralAddSubgroup_isOpen :
    IsOpen (fieldOnePadicIntegralAddSubgroup p : Set ℚ_[p]) := by
  change IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1}
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

/-- Principal-parts quotient `ℚ_[p] / ℤ_[p]`. -/
abbrev FieldOnePadicPrincipalQuotient :=
  ℚ_[p] ⧸ fieldOnePadicIntegralAddSubgroup p

/-- The depth-one principal part represented by `p⁻¹`. -/
def fieldOnePadicPrincipalClass :
    FieldOnePadicPrincipalQuotient p :=
  QuotientAddGroup.mk'
    (fieldOnePadicIntegralAddSubgroup p) (p : ℚ_[p])⁻¹

/-- The depth-one principal class is killed by `p`. -/
theorem fieldOnePadicPrincipalClass_nsmul :
    p • fieldOnePadicPrincipalClass p = 0 := by
  change p •
    (QuotientAddGroup.mk' (fieldOnePadicIntegralAddSubgroup p))
      (p : ℚ_[p])⁻¹ = 0
  rw [← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).2
  change ‖p • (p : ℚ_[p])⁻¹‖ ≤ 1
  rw [nsmul_eq_mul]
  simp [hp.out.ne_zero]

/-- The depth-one principal class is nonzero. -/
theorem fieldOnePadicPrincipalClass_ne_zero :
    fieldOnePadicPrincipalClass p ≠ 0 := by
  intro h
  have hmem :
      (p : ℚ_[p])⁻¹ ∈ fieldOnePadicIntegralAddSubgroup p :=
    (QuotientAddGroup.eq_zero_iff _).1 h
  change ‖(p : ℚ_[p])⁻¹‖ ≤ 1 at hmem
  rw [norm_inv, Padic.norm_p, inv_inv] at hmem
  exact (not_le.mpr (by exact_mod_cast hp.out.one_lt)) hmem

/-- Exact additive order of the depth-one principal class. -/
theorem fieldOnePadicPrincipalClass_addOrderOf :
    addOrderOf (fieldOnePadicPrincipalClass p) = p := by
  have hdvd : addOrderOf (fieldOnePadicPrincipalClass p) ∣ p :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr
      (fieldOnePadicPrincipalClass_nsmul p)
  rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact (fieldOnePadicPrincipalClass_ne_zero p
      (AddMonoid.addOrderOf_eq_one_iff.mp h)).elim
  · exact h

/-- Cyclic depth-one principal-parts subgroup. -/
abbrev fieldOnePadicPrincipalCyclicSubgroup :
    AddSubgroup (FieldOnePadicPrincipalQuotient p) :=
  AddSubgroup.zmultiples (fieldOnePadicPrincipalClass p)

/-- Distinguished generator of the depth-one cyclic subgroup. -/
def fieldOnePadicPrincipalGenerator :
    fieldOnePadicPrincipalCyclicSubgroup p :=
  ⟨fieldOnePadicPrincipalClass p,
    AddSubgroup.mem_zmultiples (fieldOnePadicPrincipalClass p)⟩

theorem fieldOnePadicPrincipalGenerator_generates
    (x : fieldOnePadicPrincipalCyclicSubgroup p) :
    x ∈ AddSubgroup.zmultiples
      (fieldOnePadicPrincipalGenerator p) := by
  rw [AddSubgroup.mem_zmultiples_iff]
  rcases AddSubgroup.mem_zmultiples_iff.mp x.2 with ⟨n, hn⟩
  exact ⟨n, Subtype.ext hn⟩

theorem fieldOnePadicPrincipalCyclicSubgroup_card :
    Nat.card (fieldOnePadicPrincipalCyclicSubgroup p) = p := by
  rw [Nat.card_zmultiples,
    fieldOnePadicPrincipalClass_addOrderOf]

/-- The exact cyclic identification sending `1` to the class of `p⁻¹`. -/
noncomputable def fieldOnePadicPrincipalCyclicEquiv :
    ZMod p ≃+ fieldOnePadicPrincipalCyclicSubgroup p :=
  zmodAddEquivOfGenerator
    (g := fieldOnePadicPrincipalGenerator p)
    (fieldOnePadicPrincipalGenerator_generates p)
    (fieldOnePadicPrincipalCyclicSubgroup_card p)

/-- Normalized depth-one character `1 ↦ 1 / p mod ℤ`. -/
noncomputable def fieldOnePadicPrincipalCyclicCharacter :
    fieldOnePadicPrincipalCyclicSubgroup p →+ UnitAddCircle :=
  ZMod.toAddCircle.comp
    (fieldOnePadicPrincipalCyclicEquiv p).symm.toAddMonoidHom

@[simp]
theorem fieldOnePadicPrincipalCyclicCharacter_generator :
    fieldOnePadicPrincipalCyclicCharacter p
      (fieldOnePadicPrincipalGenerator p) =
      ZMod.toAddCircle (1 : ZMod p) := by
  change ZMod.toAddCircle
      ((fieldOnePadicPrincipalCyclicEquiv p).symm
        (fieldOnePadicPrincipalGenerator p)) =
    ZMod.toAddCircle (1 : ZMod p)
  congr 1
  exact zmodAddEquivOfGenerator_symm_apply_generator
    (fieldOnePadicPrincipalGenerator_generates p)
    (fieldOnePadicPrincipalCyclicSubgroup_card p)

/-- A noncanonical extension of the normalized depth-one character to all
principal parts. -/
noncomputable def fieldOnePadicQuotientCharacter :
    FieldOnePadicPrincipalQuotient p →+ UnitAddCircle :=
  fieldOneUnitAddCircleExtension
    (fieldOnePadicPrincipalCyclicSubgroup p)
    (fieldOnePadicPrincipalCyclicCharacter p)

/-- Additive-circle-valued character on `ℚ_[p]`, trivial on `ℤ_[p]`. -/
noncomputable def fieldOnePadicUnitAddCircleCharacter :
    ℚ_[p] →+ UnitAddCircle :=
  (fieldOnePadicQuotientCharacter p).comp
    (QuotientAddGroup.mk'
      (fieldOnePadicIntegralAddSubgroup p))

theorem fieldOnePadicUnitAddCircleCharacter_vanishes_on_integers
    {x : ℚ_[p]} (hx : x ∈ fieldOnePadicIntegralAddSubgroup p) :
    fieldOnePadicUnitAddCircleCharacter p x = 0 := by
  have hmk :
      (QuotientAddGroup.mk'
        (fieldOnePadicIntegralAddSubgroup p)) x = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 hx
  rw [fieldOnePadicUnitAddCircleCharacter,
    AddMonoidHom.comp_apply, hmk, map_zero]

theorem fieldOnePadicUnitAddCircleCharacter_principal :
    fieldOnePadicUnitAddCircleCharacter p (p : ℚ_[p])⁻¹ =
      ZMod.toAddCircle (1 : ZMod p) := by
  change fieldOnePadicQuotientCharacter p
      (fieldOnePadicPrincipalClass p) =
    ZMod.toAddCircle (1 : ZMod p)
  rw [show fieldOnePadicPrincipalClass p =
      (fieldOnePadicPrincipalGenerator p :
        FieldOnePadicPrincipalQuotient p) from rfl,
    fieldOnePadicQuotientCharacter,
    fieldOneUnitAddCircleExtension_apply_subtype,
    fieldOnePadicPrincipalCyclicCharacter_generator]

theorem fieldOnePadicUnitAddCircleCharacter_principal_ne_zero :
    fieldOnePadicUnitAddCircleCharacter p
      (p : ℚ_[p])⁻¹ ≠ 0 := by
  rw [fieldOnePadicUnitAddCircleCharacter_principal]
  intro h
  exact one_ne_zero (ZMod.toAddCircle_eq_zero.mp h)

/-- Complex-valued finite-place additive character. -/
noncomputable def fieldOnePadicAddChar : AddChar ℚ_[p] ℂ :=
  Circle.coeHom.compAddChar <|
    AddCircle.toCircle_addChar.compAddMonoidHom <|
      fieldOnePadicUnitAddCircleCharacter p

theorem fieldOnePadicAddChar_principal_ne_one :
    fieldOnePadicAddChar p (p : ℚ_[p])⁻¹ ≠ 1 := by
  intro h
  have hcircle :
      AddCircle.toCircle
          (fieldOnePadicUnitAddCircleCharacter p
            (p : ℚ_[p])⁻¹) = (1 : Circle) :=
    Subtype.ext h
  have hzero :
      fieldOnePadicUnitAddCircleCharacter p
        (p : ℚ_[p])⁻¹ = 0 :=
    AddCircle.injective_toCircle one_ne_zero <| by
      simpa only [AddCircle.toCircle_zero] using hcircle
  exact
    fieldOnePadicUnitAddCircleCharacter_principal_ne_zero p hzero

/-- The constructed character is genuinely nontrivial. -/
theorem fieldOnePadicAddChar_ne_one :
    fieldOnePadicAddChar p ≠ 1 := by
  intro h
  exact fieldOnePadicAddChar_principal_ne_one p <| by
    simpa only [Pi.one_apply] using
      DFunLike.congr_fun h (p : ℚ_[p])⁻¹

/-- Local constancy follows from the open integral kernel. -/
theorem fieldOnePadicAddChar_isLocallyConstant :
    IsLocallyConstant (fieldOnePadicAddChar p) := by
  have hlocal :
      IsLocallyConstant
        (fieldOnePadicUnitAddCircleCharacter p) := by
    apply
      AddMonoidHom.isLocallyConstant_of_open_addSubgroup_le_ker
        (fieldOnePadicUnitAddCircleCharacter p)
        (fieldOnePadicIntegralAddSubgroup p)
        (fieldOnePadicIntegralAddSubgroup_isOpen p)
    intro x hx
    exact
      fieldOnePadicUnitAddCircleCharacter_vanishes_on_integers p hx
  simpa only [fieldOnePadicAddChar,
    AddChar.compAddMonoidHom_apply,
    MonoidHom.compAddChar_apply] using
      hlocal.comp
        (fun z : UnitAddCircle => (AddCircle.toCircle z : ℂ))

/-- Packaged locally constant additive character for the generic
finite-place Weyl multiplier. -/
noncomputable def fieldOnePadicLocallyConstantAddChar :
    LocallyConstantAddChar (R := ℚ_[p]) :=
  ⟨fieldOnePadicAddChar p,
    fieldOnePadicAddChar_isLocallyConstant p⟩

/-- Specialized Weyl multiplier on `p`-adic Bruhat functions. -/
noncomputable def fieldOnePadicWeylMultiplier (r : ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ]
      compactlySupportedLocallyConstant ℚ_[p] :=
  locallyConstantWeylMultiplier
    (fieldOnePadicLocallyConstantAddChar p) r

@[simp]
theorem fieldOnePadicWeylMultiplier_apply
    (r : ℚ_[p])
    (f : compactlySupportedLocallyConstant ℚ_[p]) (x : ℚ_[p]) :
    (fieldOnePadicWeylMultiplier p r f).1 x =
      fieldOnePadicAddChar p (r * x) * f.1 x :=
  rfl

/-- Addition of `p`-adic exponents becomes composition. -/
theorem fieldOnePadicWeylMultiplier_add (r s : ℚ_[p]) :
    (fieldOnePadicWeylMultiplier p r).comp
        (fieldOnePadicWeylMultiplier p s) =
      fieldOnePadicWeylMultiplier p (r + s) :=
  locallyConstantWeylMultiplier_add
    (fieldOnePadicLocallyConstantAddChar p) r s

/-- Negation supplies the inverse multiplier. -/
theorem fieldOnePadicWeylMultiplier_neg_left (r : ℚ_[p]) :
    (fieldOnePadicWeylMultiplier p (-r)).comp
        (fieldOnePadicWeylMultiplier p r) =
      LinearMap.id :=
  locallyConstantWeylMultiplier_neg_left
    (fieldOnePadicLocallyConstantAddChar p) r

end

end GaloisForLFunctions.RHTower
