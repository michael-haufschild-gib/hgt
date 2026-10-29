import GaloisForLFunctions.HeckeLFunctions.IdealsOfARayClassAreConePoints

/-!
# Nonzero ideal elements as global-unit orbits

Multiplication by a nonzero integral ideal identifies its inverse ordinary ideal class with
principal ideals contained in it. Choosing generators gives an explicit bijection between
nonzero ideal elements and inverse-class ideals times global units. The principal ideal and
absolute field norm are preserved exactly, so the equivalence can reindex weighted series.
-/

noncomputable section
open NumberField Set
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions

section Generators
variable {R : Type*} [CommRing R]

/-- Actual nonzero elements of an integral ideal. -/
abbrev nonzeroIdealElements (b : Ideal R) := {a : R // a ∈ b ∧ a ≠ 0}

/-- Nonzero principal ideals contained in a fixed integral ideal. -/
abbrev principalIdealsInside (b : Ideal R) :=
  {J : Ideal R // J ≠ ⊥ ∧ J ≤ b ∧ Submodule.IsPrincipal J}

/-- Choose a generator from the proved principality of an actual ideal. -/
def principalInsideGenerator {b : Ideal R} (J : principalIdealsInside b) : R := by
  letI : Submodule.IsPrincipal J.1 := J.2.2.2
  exact Classical.choose (Submodule.IsPrincipal.principal (S := J.1))

/-- The chosen element generates exactly the specified principal ideal. -/
theorem span_principalInsideGenerator {b : Ideal R} (J : principalIdealsInside b) :
    Ideal.span {principalInsideGenerator J} = J.1 := by
  letI : Submodule.IsPrincipal J.1 := J.2.2.2
  exact (Classical.choose_spec (Submodule.IsPrincipal.principal (S := J.1))).symm

/-- A generator of a nonzero principal ideal is nonzero. -/
theorem principalInsideGenerator_ne_zero {b : Ideal R} (J : principalIdealsInside b) :
    principalInsideGenerator J ≠ 0 := by
  intro h
  apply J.2.1
  rw [← span_principalInsideGenerator J, h]
  exact Ideal.span_singleton_eq_bot.mpr rfl

/-- Containment of the principal ideal puts its generator in the fixed ideal. -/
theorem principalInsideGenerator_mem {b : Ideal R} (J : principalIdealsInside b) :
    principalInsideGenerator J ∈ b := by
  apply J.2.2.1
  rw [← span_principalInsideGenerator]
  exact Ideal.subset_span (Set.mem_singleton _)

variable [IsDomain R]

/-- Multiply the chosen generator by an actual global unit. -/
def principalIdealUnitElement (b : Ideal R) (p : principalIdealsInside b × Rˣ) :
    nonzeroIdealElements b :=
  ⟨(p.2 : R) * principalInsideGenerator p.1,
    b.mul_mem_left _ (principalInsideGenerator_mem p.1),
    mul_ne_zero p.2.ne_zero (principalInsideGenerator_ne_zero p.1)⟩

/-- Every element in a generator fiber spans precisely that fiber's ideal. -/
theorem span_principalIdealUnitElement (b : Ideal R) (p : principalIdealsInside b × Rˣ) :
    Ideal.span {(principalIdealUnitElement b p).1} = p.1.1 := by
  change Ideal.span {(p.2 : R) * principalInsideGenerator p.1} = p.1.1
  rw [Ideal.span_singleton_mul_left_unit p.2.isUnit, span_principalInsideGenerator]

/-- Nonzero cancellation makes the principal ideal and multiplying unit unique. -/
theorem principalIdealUnitElement_injective (b : Ideal R) :
    Function.Injective (principalIdealUnitElement b) := by
  rintro ⟨J, u⟩ ⟨L, v⟩ h
  have hJ : J = L := by
    apply Subtype.ext
    have hs := congrArg (fun a : nonzeroIdealElements b => Ideal.span {a.1}) h
    simpa only [span_principalIdealUnitElement] using hs
  subst L
  apply Prod.ext
  · rfl
  · apply Units.ext
    exact mul_right_cancel₀ (principalInsideGenerator_ne_zero J) (congrArg Subtype.val h)

/-- Every nonzero ideal element is a unit multiple of its principal ideal's chosen generator. -/
theorem principalIdealUnitElement_surjective (b : Ideal R) :
    Function.Surjective (principalIdealUnitElement b) := by
  intro a
  let J : principalIdealsInside b :=
    ⟨Ideal.span {a.1}, by
      intro hz
      exact a.2.2 (Ideal.span_singleton_eq_bot.mp hz),
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a.2.1), inferInstance⟩
  have hs : Ideal.span {principalInsideGenerator J} = Ideal.span {a.1} :=
    span_principalInsideGenerator J
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  refine ⟨(J, u), Subtype.ext ?_⟩
  change (u : R) * principalInsideGenerator J = a.1
  simpa only [mul_comm] using hu

/-- Nonzero ideal elements are exactly principal ideals in the ideal times their unit generators. -/
def nonzeroIdealElementsEquivPrincipalUnits (b : Ideal R) :
    nonzeroIdealElements b ≃ principalIdealsInside b × Rˣ :=
  (Equiv.ofBijective (principalIdealUnitElement b)
    ⟨principalIdealUnitElement_injective b, principalIdealUnitElement_surjective b⟩).symm

/-- The inverse equivalence retains the exact unit-times-generator formula. -/
theorem nonzeroIdealElementsEquivPrincipalUnits_symm_apply (b : Ideal R)
    (p : principalIdealsInside b × Rˣ) :
    ((nonzeroIdealElementsEquivPrincipalUnits b).symm p).1 =
      (p.2 : R) * principalInsideGenerator p.1 := rfl

end Generators

section IdealClasses
variable {K : Type*} [Field K] [NumberField K]
open scoped nonZeroDivisors

/-- The actual nonzero integral ideals in the inverse ordinary class of `b`. -/
abbrev inverseClassIntegralIdeals (b : (Ideal (𝓞 K))⁰) :=
  {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk0 b)⁻¹}

/-- Multiplication by `b` turns an ideal in its inverse class into a principal ideal inside `b`. -/
def inverseClassPrincipalIdeal (b : (Ideal (𝓞 K))⁰) (I : inverseClassIntegralIdeals b) :
    principalIdealsInside (b : Ideal (𝓞 K)) := by
  refine ⟨((I.1 * b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)), nonZeroDivisors.coe_ne_zero _,
    Ideal.mul_le_left, ?_⟩
  apply (ClassGroup.mk0_eq_one_iff (I.1 * b).2).mp
  rw [map_mul, I.2, inv_mul_cancel]

/-- Nonzero ideal cancellation makes multiplication into the principal class injective. -/
theorem inverseClassPrincipalIdeal_injective (b : (Ideal (𝓞 K))⁰) :
    Function.Injective (inverseClassPrincipalIdeal b) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun A : principalIdealsInside (b : Ideal (𝓞 K)) => A.1) h
  exact mul_right_cancel₀ (nonZeroDivisors.coe_ne_zero b) he

/-- Every principal ideal inside `b` has an integral quotient in the inverse class of `b`. -/
theorem inverseClassPrincipalIdeal_surjective (b : (Ideal (𝓞 K))⁰) :
    Function.Surjective (inverseClassPrincipalIdeal b) := by
  intro J
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr J.2.2.1
  have hI0 : I ≠ ⊥ := by
    intro hz
    apply J.2.1
    rw [hI, hz, Ideal.mul_bot]
  let I₀ : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩
  have hclass : ClassGroup.mk0 I₀ = (ClassGroup.mk0 b)⁻¹ := by
    apply ClassGroup.mk0_eq_mk0_inv_iff.mpr
    refine ⟨principalInsideGenerator J, principalInsideGenerator_ne_zero J, ?_⟩
    change I * (b : Ideal (𝓞 K)) = Ideal.span {principalInsideGenerator J}
    rw [span_principalInsideGenerator, hI, mul_comm]
  refine ⟨⟨I₀, hclass⟩, Subtype.ext ?_⟩
  change I * (b : Ideal (𝓞 K)) = J.1
  rw [hI, mul_comm]

/-- Multiplication by a nonzero ideal identifies its inverse class with the principal ideals inside it. -/
def inverseClassIntegralIdealsEquivPrincipal (b : (Ideal (𝓞 K))⁰) :
    inverseClassIntegralIdeals b ≃ principalIdealsInside (b : Ideal (𝓞 K)) :=
  Equiv.ofBijective (inverseClassPrincipalIdeal b)
    ⟨inverseClassPrincipalIdeal_injective b, inverseClassPrincipalIdeal_surjective b⟩

/-- A chosen generator of the actual principal product `I*b`. -/
def inverseClassGenerator (b : (Ideal (𝓞 K))⁰) (I : inverseClassIntegralIdeals b) : 𝓞 K :=
  principalInsideGenerator (inverseClassPrincipalIdeal b I)

/-- The chosen class-normalized generator spans exactly `I*b`. -/
theorem span_inverseClassGenerator (b : (Ideal (𝓞 K))⁰) (I : inverseClassIntegralIdeals b) :
    Ideal.span {inverseClassGenerator b I} = (I.1 : Ideal (𝓞 K)) * (b : Ideal (𝓞 K)) :=
  span_principalInsideGenerator (inverseClassPrincipalIdeal b I)

/-- The generator is nonzero and lies in the original integral ideal. -/
theorem inverseClassGenerator_mem_ne_zero (b : (Ideal (𝓞 K))⁰) (I : inverseClassIntegralIdeals b) :
    inverseClassGenerator b I ∈ (b : Ideal (𝓞 K)) ∧ inverseClassGenerator b I ≠ 0 :=
  ⟨principalInsideGenerator_mem (inverseClassPrincipalIdeal b I),
    principalInsideGenerator_ne_zero (inverseClassPrincipalIdeal b I)⟩

/-- Nonzero ideal elements are exactly inverse-class integral ideals times actual global units. -/
def nonzeroIdealElementsEquivClassUnits (b : (Ideal (𝓞 K))⁰) :
    nonzeroIdealElements (b : Ideal (𝓞 K)) ≃ inverseClassIntegralIdeals b × (𝓞 K)ˣ :=
  (nonzeroIdealElementsEquivPrincipalUnits (b : Ideal (𝓞 K))).trans
    (Equiv.prodCongr (inverseClassIntegralIdealsEquivPrincipal b).symm (Equiv.refl _))

/-- The orbit equivalence retains its exact unit-times-generator formula. -/
theorem nonzeroIdealElementsEquivClassUnits_symm_apply (b : (Ideal (𝓞 K))⁰)
    (I : inverseClassIntegralIdeals b) (u : (𝓞 K)ˣ) :
    ((nonzeroIdealElementsEquivClassUnits b).symm (I, u)).1 =
      (u : 𝓞 K) * inverseClassGenerator b I := rfl

/-- Each actual unit orbit generates the specified principal product. -/
theorem span_nonzeroIdealElementsEquivClassUnits_symm (b : (Ideal (𝓞 K))⁰)
    (I : inverseClassIntegralIdeals b) (u : (𝓞 K)ˣ) :
    Ideal.span {((nonzeroIdealElementsEquivClassUnits b).symm (I, u)).1} =
      (I.1 : Ideal (𝓞 K)) * (b : Ideal (𝓞 K)) := by
  rw [nonzeroIdealElementsEquivClassUnits_symm_apply,
    Ideal.span_singleton_mul_left_unit u.isUnit, span_inverseClassGenerator]

/-- The exact generator norm is the product of the two ideal norms. -/
theorem norm_inverseClassGenerator (b : (Ideal (𝓞 K))⁰) (I : inverseClassIntegralIdeals b) :
    (Algebra.norm ℤ (inverseClassGenerator b I)).natAbs =
      Ideal.absNorm (I.1 : Ideal (𝓞 K)) * Ideal.absNorm (b : Ideal (𝓞 K)) := by
  rw [← Ideal.absNorm_span_singleton, span_inverseClassGenerator, map_mul]

/-- Every element of the unit orbit has the same exact absolute field norm. -/
theorem norm_nonzeroIdealElementsEquivClassUnits_symm (b : (Ideal (𝓞 K))⁰)
    (I : inverseClassIntegralIdeals b) (u : (𝓞 K)ˣ) :
    (Algebra.norm ℤ ((nonzeroIdealElementsEquivClassUnits b).symm (I, u)).1).natAbs =
      Ideal.absNorm (I.1 : Ideal (𝓞 K)) * Ideal.absNorm (b : Ideal (𝓞 K)) := by
  rw [← Ideal.absNorm_span_singleton, span_nonzeroIdealElementsEquivClassUnits_symm,
    map_mul]

end IdealClasses

end GaloisForLFunctions.HeckeLFunctions
