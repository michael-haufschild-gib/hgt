import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.FractionalIdeal.Norm

/-!
# Fractional-ideal elements as ideal-class unit orbits

Each nonzero element of an invertible fractional ideal determines an
integral ideal in its inverse ordinary class. Choosing generators of
the principal products gives a bijection with those ideals times global
units. Cancellation proves uniqueness; fractional-ideal norm multiplicativity
retains the exact field norm throughout this reindexing.
-/

noncomputable section
open NumberField
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- Actual nonzero elements of a fractional ideal in the number field. -/
abbrev nonzeroFractionalIdealElements (J : FI) := {a : K // a ∈ J ∧ a ≠ 0}

/-- Nonzero integral ideals in the inverse ordinary class of a fractional ideal. -/
abbrev fractionalInverseClassIntegralIdeals (J : FIˣ) :=
  {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk K J)⁻¹}

/-- The product of an inverse-class ideal with the fractional base ideal is principal. -/
theorem fractionalInverseClassProduct_isPrincipal (J : FIˣ)
    (I : fractionalInverseClassIntegralIdeals J) :
    (↑(((I.1 : Ideal (𝓞 K)) : FI) * (J : FI)) : Submodule (𝓞 K) K).IsPrincipal := by
  change (↑(↑(FractionalIdeal.mk0 K I.1 * J) : FI) : Submodule (𝓞 K) K).IsPrincipal
  apply ClassGroup.mk_eq_one_iff.mp
  rw [map_mul, ClassGroup.mk_mk0, I.2, inv_mul_cancel]

/-- Choose a generator of the actual principal product of the two ideals. -/
def fractionalClassGenerator (J : FIˣ) (I : fractionalInverseClassIntegralIdeals J) : K :=
  (FractionalIdeal.isPrincipal_iff _ |>.mp
    (fractionalInverseClassProduct_isPrincipal J I)).choose

theorem span_fractionalClassGenerator (J : FIˣ) (I : fractionalInverseClassIntegralIdeals J) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (fractionalClassGenerator J I) =
      ((I.1 : Ideal (𝓞 K)) : FI) * (J : FI) :=
  (FractionalIdeal.isPrincipal_iff _ |>.mp
    (fractionalInverseClassProduct_isPrincipal J I)).choose_spec.symm

theorem fractionalClassGenerator_ne_zero (J : FIˣ) (I : fractionalInverseClassIntegralIdeals J) :
    fractionalClassGenerator J I ≠ 0 := by
  apply (FractionalIdeal.spanSingleton_ne_zero_iff (S := nonZeroDivisors (𝓞 K))).mp
  rw [span_fractionalClassGenerator]
  exact mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero I.1))
    J.ne_zero

theorem fractionalClassGenerator_mem (J : FIˣ) (I : fractionalInverseClassIntegralIdeals J) :
    fractionalClassGenerator J I ∈ (J : FI) := by
  apply FractionalIdeal.spanSingleton_le_iff_mem.mp
  rw [span_fractionalClassGenerator]
  exact (mul_le_mul_left (FractionalIdeal.coeIdeal_le_one (I := (I.1 : Ideal (𝓞 K))))
    (J : FI)).trans_eq (one_mul _)

/-- The chosen generator determines its integral ideal, by cancellation of the base ideal. -/
theorem fractionalClassGenerator_injective (J : FIˣ) :
    Function.Injective (fractionalClassGenerator J) := by
  intro I L h
  apply Subtype.ext
  apply Subtype.ext
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change ((I.1 : Ideal (𝓞 K)) : FI) = ((L.1 : Ideal (𝓞 K)) : FI)
  apply mul_right_cancel₀ J.ne_zero
  rw [← span_fractionalClassGenerator, ← span_fractionalClassGenerator, h]

/-- Selected generators embed the inverse ideal class in the countable number field. -/
theorem fractionalInverseClassIntegralIdeals_countable (J : FIˣ) :
    Countable (fractionalInverseClassIntegralIdeals J) := by
  letI : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.symm.toEquiv
  exact (fractionalClassGenerator_injective J).countable

/-- Every nonzero element determines an integral ideal in the inverse fractional class. -/
theorem exists_fractionalInverseClassIdeal (J : FIˣ) (a : nonzeroFractionalIdealElements (J : FI)) :
    ∃ I : fractionalInverseClassIntegralIdeals J,
      ((I.1 : Ideal (𝓞 K)) : FI) * (J : FI) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a.1 := by
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a.1 * (J : FI)⁻¹ ≤ 1 := by
    calc
      _ ≤ (J : FI) * (J : FI)⁻¹ :=
        mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr a.2.1) _
      _ = 1 := mul_inv_cancel₀ J.ne_zero
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hIJ : (I : FI) * (J : FI) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a.1 := by
    rw [hI, mul_assoc, inv_mul_cancel₀ J.ne_zero, mul_one]
  have hI0 : I ≠ ⊥ := by
    intro h0
    have hs : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a.1 = 0 := by
      rw [← hIJ, h0, FractionalIdeal.coeIdeal_bot, zero_mul]
    exact a.2.2 (FractionalIdeal.spanSingleton_eq_zero_iff.mp hs)
  let I₀ : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩
  have hclass : ClassGroup.mk0 I₀ = (ClassGroup.mk K J)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← ClassGroup.mk_mk0 (K := K), ← map_mul]
    apply ClassGroup.mk_eq_one_iff.mpr
    change (↑((I : FI) * (J : FI)) : Submodule (𝓞 K) K).IsPrincipal
    exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨a.1, hIJ⟩
  exact ⟨⟨I₀, hclass⟩, hIJ⟩

/-- Multiply each chosen class generator by a global unit. -/
def fractionalClassUnitElement (J : FIˣ)
    (p : fractionalInverseClassIntegralIdeals J × (𝓞 K)ˣ) :
    nonzeroFractionalIdealElements (J : FI) :=
  ⟨((p.2 : 𝓞 K) : K) * fractionalClassGenerator J p.1, by
    have h := (J : FI).coeToSubmodule.smul_mem (p.2 : 𝓞 K)
      (fractionalClassGenerator_mem J p.1)
    exact h,
    mul_ne_zero (by exact_mod_cast p.2.ne_zero) (fractionalClassGenerator_ne_zero J p.1)⟩

/-- Every unit multiple generates exactly the specified fractional principal product. -/
theorem span_fractionalClassUnitElement (J : FIˣ)
    (p : fractionalInverseClassIntegralIdeals J × (𝓞 K)ˣ) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (fractionalClassUnitElement J p).1 =
      ((p.1.1 : Ideal (𝓞 K)) : FI) * (J : FI) := by
  rw [← span_fractionalClassGenerator]
  apply (FractionalIdeal.spanSingleton_eq_spanSingleton).mpr
  refine ⟨p.2⁻¹, ?_⟩
  change (((p.2⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
    (((p.2 : 𝓞 K) : K) * fractionalClassGenerator J p.1) = fractionalClassGenerator J p.1
  have hu : (((p.2⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * ((p.2 : 𝓞 K) : K) = 1 := by
    exact_mod_cast Units.inv_mul p.2
  rw [← mul_assoc, hu, one_mul]

/-- Cancellation of principal products and generators makes both class and unit unique. -/
theorem fractionalClassUnitElement_injective (J : FIˣ) :
    Function.Injective (fractionalClassUnitElement J) := by
  rintro ⟨I, u⟩ ⟨L, v⟩ h
  have hIL : I = L := by
    apply Subtype.ext
    apply Subtype.ext
    apply FractionalIdeal.coeIdeal_injective (K := K)
    change ((I.1 : Ideal (𝓞 K)) : FI) = ((L.1 : Ideal (𝓞 K)) : FI)
    apply mul_right_cancel₀ J.ne_zero
    rw [← span_fractionalClassUnitElement J (I, u), ← span_fractionalClassUnitElement J (L, v), h]
  subst L
  apply Prod.ext
  · rfl
  · apply Units.ext
    have hu : ((u : 𝓞 K) : K) = ((v : 𝓞 K) : K) :=
      mul_right_cancel₀ (fractionalClassGenerator_ne_zero J I) (congrArg Subtype.val h)
    exact_mod_cast hu

/-- Every nonzero fractional-ideal element is a global-unit multiple of its class generator. -/
theorem fractionalClassUnitElement_surjective (J : FIˣ) :
    Function.Surjective (fractionalClassUnitElement J) := by
  intro a
  obtain ⟨I, hI⟩ := exists_fractionalInverseClassIdeal J a
  have hs : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (fractionalClassGenerator J I) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a.1 :=
    (span_fractionalClassGenerator J I).trans hI
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hs
  exact ⟨(I, u), Subtype.ext hu⟩

/-- Nonzero elements of an invertible fractional ideal are its inverse-class ideals times global units. -/
def nonzeroFractionalIdealElementsEquivClassUnits (J : FIˣ) :
    nonzeroFractionalIdealElements (J : FI) ≃
      fractionalInverseClassIntegralIdeals J × (𝓞 K)ˣ :=
  (Equiv.ofBijective (fractionalClassUnitElement J)
    ⟨fractionalClassUnitElement_injective J, fractionalClassUnitElement_surjective J⟩).symm

theorem nonzeroFractionalIdealElementsEquivClassUnits_symm_apply (J : FIˣ)
    (I : fractionalInverseClassIntegralIdeals J) (u : (𝓞 K)ˣ) :
    ((nonzeroFractionalIdealElementsEquivClassUnits J).symm (I, u)).1 =
      ((u : 𝓞 K) : K) * fractionalClassGenerator J I := rfl

/-- The exact generator norm is the integral ideal norm times the fractional base norm. -/
theorem norm_fractionalClassGenerator (J : FIˣ) (I : fractionalInverseClassIntegralIdeals J) :
    |Algebra.norm ℚ (fractionalClassGenerator J I)| =
      (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℚ) * FractionalIdeal.absNorm (J : FI) := by
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), span_fractionalClassGenerator,
    map_mul, FractionalIdeal.coeIdeal_absNorm]

/-- Every element of a global-unit orbit has the same exact fractional norm. -/
theorem norm_nonzeroFractionalIdealElementsEquivClassUnits_symm (J : FIˣ)
    (I : fractionalInverseClassIntegralIdeals J) (u : (𝓞 K)ˣ) :
    |Algebra.norm ℚ ((nonzeroFractionalIdealElementsEquivClassUnits J).symm (I, u)).1| =
      (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℚ) * FractionalIdeal.absNorm (J : FI) := by
  change |Algebra.norm ℚ (fractionalClassUnitElement J (I, u)).1| = _
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), span_fractionalClassUnitElement,
    map_mul, FractionalIdeal.coeIdeal_absNorm]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.nonzeroFractionalIdealElementsEquivClassUnits
#print axioms GaloisForLFunctions.HTGeometry.norm_nonzeroFractionalIdealElementsEquivClassUnits_symm
