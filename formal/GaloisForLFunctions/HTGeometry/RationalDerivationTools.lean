import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Rational-linear derivations of a fraction field

In characteristic zero every additive derivation is automatically `ℚ`-linear, so the derivation of
a differential field can be handled as a `ℚ`-derivation.  This file provides the three tools used
to transport statements about such derivations from a domain to its fraction field:

* `ratOfIntDerivation`, upgrading an integer-linear derivation of a `ℚ`-algebra;
* `derivationEqualizerSubfield`, the subfield on which two derivations agree, together with the
  fact that agreement on the image of the domain forces agreement everywhere;
* `derivationStableOf` and `derivationIntertwinerOf`, the intermediate-field loci used to propagate
  stability and intertwining from generators to the whole field, allowing a base field that is not
  killed by the derivation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An integer-linear derivation of a `ℚ`-algebra is `ℚ`-linear. -/
def ratOfIntDerivation (A : Type*) [CommRing A] [Algebra ℚ A] (D : Derivation ℤ A A) :
    Derivation ℚ A A :=
  Derivation.mk' D.toLinearMap.toAddMonoidHom.toRatLinearMap
    (fun a b => by
      have h := D.leibniz a b
      simp only [smul_eq_mul] at h ⊢
      exact h)

@[simp] theorem ratOfIntDerivation_apply {A : Type*} [CommRing A] [Algebra ℚ A]
    (D : Derivation ℤ A A) (a : A) : ratOfIntDerivation A D a = D a := rfl

section Equalizer

variable {F : Type*} [Field F] [Algebra ℚ F]

/-- The subfield on which two derivations agree. -/
def derivationEqualizerSubfield (D₁ D₂ : Derivation ℚ F F) : Subfield F where
  carrier := {x | D₁ x = D₂ x}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, map_add, hx, hy]
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Derivation.leibniz, Derivation.leibniz, hx, hy]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_neg, map_neg, hx]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Derivation.leibniz_inv, Derivation.leibniz_inv, hx]

/-- **Derivations agreeing on the domain agree on its fraction field.** -/
theorem derivation_eq_of_agree_on_algebraMap {A : Type*} [CommRing A] [IsDomain A]
    [Algebra A F] [IsFractionRing A F] (D₁ D₂ : Derivation ℚ F F)
    (h : ∀ a : A, D₁ (algebraMap A F a) = D₂ (algebraMap A F a)) : D₁ = D₂ := by
  have hall : ∀ x : F, x ∈ derivationEqualizerSubfield D₁ D₂ := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    exact div_mem (h a) (h b)
  exact Derivation.ext fun x => hall x

end Equalizer

section Stability

variable {C E : Type*} [Field C] [Field E] [Algebra C E] [Algebra ℚ E]

/-- Elements of an intermediate field whose derivative stays inside it, for a derivation that need
not kill the base field. -/
def derivationStableOf (L : IntermediateField C E) (D : Derivation ℚ E E)
    (hbase : ∀ c : C, D (algebraMap C E c) ∈ L) : IntermediateField C E where
  carrier := {y | y ∈ L ∧ D y ∈ L}
  zero_mem' := ⟨zero_mem L, by rw [map_zero]; exact zero_mem L⟩
  one_mem' := ⟨one_mem L, by rw [Derivation.map_one_eq_zero]; exact zero_mem L⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨add_mem hx.1 hy.1, by rw [map_add]; exact add_mem hx.2 hy.2⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem hx.1 hy.2) (mul_mem hy.1 hx.2)
  algebraMap_mem' := fun c => ⟨algebraMap_mem L c, hbase c⟩
  inv_mem' := by
    intro x hx
    refine ⟨inv_mem hx.1, ?_⟩
    rw [Derivation.leibniz_inv, smul_eq_mul]
    exact mul_mem (neg_mem (pow_mem (inv_mem hx.1) 2)) hx.2

theorem adjoin_le_derivationStableOf {S : Set E} {L : IntermediateField C E}
    {D : Derivation ℚ E E} {hbase : ∀ c : C, D (algebraMap C E c) ∈ L}
    (h : ∀ x ∈ S, x ∈ L ∧ D x ∈ L) :
    IntermediateField.adjoin C S ≤ derivationStableOf L D hbase := by
  rw [IntermediateField.adjoin_le_iff]
  exact fun x hx => h x hx

end Stability

section Intertwining

variable {C E E' : Type*} [Field C] [Field E] [Field E'] [Algebra C E] [Algebra C E']
  [Algebra ℚ E] [Algebra ℚ E']

/-- The locus where an algebra homomorphism intertwines two derivations, for derivations that need
not kill the base field. -/
def derivationIntertwinerOf (T : E →ₐ[C] E') (D₁ : Derivation ℚ E E) (D₂ : Derivation ℚ E' E')
    (hbase : ∀ c : C, D₂ (T (algebraMap C E c)) = T (D₁ (algebraMap C E c))) :
    IntermediateField C E where
  carrier := {f | D₂ (T f) = T (D₁ f)}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, map_add, map_add, hx, hy, map_add]
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hx, hy, map_add,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
  algebraMap_mem' := hbase
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_inv₀, Derivation.leibniz_inv, Derivation.leibniz_inv, hx, smul_eq_mul, smul_eq_mul,
      map_mul, map_neg, map_pow, map_inv₀]

end Intertwining

end

end GaloisForLFunctions.HTGeometry
