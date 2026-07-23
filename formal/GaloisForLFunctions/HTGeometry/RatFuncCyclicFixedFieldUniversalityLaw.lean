import GaloisForLFunctions.HTGeometry.RatFuncProjectiveCyclicClassification
import GaloisForLFunctions.HTGeometry.ScalarDifferentialTorsor
import GaloisForLFunctions.HTGeometry.RatFuncTranslationFixedField

/-!
# Universal cyclic fixed-field classification on a rational coordinate

Over an algebraically closed characteristic-zero field, every coefficient-fixing automorphism of
`K(X)` has one of four conjugacy types.  Combining projective normal form with the exact scale and
translation fixed fields determines its complete cyclic fixed locus in the same four branches.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

private theorem ratFunc_fixed_iff_conjugate_fixed
    (e h a : RatFunc K ≃ₐ[K] RatFunc K)
    (ha : h.symm * e * h = a) (r : RatFunc K) :
    e r = r ↔ a (h.symm r) = h.symm r := by
  constructor
  · intro hr
    calc
      a (h.symm r) = (h.symm * e * h) (h.symm r) := by rw [ha]
      _ = h.symm (e r) := by simp
      _ = h.symm r := by rw [hr]
  · intro hr
    apply h.symm.injective
    calc
      h.symm (e r) = (h.symm * e * h) (h.symm r) := by simp
      _ = a (h.symm r) := by rw [ha]
      _ = h.symm r := hr

private theorem ratFuncUnitScaleEquiv_fixed_iff_mem_powerField
    (u : Kˣ) {N : ℕ} (hN : 0 < N) (hu : orderOf u = N) (r : RatFunc K) :
    ratFuncUnitScaleEquiv u r = r ↔ r ∈ ratFuncPowerField K N := by
  rw [← mem_fixedField_zpowers_iff]
  change r ∈ IntermediateField.fixedField
      (Subgroup.zpowers (ratFuncUnitScaleAction u)) ↔ _
  rw [fixedField_zpowers_ratFuncUnitScaleAction u hN hu]

private theorem ratFuncUnitScaleEquiv_fixed_iff_constant_of_infinite_order
    (u : Kˣ) (hu : orderOf u = 0) (r : RatFunc K) :
    ratFuncUnitScaleEquiv u r = r ↔ ∃ c : K, r = RatFunc.C c := by
  rw [← mem_fixedField_zpowers_iff]
  change r ∈ IntermediateField.fixedField
      (Subgroup.zpowers (ratFuncUnitScaleAction u)) ↔ _
  rw [fixedField_zpowers_ratFuncUnitScaleAction_of_infinite_order u hu,
    IntermediateField.mem_bot]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

private theorem ratFuncTranslationEquiv_one_fixed_iff_constant
    [CharZero K] (r : RatFunc K) :
    ratFuncTranslationEquiv 1 r = r ↔ ∃ c : K, r = RatFunc.C c := by
  rw [← mem_fixedField_zpowers_iff]
  change r ∈ IntermediateField.fixedField
      (Subgroup.zpowers
        (ratFuncTranslationAction (Multiplicative.ofAdd (1 : K)))) ↔ _
  rw [fixedField_zpowers_ratFuncTranslationAction (1 : K) one_ne_zero,
    IntermediateField.mem_bot]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

/-- **Rational-coordinate cyclic fixed-field universality law.**  Every coefficient-fixing
automorphism of `K(X)` is either the identity; a conjugate of a finite nontrivial scaling, whose
fixed elements are exactly a conjugated power field; or an infinite scaling/translation conjugate,
whose fixed elements are exactly the conjugated constants. -/
theorem ratFuncAlgEquiv_cyclicFixedFieldUniversality
    [IsAlgClosed K] [CharZero K] (e : RatFunc K ≃ₐ[K] RatFunc K) :
    e = AlgEquiv.refl ∨
      (∃ (h : RatFunc K ≃ₐ[K] RatFunc K) (u : Kˣ) (N : ℕ),
        2 ≤ N ∧ orderOf u = N ∧
          h.symm * e * h = ratFuncUnitScaleEquiv u ∧
          ∀ r : RatFunc K,
            e r = r ↔ h.symm r ∈ ratFuncPowerField K N) ∨
      (∃ (h : RatFunc K ≃ₐ[K] RatFunc K) (u : Kˣ),
        orderOf u = 0 ∧
          h.symm * e * h = ratFuncUnitScaleEquiv u ∧
          ∀ r : RatFunc K,
            e r = r ↔ ∃ c : K, h.symm r = RatFunc.C c) ∨
      (∃ h : RatFunc K ≃ₐ[K] RatFunc K,
        h.symm * e * h = ratFuncTranslationEquiv 1 ∧
          ∀ r : RatFunc K,
            e r = r ↔ ∃ c : K, h.symm r = RatFunc.C c) := by
  rcases ratFuncAlgEquiv_cyclicNormalForm e with he | hfinite | hinfinite | htranslation
  · exact Or.inl he
  · right
    left
    obtain ⟨h, u, N, hN, hu, heq⟩ := hfinite
    refine ⟨h, u, N, hN, hu, heq, fun r ↦ ?_⟩
    rw [ratFunc_fixed_iff_conjugate_fixed e h (ratFuncUnitScaleEquiv u) heq r,
      ratFuncUnitScaleEquiv_fixed_iff_mem_powerField u (by omega) hu]
  · right
    right
    left
    obtain ⟨h, u, hu, heq⟩ := hinfinite
    refine ⟨h, u, hu, heq, fun r ↦ ?_⟩
    rw [ratFunc_fixed_iff_conjugate_fixed e h (ratFuncUnitScaleEquiv u) heq r,
      ratFuncUnitScaleEquiv_fixed_iff_constant_of_infinite_order u hu]
  · right
    right
    right
    obtain ⟨h, heq⟩ := htranslation
    refine ⟨h, heq, fun r ↦ ?_⟩
    rw [ratFunc_fixed_iff_conjugate_fixed e h (ratFuncTranslationEquiv 1) heq r,
      ratFuncTranslationEquiv_one_fixed_iff_constant]

end

end GaloisForLFunctions.HTGeometry
