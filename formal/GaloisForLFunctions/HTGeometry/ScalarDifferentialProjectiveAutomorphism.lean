import GaloisForLFunctions.HTGeometry.RatFuncProjectiveAutomorphism

/-!
# The ordinary projective endpoint of scalar differential automorphisms

This module isolates the ordinary field-theoretic final step in the classification of
automorphisms of a free scalar differential field.  Once an ambient automorphism and its inverse
send a generator into `C(u)`, it restricts to `C(u)` and hence acts by one unique projective linear
fractional transformation.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Restrict an ambient algebra equivalence to a simple intermediate field that it preserves in
both directions. -/
def restrictAlgEquivToAdjoinSingleton
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (σ : E ≃ₐ[C] E) (u : E)
    (hu : σ u ∈ IntermediateField.adjoin C {u})
    (huinv : σ.symm u ∈ IntermediateField.adjoin C {u}) :
    IntermediateField.adjoin C {u} ≃ₐ[C] IntermediateField.adjoin C {u} := by
  let S := IntermediateField.adjoin C {u}
  have hmap : S.map σ.toAlgHom = IntermediateField.adjoin C {σ u} := by
    dsimp [S]
    rw [IntermediateField.adjoin_map]
    congr 1
    ext x
    simp
  have hle : S.map σ.toAlgHom ≤ S := by
    rw [hmap, IntermediateField.adjoin_le_iff]
    simpa [S] using hu
  have hge : S ≤ S.map σ.toAlgHom := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨σ.symm u, ?_, ?_⟩
    · simpa [S] using huinv
    · exact σ.apply_symm_apply u
  have heq : S.map σ.toAlgHom = S := le_antisymm hle hge
  exact (S.equivMap σ.toAlgHom).trans (IntermediateField.equivOfEq heq)

@[simp]
theorem restrictAlgEquivToAdjoinSingleton_apply
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (σ : E ≃ₐ[C] E) (u : E)
    (hu : σ u ∈ IntermediateField.adjoin C {u})
    (huinv : σ.symm u ∈ IntermediateField.adjoin C {u})
    (z : IntermediateField.adjoin C {u}) :
    (restrictAlgEquivToAdjoinSingleton σ u hu huinv z : E) = σ z := by
  rfl

/-- Conjugate an automorphism preserving `C(u)` to an automorphism of `C(X)`. -/
def ratFuncAlgEquivOfAdjoinInvariant
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (σ : E ≃ₐ[C] E) (u : E) (htu : Transcendental C u)
    (hu : σ u ∈ IntermediateField.adjoin C {u})
    (huinv : σ.symm u ∈ IntermediateField.adjoin C {u}) :
    RatFunc C ≃ₐ[C] RatFunc C :=
  let e := RatFunc.algEquivOfTranscendental u htu
  e.trans ((restrictAlgEquivToAdjoinSingleton σ u hu huinv).trans e.symm)

theorem ratFuncAlgEquivOfAdjoinInvariant_image_X
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (σ : E ≃ₐ[C] E) (u : E) (htu : Transcendental C u)
    (hu : σ u ∈ IntermediateField.adjoin C {u})
    (huinv : σ.symm u ∈ IntermediateField.adjoin C {u}) :
    RatFunc.algEquivOfTranscendental u htu
        (ratFuncAlgEquivOfAdjoinInvariant σ u htu hu huinv RatFunc.X) =
      ⟨σ u, hu⟩ := by
  change RatFunc.algEquivOfTranscendental u htu
      ((RatFunc.algEquivOfTranscendental u htu).symm
        (restrictAlgEquivToAdjoinSingleton σ u hu huinv
          (RatFunc.algEquivOfTranscendental u htu RatFunc.X))) = _
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [restrictAlgEquivToAdjoinSingleton_apply]
  exact congrArg σ (RatFunc.algEquivOfTranscendental_X (f := u) htu)

/-- An ambient automorphism preserving `C(u)` sends `u` by a determinant-nonzero Möbius
transformation over `C`. -/
theorem exists_mobius_image_of_adjoin_invariant
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (σ : E ≃ₐ[C] E) (u : E) (htu : Transcendental C u)
    (hu : σ u ∈ IntermediateField.adjoin C {u})
    (huinv : σ.symm u ∈ IntermediateField.adjoin C {u}) :
    ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      σ u = (algebraMap C E a * u + algebraMap C E b) /
        (algebraMap C E c * u + algebraMap C E d) := by
  let g := ratFuncAlgEquivOfAdjoinInvariant σ u htu hu huinv
  obtain ⟨a, b, c, d, hdet, hX⟩ := RatFunc.exists_mobius_image_X g
  refine ⟨a, b, c, d, hdet, ?_⟩
  have hmap := congrArg
    (fun r : RatFunc C => ((RatFunc.algEquivOfTranscendental u htu r :
      IntermediateField.adjoin C {u}) : E)) hX
  dsimp [g] at hmap
  rw [ratFuncAlgEquivOfAdjoinInvariant_image_X] at hmap
  simpa [RatFunc.mobius, RatFunc.algEquivOfTranscendental_X,
    ← RatFunc.algebraMap_eq_C] using hmap

@[simp]
theorem coe_algEquivOfTranscendental_mobius
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (u : E) (htu : Transcendental C u) (a b c d : C) :
    ((RatFunc.algEquivOfTranscendental u htu (RatFunc.mobius a b c d) :
      IntermediateField.adjoin C {u}) : E) =
      (algebraMap C E a * u + algebraMap C E b) /
        (algebraMap C E c * u + algebraMap C E d) := by
  simp [RatFunc.mobius, RatFunc.algEquivOfTranscendental_X,
    -RatFunc.algebraMap_eq_C]

/-- Equality of determinant-nonzero Möbius evaluations at a transcendental element is exactly
equality of coefficient matrices up to a nonzero scalar. -/
theorem mobius_eval_eq_iff_exists_smul
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (u : E) (htu : Transcendental C u)
    {a b c d A B C' D : C}
    (habcd : a * d - b * c ≠ 0)
    (hABCD : A * D - B * C' ≠ 0) :
    (algebraMap C E a * u + algebraMap C E b) /
          (algebraMap C E c * u + algebraMap C E d) =
        (algebraMap C E A * u + algebraMap C E B) /
          (algebraMap C E C' * u + algebraMap C E D) ↔
      ∃ l : C, l ≠ 0 ∧ a = l * A ∧ b = l * B ∧ c = l * C' ∧ d = l * D := by
  rw [← coe_algEquivOfTranscendental_mobius u htu a b c d,
    ← coe_algEquivOfTranscendental_mobius u htu A B C' D]
  have hinj : Function.Injective
      (fun r : RatFunc C => ((RatFunc.algEquivOfTranscendental u htu r :
        IntermediateField.adjoin C {u}) : E)) := by
    exact Subtype.val_injective.comp
      (RatFunc.algEquivOfTranscendental u htu).injective
  rw [hinj.eq_iff]
  exact RatFunc.mobius_eq_iff_exists_smul habcd hABCD

/-- Complete ordinary projective classifier for an ambient automorphism preserving `C(u)`: the
image of `u` has a determinant-nonzero Möbius presentation unique up to one nonzero scalar. -/
theorem exists_unique_mobius_image_of_adjoin_invariant
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (σ : E ≃ₐ[C] E) (u : E) (htu : Transcendental C u)
    (hu : σ u ∈ IntermediateField.adjoin C {u})
    (huinv : σ.symm u ∈ IntermediateField.adjoin C {u}) :
    ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      σ u = (algebraMap C E a * u + algebraMap C E b) /
        (algebraMap C E c * u + algebraMap C E d) ∧
      ∀ A B C' D : C, A * D - B * C' ≠ 0 →
        σ u = (algebraMap C E A * u + algebraMap C E B) /
          (algebraMap C E C' * u + algebraMap C E D) →
        ∃ l : C, l ≠ 0 ∧ A = l * a ∧ B = l * b ∧ C' = l * c ∧ D = l * d := by
  obtain ⟨a, b, c, d, hdet, himage⟩ :=
    exists_mobius_image_of_adjoin_invariant σ u htu hu huinv
  refine ⟨a, b, c, d, hdet, himage, ?_⟩
  intro A B C' D hdet' himage'
  exact (mobius_eval_eq_iff_exists_smul u htu hdet' hdet).mp
    (himage'.symm.trans himage)

end

end GaloisForLFunctions
