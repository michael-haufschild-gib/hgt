import GaloisForLFunctions.HTGeometry.FiniteRightFactorSpecialization
import GaloisForLFunctions.HTGeometry.IntermediateFieldTensorFraction

/-!
# Coboundary descent from a concrete field compositum

Let `A` and `B` be linearly disjoint intermediate fields in a common overfield.  Suppose an
ambient automorphism restricts to `sigma` on `A` and fixes `B` pointwise.  Any additive
coboundary in the compositum `A B` whose right-hand side belongs to `A` then descends to an
additive coboundary already in `A`.

The proof first presents the compositum certificate as a quotient in `A tensor B`, clears its
denominator, and then invokes finite-right-factor specialization.  Thus neither intermediate field
is assumed finitely generated.
-/

open scoped TensorProduct

namespace GaloisForLFunctions

noncomputable section

/-- Tensor multiplication intertwines a left-factor action with the corresponding ambient
automorphism, provided the latter fixes the right factor. -/
theorem intermediateFieldTensorMulMap_tensorLeftAction
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E)
    (T : E ≃ₐ[C] E) (sigma : A ≃ₐ[C] A)
    (hleft : ∀ a : A, T (a : E) = (sigma a : E))
    (hright : ∀ b : B, T (b : E) = (b : E))
    (x : A ⊗[C] B) :
    intermediateFieldTensorMulMap C E A B
        (tensorLeftAction C A B sigma x) =
      T (intermediateFieldTensorMulMap C E A B x) := by
  induction x with
  | zero => simp
  | tmul a b =>
      simp only [tensorLeftAction_tmul,
        intermediateFieldTensorMulMap_tmul, map_mul, hleft, hright]
  | add x y hx hy => simp [hx, hy]

/-- **Compositum coboundary descent.**  Under linear disjointness, an ambient additive
coboundary with certificate in `A sup B`, left-hand side in `A`, and a translation which fixes
`B`, already has a certificate in `A`. -/
theorem exists_left_coboundary_of_mem_intermediateField_sup
    (C E : Type*) [Field C] [IsAlgClosed C] [Field E] [Algebra C E]
    (A B : IntermediateField C E)
    (hAB : A.LinearDisjoint B)
    (T : E ≃ₐ[C] E) (sigma : A ≃ₐ[C] A)
    (hleft : ∀ a : A, T (a : E) = (sigma a : E))
    (hright : ∀ b : B, T (b : E) = (b : E))
    (a : A) {g : E} (hg : g ∈ A ⊔ B)
    (hcoboundary : T g - g = (a : E)) :
    ∃ u : A, sigma u - u = a := by
  let mu := intermediateFieldTensorMulMap C E A B
  have hmu : Function.Injective mu :=
    intermediateFieldTensorMulMap_injective_of_linearDisjoint C E A B hAB
  obtain ⟨N, D, hD, hgfrac⟩ :=
    exists_tensor_fraction_of_mem_sup C E A B hmu hg
  have hmuD : mu D ≠ 0 := hmu.ne hD
  have hTmuD : T (mu D) ≠ 0 := T.injective.ne hmuD
  have hquotient :
      T (mu N) / T (mu D) - mu N / mu D = (a : E) := by
    calc
      T (mu N) / T (mu D) - mu N / mu D =
          T (mu N / mu D) - mu N / mu D := by
        rw [map_div₀]
      _ = T g - g := by rw [hgfrac]
      _ = (a : E) := hcoboundary
  have hcross :
      T (mu N) * mu D - mu N * T (mu D) =
        (a : E) * T (mu D) * mu D := by
    field_simp [hmuD, hTmuD] at hquotient
    ring_nf at hquotient ⊢
    exact hquotient
  have htensor : tensorLeftAction C A B sigma N * D -
        N * tensorLeftAction C A B sigma D =
      (a ⊗ₜ[C] (1 : B)) * tensorLeftAction C A B sigma D * D := by
    apply hmu
    simpa only [map_sub, map_mul,
      intermediateFieldTensorMulMap_tensorLeftAction,
      intermediateFieldTensorMulMap_tmul, Subtype.coe_one, mul_one] using hcross
  exact exists_left_coboundary_of_arbitrary_right_tensor_fraction_identity
    C A B sigma a N D hD htensor

end

end GaloisForLFunctions
