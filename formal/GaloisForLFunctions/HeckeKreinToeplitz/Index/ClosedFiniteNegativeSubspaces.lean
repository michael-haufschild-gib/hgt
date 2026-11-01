import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeDirections
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Closed subspaces of a Hilbert space with finitely many negative directions

The purely positive part splits off by Hilbert orthogonal projection. Its
orthogonal remainder injects into the negative factor, so is finite-dimensional.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Positive coordinates whose negative coordinate can vanish inside `W`. -/
def positiveKernel (W : Submodule ℂ (H × E)) : Submodule ℂ H :=
  W.comap (LinearMap.inl ℂ H E)

/-- The remainder after splitting off the purely positive directions. -/
def finitePart (W : Submodule ℂ (H × E)) : Submodule ℂ (H × E) :=
  W ⊓ (positiveKernel W)ᗮ.comap (LinearMap.fst ℂ H E)

theorem finitePart_snd_eq_zero (W : Submodule ℂ (H × E))
    (v : finitePart W) (hv : (v : H × E).2 = 0) : v = 0 := by
  have hx : (v : H × E).1 ∈ positiveKernel W := by
    change ((v : H × E).1, 0) ∈ W
    have heq : ((v : H × E).1, 0) = (v : H × E) := Prod.ext rfl hv.symm
    rw [heq]
    exact v.property.1
  have ho := (Submodule.mem_orthogonal (positiveKernel W) _).mp v.property.2 _ hx
  have hz : (v : H × E).1 = 0 := inner_self_eq_zero.mp ho
  exact Subtype.ext (Prod.ext hz hv)

/-- The finite remainder embeds into the negative Hilbert factor. -/
def finitePartToNegative (W : Submodule ℂ (H × E)) : finitePart W →ₗ[ℂ] E :=
  (LinearMap.snd ℂ H E).comp (finitePart W).subtype

theorem finitePartToNegative_injective (W : Submodule ℂ (H × E)) :
    Function.Injective (finitePartToNegative W) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply finitePart_snd_eq_zero W
  change finitePartToNegative W (u - v) = 0
  rw [map_sub, huv, sub_self]

instance finiteDimensional_finitePart [FiniteDimensional ℂ E]
    (W : Submodule ℂ (H × E)) : FiniteDimensional ℂ (finitePart W) :=
  Module.Finite.of_injective (finitePartToNegative W) (finitePartToNegative_injective W)

theorem finrank_finitePart_le [FiniteDimensional ℂ E]
    (W : Submodule ℂ (H × E)) :
    Module.finrank ℂ (finitePart W) ≤ Module.finrank ℂ E :=
  LinearMap.finrank_le_finrank_of_injective (finitePartToNegative_injective W)

theorem isClosed_positiveKernel (W : Submodule ℂ (H × E))
    (hW : IsClosed (W : Set (H × E))) : IsClosed (positiveKernel W : Set H) :=
  hW.preimage (ContinuousLinearMap.inl ℂ H E).continuous

variable (W : Submodule ℂ (H × E)) [(positiveKernel W).HasOrthogonalProjection]

/-- The positive coordinate of the orthogonal splitting. -/
def positiveCoordinate : W →L[ℂ] positiveKernel W :=
  (positiveKernel W).orthogonalProjectionOnto.comp
    ((ContinuousLinearMap.fst ℂ H E).comp W.subtypeL)

private def remainderMap : W →ₗ[ℂ] H × E :=
  W.subtype - (LinearMap.inl ℂ H E).comp
    ((positiveKernel W).subtype.comp (positiveCoordinate W).toLinearMap)

private theorem remainderMap_mem (w : W) : remainderMap W w ∈ finitePart W := by
  constructor
  · exact W.sub_mem w.property (positiveCoordinate W w).property
  · exact (positiveKernel W).sub_starProjection_mem_orthogonal (w : H × E).1

/-- The finite coordinate of the orthogonal splitting. -/
def finiteCoordinate : W →ₗ[ℂ] finitePart W :=
  (remainderMap W).codRestrict (finitePart W) (remainderMap_mem W)

@[simp] theorem finiteCoordinate_coe (w : W) :
    (finiteCoordinate W w : H × E) =
      (w : H × E) - ((positiveCoordinate W w : H), 0) := rfl

private theorem positiveCoordinate_inl (u : positiveKernel W) :
    positiveCoordinate W ⟨((u : H), 0), u.property⟩ = u := by
  apply Subtype.ext
  exact (Submodule.starProjection_eq_self_iff).mpr u.property

private theorem positiveCoordinate_finite (v : finitePart W) :
    positiveCoordinate W ⟨(v : H × E), v.property.1⟩ = 0 := by
  change (positiveKernel W).orthogonalProjectionOnto (v : H × E).1 = 0
  exact (Submodule.orthogonalProjectionOnto_eq_zero_iff
    (K := positiveKernel W) (v := (v : H × E).1)).mpr v.property.2

/-- Split a subspace into its positive Hilbert part and finite remainder. -/
def subspaceSplitting : W ≃ₗ[ℂ] positiveKernel W × finitePart W where
  toFun w := (positiveCoordinate W w, finiteCoordinate W w)
  invFun p := ⟨((p.1 : H), 0) + (p.2 : H × E),
    W.add_mem p.1.property p.2.property.1⟩
  left_inv w := by
    apply Subtype.ext
    change ((positiveCoordinate W w : H), 0) +
      ((w : H × E) - ((positiveCoordinate W w : H), 0)) = (w : H × E)
    abel
  right_inv p := by
    have hp : positiveCoordinate W
        ⟨((p.1 : H), 0) + (p.2 : H × E), W.add_mem p.1.property p.2.property.1⟩ = p.1 := by
      change positiveCoordinate W
        (⟨((p.1 : H), 0), p.1.property⟩ + ⟨(p.2 : H × E), p.2.property.1⟩) = p.1
      rw [map_add, positiveCoordinate_inl, positiveCoordinate_finite, add_zero]
    apply Prod.ext hp
    apply Subtype.ext
    change ((p.1 : H), 0) + (p.2 : H × E) -
      ((positiveCoordinate W _ : H), 0) = (p.2 : H × E)
    rw [hp]
    exact add_sub_cancel_left _ _
  map_add' u v := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' a u := Prod.ext (map_smul _ _ _) (map_smul _ _ _)

omit [(positiveKernel W).HasOrthogonalProjection] in
/-- Positive and finite summands are orthogonal for the indefinite form. -/
theorem pairing_positive_finite (u : positiveKernel W) (v : finitePart W) :
    pairing ((u : H), (0 : E)) (v : H × E) = 0 := by
  change inner ℂ (u : H) (v : H × E).1 - inner ℂ (0 : E) (v : H × E).2 = 0
  rw [inner_zero_left, sub_zero]
  exact (Submodule.mem_orthogonal (positiveKernel W) _).mp v.property.2 _ u.property

theorem pairing_subspaceSplitting (u v : W) :
    pairing (u : H × E) (v : H × E) =
      inner ℂ (positiveCoordinate W u : H) (positiveCoordinate W v : H) +
        pairing (finiteCoordinate W u : H × E) (finiteCoordinate W v : H × E) := by
  have hu : (u : H × E) = ((positiveCoordinate W u : H), 0) +
      (finiteCoordinate W u : H × E) := by
    rw [finiteCoordinate_coe]
    abel
  have hv : (v : H × E) = ((positiveCoordinate W v : H), 0) +
      (finiteCoordinate W v : H × E) := by
    rw [finiteCoordinate_coe]
    abel
  conv_lhs => rw [hu, hv, pairing_add_left, pairing_add_right, pairing_add_right]
  rw [pairing_positive_finite]
  have hz : pairing (finiteCoordinate W u : H × E)
      ((positiveCoordinate W v : H), (0 : E)) = 0 := by
    rw [← pairing_conj_symm, pairing_positive_finite, map_zero]
  rw [hz]
  simp only [pairing, inner_zero_left, sub_zero, add_zero, zero_add]

/-- The splitting and its inverse are continuous in the inherited norms. -/
def subspaceContinuousSplitting : W ≃L[ℂ] positiveKernel W × finitePart W where
  toLinearEquiv := subspaceSplitting W
  continuous_toFun := by
    apply Continuous.prodMk (positiveCoordinate W).continuous
    apply Continuous.subtype_mk
    exact W.subtypeL.continuous.sub
      (((positiveKernel W).subtypeL.comp (positiveCoordinate W)).continuous.prodMk
        continuous_const)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_fst).prodMk continuous_const).add
      (continuous_subtype_val.comp continuous_snd)

omit [(positiveKernel W).HasOrthogonalProjection] in
/-- A closed subspace splits continuously, with the original form on its finite remainder. -/
theorem exists_closed_subspace_splitting [CompleteSpace H]
    (hW : IsClosed (W : Set (H × E))) :
    ∃ e : W ≃L[ℂ] positiveKernel W × finitePart W,
      ∀ u v : W, pairing (u : H × E) (v : H × E) =
        inner ℂ ((e u).1 : H) ((e v).1 : H) +
          pairing ((e u).2 : H × E) ((e v).2 : H × E) := by
  letI : CompleteSpace (positiveKernel W) := (isClosed_positiveKernel W hW).completeSpace_coe
  exact ⟨subspaceContinuousSplitting W, pairing_subspaceSplitting W⟩

#print axioms finitePartToNegative_injective
#print axioms subspaceSplitting
#print axioms pairing_subspaceSplitting
#print axioms exists_closed_subspace_splitting

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
