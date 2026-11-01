import GaloisForLFunctions.HeckeKreinToeplitz.Index.RestrictedFiniteNegativeRadical
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteHermitianSignature

/-!
# Signed Hilbert models for closed nondegenerate subspaces

The closed positive kernel is already Hilbert. Splitting the finite
remainder by its Hermitian signature supplies the missing positive and
negative factors, with a continuous linear equivalence to the subspace.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

private def regroupHilbertFactors
    (V P N : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] :
    (V × (P × N)) ≃L[ℂ] (WithLp 2 (V × P) × N) where
  toFun x := (WithLp.toLp 2 (x.1, x.2.1), x.2.2)
  invFun x := (x.1.fst, (x.1.snd, x.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun :=
    ((WithLp.prodContinuousLinearEquiv 2 ℂ V P).symm.continuous.comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd)
  continuous_invFun :=
    (continuous_fst.comp ((WithLp.prodContinuousLinearEquiv 2 ℂ V P).continuous.comp
      continuous_fst)).prodMk
        ((continuous_snd.comp ((WithLp.prodContinuousLinearEquiv 2 ℂ V P).continuous.comp
          continuous_fst)).prodMk continuous_snd)

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

/-- A closed subspace with zero radical has a complete positive/negative Hilbert model. -/
theorem exists_closed_signed_splitting (W : Submodule ℂ (H × E))
    (hW : IsClosed (W : Set (H × E))) (hnd : restrictedRadical W = ⊥) :
    ∃ (n : ℕ) (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
      (e : W ≃L[ℂ] (WithLp 2 (positiveKernel W × FiniteSignature.PositiveSpace d) ×
        FiniteSignature.NegativeSpace d hd)),
      ∀ u v : W, pairing (e u) (e v) = pairing (u : H × E) (v : H × E) := by
  letI : CompleteSpace (positiveKernel W) := (isClosed_positiveKernel W hW).completeSpace_coe
  let B : finitePart W → finitePart W → ℂ := fun u v => pairing (v : H × E) (u : H × E)
  have hB : IsHermitianForm B :=
    { add_left := fun u v w => pairing_add_right (w : H × E) u v
      smul_left := fun c v w => pairing_smul_right c (w : H × E) v
      symm := fun u v => (pairing_conj_symm (u : H × E) (v : H × E)).symm }
  have hFnd : ∀ f, (∀ g, B f g = 0) → f = 0 := by
    intro f hf
    have hr : (f : H × E) ∈ restrictedRadical W := by
      refine (mem_restrictedRadical W (f : H × E)).mpr ⟨f.property.1, ?_⟩
      intro w hw
      let w' : W := ⟨w, hw⟩
      have heq : ((positiveCoordinate W w' : H), (0 : E)) +
          (finiteCoordinate W w' : H × E) = w := by
        rw [finiteCoordinate_coe]
        change ((positiveCoordinate W w' : H), (0 : E)) +
          (w - ((positiveCoordinate W w' : H), (0 : E))) = w
        abel
      have hfg : pairing (finiteCoordinate W w' : H × E) (f : H × E) = 0 :=
        hf (finiteCoordinate W w')
      rw [← heq, pairing_add_left, pairing_positive_finite W, hfg, zero_add]
    rw [hnd, Submodule.mem_bot] at hr
    exact Subtype.ext hr
  obtain ⟨n, d, hd, eF, hF⟩ := FiniteSignature.exists_signed_hilbert_coordinates hB hFnd
  let e₀ := subspaceContinuousSplitting W
  let e₁ := ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ (positiveKernel W))
    eF.toContinuousLinearEquiv
  let e₂ := regroupHilbertFactors (positiveKernel W)
    (FiniteSignature.PositiveSpace d) (FiniteSignature.NegativeSpace d hd)
  refine ⟨n, d, hd, (e₀.trans e₁).trans e₂, ?_⟩
  intro u v
  change inner ℂ (WithLp.toLp 2 ((positiveCoordinate W u), (eF (finiteCoordinate W u)).1))
      (WithLp.toLp 2 ((positiveCoordinate W v), (eF (finiteCoordinate W v)).1)) -
        inner ℂ (eF (finiteCoordinate W u)).2 (eF (finiteCoordinate W v)).2 = _
  rw [WithLp.prod_inner_apply, pairing_subspaceSplitting W]
  have hh := hF (finiteCoordinate W v) (finiteCoordinate W u)
  change pairing (finiteCoordinate W u : H × E) (finiteCoordinate W v : H × E) =
    inner ℂ (eF (finiteCoordinate W u)).1 (eF (finiteCoordinate W v)).1 -
      inner ℂ (eF (finiteCoordinate W u)).2 (eF (finiteCoordinate W v)).2 at hh
  rw [hh]
  change (inner ℂ (positiveCoordinate W u : H) (positiveCoordinate W v : H) +
      inner ℂ (eF (finiteCoordinate W u)).1 (eF (finiteCoordinate W v)).1) -
        inner ℂ (eF (finiteCoordinate W u)).2 (eF (finiteCoordinate W v)).2 =
      inner ℂ (positiveCoordinate W u : H) (positiveCoordinate W v : H) +
        (inner ℂ (eF (finiteCoordinate W u)).1 (eF (finiteCoordinate W v)).1 -
          inner ℂ (eF (finiteCoordinate W u)).2 (eF (finiteCoordinate W v)).2)
  ring

#print axioms exists_closed_signed_splitting

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
