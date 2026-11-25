import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FlatFibreInjectivity
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.SmoothNoetherianModel
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! Detection of the pointed equalizer of smooth affine algebras on field fibres. -/

open TensorProduct

namespace GlobalTheory.GlobalFunctions

private theorem flat_prod {R A B : Type} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Flat R A] [Module.Flat R B] : Module.Flat R (A × B) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have hA := Module.Flat.rTensor_preserves_injective_linearMap (M := A) I.subtype I.subtype_injective
  have hB := Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype I.subtype_injective
  have e (x : I ⊗[R] (A × B)) :
      TensorProduct.prodRight R R R A B (I.subtype.rTensor (A × B) x) =
      Prod.map (I.subtype.rTensor A) (I.subtype.rTensor B)
        (TensorProduct.prodRight R R I A B x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]; ext <;> simp
    | tmul m y => simp
    | add x y hx hy => simp only [map_add, hx, hy]; ext <;> simp
  intro x y hxy
  apply (TensorProduct.prodRight R R I A B).injective
  apply hA.prodMap hB
  rw [← e, ← e, hxy]

private theorem baseChange_model {R₀ R k B₀ B C₀ C : Type} [CommRing R₀] [CommRing R] [CommRing k]
    [Algebra R₀ R] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k]
    [AddCommGroup B₀] [Module R₀ B₀] [AddCommGroup C₀] [Module R₀ C₀]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (β : R ⊗[R₀] B₀ ≃ₗ[R] B) (δ : R ⊗[R₀] C₀ ≃ₗ[R] C) (u₀ : B₀ →ₗ[R₀] C₀) (u : B →ₗ[R] C)
    (h : ∀ b, u (β (1 ⊗ₜ b)) = δ (1 ⊗ₜ u₀ b)) (y : k ⊗[R₀] B₀) :
    u.baseChange k (β.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y)) =
    δ.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k C₀).symm (u₀.baseChange k y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c b => simp [h]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem model_apply {R₀ R B₀ B C₀ C : Type} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [AddCommGroup B₀] [Module R₀ B₀] [AddCommGroup C₀] [Module R₀ C₀]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (β : R ⊗[R₀] B₀ ≃ₗ[R] B) (δ : R ⊗[R₀] C₀ ≃ₗ[R] C) (u₀ : B₀ →ₗ[R₀] C₀) (u : B →ₗ[R] C)
    (h : ∀ b, u (β (1 ⊗ₜ b)) = δ (1 ⊗ₜ u₀ b)) (y : R ⊗[R₀] B₀) :
    u (β y) = δ (u₀.baseChange R y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have h1 : ∀ {M : Type} [AddCommGroup M] [Module R₀ M] (m : M),
        (c ⊗ₜ[R₀] m : R ⊗[R₀] M) = c • (1 ⊗ₜ m) := by
      intro M _ _ m
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [LinearMap.baseChange_tmul, h1 b, h1 (u₀ b), map_smul, map_smul, map_smul, h]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The common kernel of the two restrictions and evaluation is detected on field fibres. -/
theorem eq_zero_of_fibres {R B C : Type} [CommRing R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C]
    (f g : B →ₐ[R] C) (r : B →ₐ[R] R)
    (hk : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] B),
      f.toLinearMap.baseChange k x = g.toLinearMap.baseChange k x →
      r.toLinearMap.baseChange k x = 0 → x = 0)
    (b : B) (hb : f b = g b) (hr : r b = 0) : b = 0 := by
  obtain ⟨R₀, B₀, C₀, _, _, _, _, _, _, _, f₀, g₀, r₀, β, δ, _, _, h⟩ := exists_noetherian_model_of_smooth R B C f g r
  let ρ : R ⊗[R₀] R₀ ≃ₗ[R] R := AlgebraTensorModule.rid R₀ R R
  have hf : ∀ b, f.toLinearMap (β.toLinearEquiv (1 ⊗ₜ b)) =
      δ.toLinearEquiv (1 ⊗ₜ f₀.toLinearMap b) := fun b ↦ (h b).1
  have hg : ∀ b, g.toLinearMap (β.toLinearEquiv (1 ⊗ₜ b)) =
      δ.toLinearEquiv (1 ⊗ₜ g₀.toLinearMap b) := fun b ↦ (h b).2.1
  have hr' : ∀ b, r.toLinearMap (β.toLinearEquiv (1 ⊗ₜ b)) =
      ρ (1 ⊗ₜ r₀.toLinearMap b) := fun b ↦ (h b).2.2.trans (by
        simp [ρ, Algebra.algebraMap_eq_smul_one])
  let φ : B₀ →ₗ[R₀] C₀ × R₀ := (f₀.toLinearMap - g₀.toLinearMap).prod r₀.toLinearMap
  have : Module.Flat R₀ (C₀ × R₀) := flat_prod
  have hφ : Function.Injective (φ.baseChange R) := by
    refine FlatFibreInjective.injective_baseChange R₀ R B₀ (C₀ × R₀) φ fun k _ _ _ _ ↦ ?_
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : (f₀.toLinearMap - g₀.toLinearMap).baseChange k y = 0 := by
      have : f₀.toLinearMap - g₀.toLinearMap = (LinearMap.fst R₀ C₀ R₀) ∘ₗ φ := rfl
      rw [this, LinearMap.baseChange_comp, LinearMap.comp_apply, hy, map_zero]
    have h2 : r₀.toLinearMap.baseChange k y = 0 := by
      have : r₀.toLinearMap = (LinearMap.snd R₀ C₀ R₀) ∘ₗ φ := rfl
      rw [this, LinearMap.baseChange_comp, LinearMap.comp_apply, hy, map_zero]
    rw [LinearMap.baseChange_sub, LinearMap.sub_apply, sub_eq_zero] at h1
    have h3 := hk k (β.toLinearEquiv.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y))
      (by rw [baseChange_model _ _ _ _ hf, baseChange_model _ _ _ _ hg, h1])
      (by rw [baseChange_model _ _ _ _ hr', h2, map_zero, map_zero])
    have h4 : (β.toLinearEquiv.baseChange R k _ _)
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y) = 0 := h3
    simpa using h4
  obtain ⟨y, rfl⟩ := β.surjective b
  have h1 : f₀.toLinearMap.baseChange R y = g₀.toLinearMap.baseChange R y := by
    apply δ.toLinearEquiv.injective
    rw [← model_apply _ _ _ _ hf, ← model_apply _ _ _ _ hg]
    exact hb
  have h2 : r₀.toLinearMap.baseChange R y = 0 := by
    apply ρ.injective
    rw [← model_apply _ _ _ _ hr', map_zero]
    exact hr
  have h3 : φ = LinearMap.inl R₀ C₀ R₀ ∘ₗ (f₀.toLinearMap - g₀.toLinearMap) +
      LinearMap.inr R₀ C₀ R₀ ∘ₗ r₀.toLinearMap := by
    ext x <;> simp [φ]
  have : y = 0 := by
    apply hφ
    rw [map_zero, h3, LinearMap.baseChange_add, LinearMap.add_apply, LinearMap.baseChange_comp,
      LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply, h2,
      LinearMap.baseChange_sub, LinearMap.sub_apply, h1, sub_self, map_zero, map_zero, add_zero]
  rw [this, map_zero]

end GlobalTheory.GlobalFunctions
