import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedHomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedTensorProduct

/-! The projections and contracting homotopies of the factors combine on the tensor complex. -/

noncomputable section

open TensorProduct

namespace GlobalTheory.CechDR.FiniteGradedComplex

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

variable (G : FiniteGradedComplex K V) (H : FiniteGradedComplex K W)

/-- The homotopy lowers degree by one, with the Koszul sign in the second term. -/
def tensorChainHomotopy (e h : V →ₗ[K] V) (h' : W →ₗ[K] W) : Module.End K (V ⊗[K] W) :=
  TensorProduct.map h 1 + TensorProduct.map (G.σ * e) h'

theorem tensorChainHomotopy_apply (e h : V →ₗ[K] V) (h' : W →ₗ[K] W)
    (a : V) (b : W) :
    G.tensorChainHomotopy e h h' (a ⊗ₜ b) = h a ⊗ₜ b + G.σ (e a) ⊗ₜ h' b := by
  simp only [tensorChainHomotopy, LinearMap.add_apply, TensorProduct.map_tmul,
    Module.End.mul_apply, Module.End.one_apply]

theorem tensorChainHomotopy_degree (e h : V →ₗ[K] V) (h' : W →ₗ[K] W)
    (hh : ∀ p a, h (G.π (p + 1) a) = G.π p (h a))
    (hh' : ∀ q b, h' (H.π (q + 1) b) = H.π q (h' b))
    (he : ∀ p a, e (G.π p a) = G.π p (e a))
    (n : ℕ) (z : V ⊗[K] W) :
    G.tensorChainHomotopy e h h' ((G.tensorComplex H).π (n + 1) z) =
      (G.tensorComplex H).π n (G.tensorChainHomotopy e h h' z) := by
  have E : G.tensorChainHomotopy e h h' ∘ₗ G.tensorProjection H (n + 1) =
      G.tensorProjection H n ∘ₗ G.tensorChainHomotopy e h h' := by
    refine G.tensor_ext_degrees H fun p q a b => ?_
    rcases p with _ | p
    · simp only [G.zero, zero_tmul, map_zero]
    rcases q with _ | q
    · simp only [H.zero, tmul_zero, map_zero]
    have ha := G.idem (p + 1) a
    have hb := H.idem (q + 1) b
    have h₁ : G.π p (h (G.π (p + 1) a)) = h (G.π (p + 1) a) :=
      (hh p (G.π (p + 1) a)).symm.trans (congrArg h ha)
    have h₂ : H.π q (h' (H.π (q + 1) b)) = h' (H.π (q + 1) b) :=
      (hh' q (H.π (q + 1) b)).symm.trans (congrArg h' hb)
    have h₃ : G.π (p + 1) (G.σ (e (G.π (p + 1) a))) = G.σ (e (G.π (p + 1) a)) := by
      rw [he, G.σπ, map_zsmul, G.idem]
    simp only [LinearMap.comp_apply, G.tensorProjection_tmul H (n + 1) _ _ _ _ ha hb,
      tensorChainHomotopy_apply, map_add,
      G.tensorProjection_tmul H n p (q + 1) _ _ h₁ hb,
      G.tensorProjection_tmul H n (p + 1) q _ _ h₃ h₂]
    by_cases hpq : (p + 1) + (q + 1) = n + 1
    · simp only [if_pos hpq, if_pos (show p + (q + 1) = n by omega),
        if_pos (show (p + 1) + q = n by omega), tensorChainHomotopy_apply]
    · simp only [if_neg hpq, if_neg (show p + (q + 1) ≠ n by omega),
        if_neg (show (p + 1) + q ≠ n by omega), map_zero, add_zero]
  exact LinearMap.congr_fun E z

theorem tensorProjection_map (e : V →ₗ[K] V) (e' : W →ₗ[K] W)
    (hπ : ∀ p a, e (G.π p a) = G.π p (e a))
    (hπ' : ∀ q b, e' (H.π q b) = H.π q (e' b)) (n : ℕ) :
    TensorProduct.map e e' ∘ₗ G.tensorProjection H n =
      G.tensorProjection H n ∘ₗ TensorProduct.map e e' := by
  have h₁ (p : ℕ) : e ∘ₗ G.π p = G.π p ∘ₗ e := LinearMap.ext (hπ p)
  have h₂ (q : ℕ) : e' ∘ₗ H.π q = H.π q ∘ₗ e' := LinearMap.ext (hπ' q)
  apply LinearMap.ext
  intro z
  simp only [tensorProjection, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [TensorProduct.map_map, TensorProduct.map_map, h₁, h₂]

/-- Tensoring the two cocycle representatives gives the representative projection
for the total differential. -/
theorem tensor_contraction (e h : V →ₗ[K] V) (e' h' : W →ₗ[K] W)
    (hde : ∀ a, G.d (e a) = 0) (hed : ∀ a, e (G.d a) = 0)
    (hc : ∀ a, G.d (h a) + h (G.d a) + e a = a)
    (hh : ∀ p a, h (G.π (p + 1) a) = G.π p (h a))
    (hπ : ∀ p a, e (G.π p a) = G.π p (e a))
    (hde' : ∀ b, H.d (e' b) = 0) (hed' : ∀ b, e' (H.d b) = 0)
    (hc' : ∀ b, H.d (h' b) + h' (H.d b) + e' b = b) :
    let D := (G.tensorComplex H).d
    let E := TensorProduct.map e e'
    let J := G.tensorChainHomotopy e h h'
    (∀ z, D (E z) = 0) ∧ (∀ z, E (D z) = 0) ∧ (∀ z, D (J z) + J (D z) + E z = z) := by
  let D := (G.tensorComplex H).d
  let E := TensorProduct.map e e'
  have hDe : G.d * e = 0 := LinearMap.ext hde
  have heD : e * G.d = 0 := LinearMap.ext hed
  have hDe' : H.d * e' = 0 := LinearMap.ext hde'
  have heD' : e' * H.d = 0 := LinearMap.ext hed'
  have hDσ : G.d * G.σ = -(G.σ * G.d) := by
    apply LinearMap.ext
    intro a
    change G.d (G.σ a) = - G.σ (G.d a)
    rw [G.σd, neg_neg]
  have hσe : G.σ * e = e * G.σ := by
    apply LinearMap.ext
    exact G.ext' fun p a => by
      simp only [Module.End.mul_apply, G.σπ, map_zsmul, hπ]
  have hσh : G.σ * h = -(h * G.σ) := by
    apply LinearMap.ext
    refine G.ext' fun p a => ?_
    rcases p with _ | p
    · simp only [G.zero, map_zero]
    · simp only [Module.End.mul_apply, LinearMap.neg_apply, G.σπ, hh, map_neg, map_zsmul,
        pow_succ, mul_neg_one, neg_smul, neg_neg]
  have hσσ : G.σ * G.σ = 1 := LinearMap.ext G.σσ
  have hh₁ : 1 - e = G.d * h + h * G.d := by
    apply LinearMap.ext
    intro a
    exact sub_eq_iff_eq_add.mpr (hc a).symm
  have hh₂ : 1 - e' = H.d * h' + h' * H.d := by
    apply LinearMap.ext
    intro b
    exact sub_eq_iff_eq_add.mpr (hc' b).symm
  have hDE : D * E = 0 := by
    change (TensorProduct.map G.d 1 + TensorProduct.map G.σ H.d) * E = 0
    simp only [E, add_mul, ← TensorProduct.map_mul, hDe, hDe', TensorProduct.map_zero_left,
      TensorProduct.map_zero_right, add_zero]
  have hED : E * D = 0 := by
    change E * (TensorProduct.map G.d 1 + TensorProduct.map G.σ H.d) = 0
    simp only [E, mul_add, ← TensorProduct.map_mul, heD, heD', TensorProduct.map_zero_left,
      TensorProduct.map_zero_right, add_zero]
  refine ⟨LinearMap.congr_fun hDE, LinearMap.congr_fun hED, fun z => ?_⟩
  have hz := LinearMap.congr_fun (tensor_homotopy hh₁ hDe heD hDσ hσe hσh hσσ hh₂) z
  exact (sub_eq_iff_eq_add.mp hz).symm

end GlobalTheory.CechDR.FiniteGradedComplex
