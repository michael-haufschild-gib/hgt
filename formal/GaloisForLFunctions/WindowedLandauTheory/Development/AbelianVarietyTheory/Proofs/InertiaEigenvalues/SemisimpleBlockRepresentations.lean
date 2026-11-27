import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Group

/-! Semisimplicity is stable under conjugation and finite sums, including
sums with diagonal characters. -/

noncomputable section

open WindowedLandauTheory.MainNotions.N Polynomial
open scoped Matrix

namespace GlobalTheory.SSComplement

theorem isSSRep_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {ρ ρ' : Γ →* GL (Fin n) k} (h : GL (Fin n) k)
    (hh : ∀ g, ρ' g = h * ρ g * h⁻¹) (hρ : IsSSRep ρ) : IsSSRep ρ' := by
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv (M := (h : Matrix (Fin n) (Fin n) k))
    (M' := ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (by simp) (by simp)
  have he : ∀ v, e v = ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ g v, e ((ρ' g : Matrix (Fin n) (Fin n) k) *ᵥ v) = (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro g v
    rw [he, he, hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := hρ (W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hW g v hv, key g v⟩)
  refine ⟨W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k)), fun g v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [key]
    exact hW' g _ hv
  · have := (Submodule.orderIsoMapComap e).symm.isCompl hc
    have h2 : IsCompl ((W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))).comap (e : (Fin n → k) →ₗ[k] (Fin n → k)))
      (W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) := this
    rwa [Submodule.comap_map_eq_of_injective e.injective] at h2

private theorem isSSRep_of_prod {Γ k : Type} [Group Γ] [Field k] {n a b : ℕ} {ρ : Γ →* GL (Fin n) k}
    {ρ₁ : Γ →* GL (Fin a) k} {ρ₂ : Γ →* GL (Fin b) k} (e : (Fin n → k) ≃ₗ[k] (Fin a → k) × (Fin b → k))
    (he : ∀ g v, e ((ρ g : Matrix (Fin n) (Fin n) k) *ᵥ v) =
      ((ρ₁ g : Matrix (Fin a) (Fin a) k) *ᵥ (e v).1, (ρ₂ g : Matrix (Fin b) (Fin b) k) *ᵥ (e v).2))
    (h₁ : IsSSRep ρ₁) (h₂ : IsSSRep ρ₂) : IsSSRep ρ := by
  intro W hW
  let W₁ : Submodule k (Fin a → k) := W.comap (e.symm.toLinearMap ∘ₗ LinearMap.inl k _ _)
  let W₂ : Submodule k (Fin b → k) := W.map (LinearMap.snd k _ _ ∘ₗ e.toLinearMap)
  obtain ⟨C₁, hC₁, hc₁⟩ := h₁ W₁ fun g v hv => by
    have h := hW g _ hv
    show e.symm (_, 0) ∈ W
    convert h using 1
    rw [LinearEquiv.symm_apply_eq, he]
    simp
  obtain ⟨C₂, hC₂, hc₂⟩ := h₂ W₂ (by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hW g v hv, congrArg Prod.snd (he g v)⟩)
  refine ⟨(C₁.prod C₂).comap e.toLinearMap, fun g v hv => ?_, ?_, ?_⟩
  · show e _ ∈ C₁.prod C₂
    rw [he]
    exact ⟨hC₁ g _ hv.1, hC₂ g _ hv.2⟩
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    have h2 : (e v).2 = 0 := Submodule.disjoint_def.1 hc₂.disjoint _ ⟨v, hv, rfl⟩ hv'.2
    have h3 : e.symm ((e v).1, 0) = v := by rw [← h2]; simp
    have h1 : (e v).1 = 0 := Submodule.disjoint_def.1 hc₁.disjoint _
      (show e.symm ((e v).1, 0) ∈ W by rwa [h3]) hv'.1
    rw [← h3, h1]
    exact map_zero e.symm
  · rw [codisjoint_iff, eq_top_iff]
    rintro v -
    obtain ⟨_, ⟨w, hw, rfl⟩, c₂, hc, h2⟩ := Submodule.mem_sup.1
      (show (e v).2 ∈ W₂ ⊔ C₂ by rw [hc₂.sup_eq_top]; trivial)
    obtain ⟨w₁, hw₁, c₁, hc', h1⟩ := Submodule.mem_sup.1
      (show (e v).1 - (e w).1 ∈ W₁ ⊔ C₁ by rw [hc₁.sup_eq_top]; trivial)
    refine Submodule.mem_sup.2 ⟨w + e.symm (w₁, 0), W.add_mem hw hw₁, e.symm (c₁, c₂), ?_, ?_⟩
    · show e (e.symm _) ∈ C₁.prod C₂
      rw [e.apply_symm_apply]
      exact ⟨hc', hc⟩
    · apply e.injective
      have h2' : (e w).2 + c₂ = (e v).2 := h2
      ext1
      · simp only [map_add, e.apply_symm_apply, Prod.fst_add]
        rw [add_assoc, h1]; abel
      · simp only [map_add, e.apply_symm_apply, Prod.snd_add]
        rw [add_zero, h2']

section Blocks

variable {Γ k : Type} [Group Γ] [Field k]

def blockM {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k) (ρ₂ : Γ →* GL (Fin b) k) :
    Γ →* Matrix (Fin n) (Fin n) k where
  toFun g := Matrix.reindex e0 e0
    (Matrix.fromBlocks (ρ₁ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ₂ g : Matrix (Fin b) (Fin b) k))
  map_one' := by simp
  map_mul' g g' := by simp [Matrix.fromBlocks_multiply]

def diagM {t : ℕ} (χ : Fin t → Γ →* kˣ) : Γ →* Matrix (Fin t) (Fin t) k where
  toFun g := Matrix.diagonal fun c => ((χ c g : kˣ) : k)
  map_one' := by simp
  map_mul' g h := by simp [Matrix.diagonal_mul_diagonal]

theorem blockM_charpoly {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k)
    (ρ₂ : Γ →* GL (Fin b) k) (g : Γ) :
    (blockM e0 ρ₁ ρ₂ g).charpoly =
      (ρ₁ g : Matrix (Fin a) (Fin a) k).charpoly * (ρ₂ g : Matrix (Fin b) (Fin b) k).charpoly := by
  show (Matrix.reindex e0 e0 _).charpoly = _
  rw [Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁]

theorem blockM_ss {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k)
    (ρ₂ : Γ →* GL (Fin b) k) (h₁ : IsSSRep ρ₁) (h₂ : IsSSRep ρ₂) : IsSSRep (blockM e0 ρ₁ ρ₂).toHomUnits := by
  refine isSSRep_of_prod ((LinearEquiv.funCongrLeft k k e0).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h₁ h₂
  show _ = _
  ext i <;> simp [blockM, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl

private theorem ss_of_scalar {a : ℕ} (ρ : Γ →* GL (Fin a) k) (c : Γ → k)
    (h : ∀ g v, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v = c g • v) : IsSSRep ρ := by
  intro W _
  obtain ⟨W', hW'⟩ := W.exists_isCompl
  exact ⟨W', fun g v hv => by rw [h]; exact W'.smul_mem _ hv, hW'⟩

theorem diagM_ss : ∀ {t : ℕ} (χ : Fin t → Γ →* kˣ), IsSSRep (diagM χ).toHomUnits
  | 0, χ => ss_of_scalar _ (fun _ => 0) fun g v => funext fun c => c.elim0
  | t + 1, χ => by
    refine isSSRep_of_prod (ρ₁ := (diagM fun c : Fin t => χ (Fin.castAdd 1 c)).toHomUnits)
      (ρ₂ := (diagM fun c : Fin 1 => χ (Fin.natAdd t c)).toHomUnits)
      ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) (diagM_ss _)
      (ss_of_scalar _ (fun g => ((χ (Fin.last t) g : kˣ) : k)) fun g v => ?_)
    · show _ = _
      ext i <;> simp [diagM, Matrix.mulVec_diagonal, LinearMap.funLeft]
    · funext c
      obtain rfl : c = 0 := Subsingleton.elim _ _
      simp [diagM, Matrix.mulVec_diagonal]
      exact Or.inl rfl

theorem diagM_charpoly {t : ℕ} (χ : Fin t → Γ →* kˣ) (g : Γ) :
    (diagM χ g).charpoly = ∏ c, (X - C ((χ c g : kˣ) : k)) :=
  Matrix.charpoly_diagonal _

end Blocks

end GlobalTheory.SSComplement
