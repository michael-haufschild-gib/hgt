import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.BrauerRestriction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Parabolic induction of virtual characters over a finite field. -/

open GaloisForLFunctions Module

noncomputable section
namespace GlobalTheory.CuspGL


private theorem sum_fibres {G X : Type} [Group G] [Fintype G] [Fintype X]
    (H : Subgroup G) (π : G → X)
    (hs : Function.Surjective π) (hπ : ∀ s t, π s = π t ↔ s⁻¹ * t ∈ H) (f : X → ℂ) :
    ∑ t, f (π t) = (Nat.card H : ℂ) * ∑ x, f x := by
  classical
  have hcard : ∀ s : G, (Finset.univ.filter (fun t => π t = π s)).card = Nat.card H := by
    intro s
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun t => ⟨s⁻¹ * t.1, (hπ s t.1).1 t.2.symm⟩
        invFun := fun h => ⟨s * h.1, ((hπ s (s * h.1)).2 (by simpa using h.2)).symm⟩
        left_inv := fun t => by ext; simp
        right_inv := fun h => by ext; simp }
  calc ∑ t, f (π t) = ∑ x, ∑ t ∈ Finset.univ.filter (fun t => π t = x), f (π t) :=
        (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ x, (Nat.card H : ℂ) * f x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        obtain ⟨s, rfl⟩ := hs x
        rw [Finset.sum_congr rfl (g := fun _ => f (π s))
          (fun t ht => by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const, hcard, nsmul_eq_mul]
    _ = _ := (Finset.mul_sum _ _ _).symm

variable {F : Type} [Field F] {n : ℕ}

private def lin (x : GL (Fin n) F) : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
  (Matrix.GeneralLinearGroup.toLin x).toLinearEquiv

private theorem lin_apply (x : GL (Fin n) F) (v : Fin n → F) :
    lin x v = Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v := rfl

private theorem lin_mul (x y : GL (Fin n) F) (v : Fin n → F) :
    lin (x * y) v =
      lin x (lin y v) := by
  simp only [lin_apply, Units.val_mul,
    Matrix.toLin'_mul_apply]

private theorem lin_one (v : Fin n → F) :
    lin (1 : GL (Fin n) F) v = v := by
  simp [lin_apply]

private theorem lin_inv (x : GL (Fin n) F) (v : Fin n → F) : lin x⁻¹ v = (lin x).symm v := rfl

private theorem lin_surjective (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    ∃ x : GL (Fin n) F, lin x = e := by
  let u := LinearMap.GeneralLinearGroup.ofLinearEquiv e
  let E : GL (Fin n) F ≃* LinearMap.GeneralLinearGroup F (Fin n → F) :=
    Matrix.GeneralLinearGroup.toLin
  refine ⟨E.symm u, ?_⟩
  change (E (E.symm u)).toLinearEquiv = e
  rw [E.apply_symm_apply]
  ext v
  rfl

private theorem map_eq_of_stable (x : GL (Fin n) F)
    (W : Submodule F (Fin n → F)) (h : ∀ v ∈ W, lin x v ∈ W) :
    W.map (lin x).toLinearMap = W := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

private def stab (W : Submodule F (Fin n → F)) : Subgroup (GL (Fin n) F) where
  carrier := {x | ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W}
  one_mem' := fun v hv => by rw [← lin_apply, lin_one]; exact hv
  mul_mem' := fun {x y} hx hy v hv => by
    rw [← lin_apply, lin_mul]; exact hx _ (hy v hv)
  inv_mem' := fun {x} hx v hv => by
    rw [← lin_apply, lin_inv]
    rw [← map_eq_of_stable x W hx] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simpa using hw

private theorem lin_mul_toLinearMap (x y : GL (Fin n) F) :
    (lin (x * y)).toLinearMap =
      (lin x).toLinearMap ∘ₗ
        (lin y).toLinearMap :=
  LinearMap.ext fun v => lin_mul x y v

private theorem map_eq_map_iff (W : Submodule F (Fin n → F))
    (s t : GL (Fin n) F) :
    W.map (lin s).toLinearMap =
        W.map (lin t).toLinearMap ↔
      s⁻¹ * t ∈ stab W := by
  constructor
  · intro h v hv
    rw [← lin_apply, lin_mul,
      lin_inv]
    have hmem : lin t v ∈
        W.map (lin s).toLinearMap := h ▸ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hw'⟩ := hmem
    simpa [← hw'] using hw
  · intro h
    have h' : ∀ v ∈ W, lin (s⁻¹ * t) v ∈ W := h
    conv_rhs => rw [show t = s * (s⁻¹ * t) by group]
    rw [lin_mul_toLinearMap, Submodule.map_comp,
      map_eq_of_stable _ W h']

private theorem conj_mem_stab_iff (W : Submodule F (Fin n → F))
    (x t : GL (Fin n) F) :
    t⁻¹ * x * t ∈ stab W ↔
      x ∈ stab (W.map (lin t).toLinearMap) := by
  change (∀ v ∈ W, lin (t⁻¹ * x * t) v ∈ W) ↔
    ∀ v ∈ W.map (lin t).toLinearMap, lin x v ∈
      W.map (lin t).toLinearMap
  constructor
  · rintro h _ ⟨w, hw, rfl⟩
    refine ⟨lin (t⁻¹ * x * t) w, h w hw, ?_⟩
    simp only [LinearEquiv.coe_coe]
    rw [← lin_mul, ← lin_mul,
      show t * (t⁻¹ * x * t) = x * t by group]
  · intro h w hw
    obtain ⟨u, hu, hu'⟩ := h (lin t w) ⟨w, hw, rfl⟩
    have hwu : lin (t⁻¹ * x * t) w = u := by
      rw [show t⁻¹ * x * t = t⁻¹ * (x * t) by group, lin_mul,
        lin_mul, ← hu', LinearEquiv.coe_coe,
        lin_inv, LinearEquiv.symm_apply_apply]
    rw [hwu]
    exact hu

private def resMat {a : ℕ} (W : Submodule F (Fin n → F)) (e : W ≃ₗ[F] (Fin a → F)) :
    stab W →* Matrix (Fin a) (Fin a) F where
  toFun h := LinearMap.toMatrix'
    (e.conj ((Matrix.toLin' ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).restrict h.2))
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.conj_apply_apply, ← LinearEquiv.eq_symm_apply]
    ext1
    simp
  map_mul' x y := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp only [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
    congr 1
    ext1
    exact lin_mul x.1 y.1 _

private theorem exists_gl_map_lin_eq_of_finrank_eq (W₀ W : Submodule F (Fin n → F))
    (h : Module.finrank F W₀ = Module.finrank F W) :
    ∃ t : GL (Fin n) F, W₀.map (lin t).toLinearMap = W := by
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl W₀
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have h₁ := Submodule.finrank_add_eq_of_isCompl hC₀
  have h₂ := Submodule.finrank_add_eq_of_isCompl hC
  let E : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    (W₀.prodEquivOfIsCompl C₀ hC₀).symm ≪≫ₗ
      (LinearEquiv.prodCongr (LinearEquiv.ofFinrankEq W₀ W h)
        (LinearEquiv.ofFinrankEq C₀ C (by omega))) ≪≫ₗ W.prodEquivOfIsCompl C hC
  obtain ⟨t, ht⟩ := lin_surjective E
  refine ⟨t, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hs : (W₀.prodEquivOfIsCompl C₀ hC₀).symm v = (⟨v, hv⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left W₀ C₀ hC₀ ⟨v, hv⟩
    simp [ht, E, hs]
  · rw [LinearEquiv.finrank_map_eq, h]

/-- Summing a virtual character over stable subspaces of fixed dimension is parabolic induction. -/
theorem parabolic_sum_mem_virtual {F : Type} [Field F] [Finite F]
    (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ)
    (hΦ : ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V),
      Φ V' (e.conj g) = Φ V g)
    (a n : ℕ) (ha : a ≤ n)
    (hχ : (fun x : GL (Fin a) F => Φ (Fin a → F) (Matrix.toLin' (x : Matrix (Fin a) (Fin a) F))) ∈
      virtualCharacterGroup (GL (Fin a) F)) :
    (fun x : GL (Fin n) F => ∑ᶠ W : {W : Submodule F (Fin n → F) //
      Module.finrank F W = a ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W},
        Φ W.1 ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict W.2.2)) ∈
      virtualCharacterGroup (GL (Fin n) F) := by
  classical
  letI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Submodule F (Fin n → F), Module.finrank F W₀ = a := by
    refine ⟨Submodule.span F (Set.range fun i : Fin a => (Pi.single (Fin.castLE ha i) (1 : F) :
      Fin n → F)), ?_⟩
    rw [finrank_span_eq_card, Fintype.card_fin]
    convert (Pi.basisFun F (Fin n)).linearIndependent.comp _ (Fin.castLE_injective ha) using 1
    ext i : 1
    simp
  let e₀ : W₀ ≃ₗ[F] (Fin a → F) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hW₀, Module.finrank_fin_fun])
  let P := stab W₀
  let ρ : P →* GL (Fin a) F := (resMat W₀ e₀).toHomUnits
  let χ : GL (Fin a) F → ℂ := fun y => Φ (Fin a → F) (Matrix.toLin' (y : Matrix (Fin a) (Fin a) F))
  have hψ : (fun p : P => χ (ρ p)) ∈ virtualCharacterGroup P :=
    (VirtualCharacter.restrict _ ρ ⟨χ, hχ⟩).property
  convert inducedFunction_mem_virtual P hψ using 1
  funext x
  have hval : ∀ p : P, χ (ρ p) =
      Φ W₀ ((Matrix.toLin' ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).restrict p.2) := by
    intro p
    simp only [χ, ρ, MonoidHom.coe_toHomUnits]
    exact (congrArg (Φ (Fin a → F)) (Matrix.toLin'_toMatrix' (e₀.conj
      ((Matrix.toLin' ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).restrict p.2)))).trans
      (hΦ _ _ e₀ _)
  haveI : Fintype (Submodule F (Fin n → F)) := Fintype.ofFinite _
  let π : GL (Fin n) F → {W : Submodule F (Fin n → F) // Module.finrank F W = a} := fun t =>
    ⟨W₀.map (lin t).toLinearMap, by
      rw [LinearEquiv.finrank_map_eq, hW₀]⟩
  let f : {W : Submodule F (Fin n → F) // Module.finrank F W = a} → ℂ := fun W =>
    if h : ∀ v ∈ W.1, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W.1 then
      Φ W.1 ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict h) else 0
  let p : {W : Submodule F (Fin n → F) // Module.finrank F W = a} → Prop := fun W =>
    ∀ v ∈ W.1, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W.1
  have hs : Function.Surjective π := fun W => by
    obtain ⟨t, ht⟩ := exists_gl_map_lin_eq_of_finrank_eq W₀ W.1 (by rw [hW₀, W.2])
    exact ⟨t, Subtype.ext ht⟩
  have hπ : ∀ s t, π s = π t ↔ s⁻¹ * t ∈ P := fun s t =>
    Subtype.ext_iff.trans (map_eq_map_iff W₀ s t)
  have hpt : ∀ t, extendByZero P (fun p => χ (ρ p)) (t⁻¹ * x * t) = f (π t) := by
    intro t
    unfold extendByZero
    by_cases h : t⁻¹ * x * t ∈ P
    · have h' : ∀ v ∈ W₀.map (lin t).toLinearMap,
          Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈
            W₀.map (lin t).toLinearMap :=
        (conj_mem_stab_iff W₀ x t).1 h
      rw [dif_pos h]
      show χ (ρ ⟨_, h⟩) = _
      rw [hval]
      simp only [f, π]
      rw [dif_pos h']
      symm
      refine (congrArg (Φ ↥(W₀.map (lin t).toLinearMap)) ?_).trans
        (hΦ _ _ ((lin t).submoduleMap W₀) _)
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      obtain ⟨w, rfl⟩ := ((lin t).submoduleMap W₀).surjective u
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      simp only [LinearMap.restrict_coe_apply, LinearEquiv.submoduleMap_apply, Subgroup.coe_mk,
        ← lin_apply]
      change _ = lin t
        (lin (t⁻¹ * x * t) (w : Fin n → F))
      simp only [← lin_mul, Subgroup.coe_mk, mul_assoc,
        mul_inv_cancel_left]
    · have h' : ¬ ∀ v ∈ W₀.map (lin t).toLinearMap,
          Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈
            W₀.map (lin t).toLinearMap :=
        fun h' => h ((conj_mem_stab_iff W₀ x t).2 h')
      rw [dif_neg h]
      simp only [f, π]
      rw [dif_neg h']
  have hinv :
      (∑ t : GL (Fin n) F, extendByZero P (fun p => χ (ρ p)) (t * x * t⁻¹)) =
        ∑ t : GL (Fin n) F, extendByZero P (fun p => χ (ρ p)) (t⁻¹ * x * t) := by
    refine Fintype.sum_equiv (Equiv.inv _) _ _ fun t => ?_
    rw [Equiv.inv_apply, inv_inv]
  unfold inducedFunction
  rw [hinv]
  rw [Finset.sum_congr rfl (fun t _ => hpt t), sum_fibres P π hs hπ f,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_mul,
    finsum_eq_sum_of_fintype,
    ← Fintype.sum_subtype_add_sum_subtype p f]
  have hzero : ∑ W : {W // ¬ p W}, f W = 0 := Finset.sum_eq_zero (fun W _ => dif_neg W.2)
  rw [hzero, add_zero]
  exact (Fintype.sum_equiv (Equiv.subtypeSubtypeEquivSubtypeInter _ _) _ _
    (fun W => dif_pos W.2)).symm

end GlobalTheory.CuspGL
