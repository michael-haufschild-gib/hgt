import GaloisForLFunctions.RHTower.DeningerDynSysCharacterTopology
import GaloisForLFunctions.RHTower.DeningerDynSysColimitTopology

/-!
# Automorphisms act by homeomorphisms

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 7.3 (`t9`) and
Proposition 7.4(c) (`t10`).

A morphism of schemes pulls the evaluation of a section back to the evaluation of its pullback,

`eval V g (f̂ P) = eval (f⁻¹ V) (f^♯ g) P` ,

because the residue field map is compatible with evaluation and extension by zero commutes with
precomposition by a homomorphism of fields.  For an isomorphism the preimage of an affine open is
affine, so `f̂` is continuous, and applying this to the inverse shows that `f̂` is a homeomorphism
of `X̂ (C)`.  Since `f̂` commutes with the Frobenius operators it descends to a homeomorphism of
`X̌ (C)`.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

universe u

variable {X Y : Scheme.{u}} {C : Type u} [Field C]

theorem deningerUnitExtend_zero {k : Type u} [Field k] (χ : kˣ →* Cˣ) :
    deningerUnitExtend χ (0 : k) = 0 := by
  rw [deningerUnitExtend, dif_pos rfl]

/-- Extension by zero commutes with precomposition by a homomorphism of fields. -/
theorem deningerUnitExtend_comp {k l : Type u} [Field k] [Field l] (σ : k →+* l)
    (χ : lˣ →* Cˣ) (a : k) :
    deningerUnitExtend (χ.comp (Units.map σ.toMonoidHom)) a = deningerUnitExtend χ (σ a) := by
  classical
  by_cases h : a = 0
  · subst h
    have e1 : deningerUnitExtend (χ.comp (Units.map σ.toMonoidHom)) (0 : k) = 0 :=
      deningerUnitExtend_zero _
    have e2 : σ (0 : k) = 0 := σ.map_zero
    rw [e1, e2]
    exact (deningerUnitExtend_zero χ).symm
  · have hσ : σ a ≠ 0 := fun hc => h (σ.injective (by rw [hc, σ.map_zero]))
    have e1 : deningerUnitExtend (χ.comp (Units.map σ.toMonoidHom)) a
        = (((χ.comp (Units.map σ.toMonoidHom)) (Units.mk0 a h) : Cˣ) : C) := by
      rw [deningerUnitExtend, dif_neg h]
    have e2 : deningerUnitExtend χ (σ a) = ((χ (Units.mk0 (σ a) hσ) : Cˣ) : C) := by
      rw [deningerUnitExtend, dif_neg hσ]
    have e3 : (χ.comp (Units.map σ.toMonoidHom)) (Units.mk0 a h) = χ (Units.mk0 (σ a) hσ) := by
      show χ (Units.map σ.toMonoidHom (Units.mk0 a h)) = χ (Units.mk0 (σ a) hσ)
      congr 1
      exact Units.ext rfl
    rw [e1, e2, e3]

variable [TopologicalSpace C]

omit [TopologicalSpace C] in
/-- The evaluation of a section at the image of a character point is the evaluation of the
pullback of that section. -/
theorem deningerCharEval_map (f : X ⟶ Y) (V : Y.Opens) (g : Γ(Y, V))
    (P : DeningerCharPoints X C) :
    deningerCharEval V g (deningerCharPointsMap f P)
      = deningerCharEval (f ⁻¹ᵁ V) (f.app V g) P := by
  classical
  rw [deningerCharEval, deningerCharEval]
  by_cases h : (deningerCharPointsMap f P).1 ∈ V
  · have h' : P.1 ∈ f ⁻¹ᵁ V := h
    rw [dif_pos h, dif_pos h']
    show deningerUnitExtend (P.2.comp (Units.map (f.residueFieldMap P.1).hom.toMonoidHom)) _ = _
    rw [deningerUnitExtend_comp]
    congr 1
    exact Scheme.evaluation_naturality_apply f P.1 h g
  · have h' : P.1 ∉ f ⁻¹ᵁ V := h
    rw [dif_neg h, dif_neg h']

/-- The trace of the induced map over an affine open of the target. -/
noncomputable def deningerCharOverMap (f : X ⟶ Y) (V : Y.Opens)
    (P : DeningerCharOver X C (f ⁻¹ᵁ V)) : DeningerCharOver Y C V :=
  ⟨deningerCharPointsMap f P.val, P.mem⟩

theorem deningerCharOverMap_continuous (f : X ⟶ Y) (V : Y.Opens) :
    Continuous (deningerCharOverMap (C := C) f V) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun g => ?_
  have hfun : (fun P : DeningerCharOver X C (f ⁻¹ᵁ V) =>
      deningerCharEval V g (deningerCharOverMap f V P).val)
      = fun P : DeningerCharOver X C (f ⁻¹ᵁ V) =>
        deningerCharEval (f ⁻¹ᵁ V) (f.app V g) P.val := by
    funext P
    exact deningerCharEval_map f V g P.val
  show Continuous fun P : DeningerCharOver X C (f ⁻¹ᵁ V) =>
    deningerCharEval V g (deningerCharOverMap f V P).val
  rw [hfun]
  exact deningerCharEval_continuous _ _

/-- **Deninger, Lemma 7.3 (`t9`).**  An isomorphism of schemes induces a continuous map of
character points. -/
theorem deningerCharPointsMap_continuous (f : X ⟶ Y) [IsIso f] :
    Continuous (deningerCharPointsMap (C := C) f) := by
  rw [continuous_iSup_dom]
  rintro ⟨U, hU⟩
  rw [continuous_coinduced_dom]
  obtain ⟨V, hV, rfl⟩ : ∃ V : Y.Opens, IsAffineOpen V ∧ f ⁻¹ᵁ V = U := by
    refine ⟨inv f ⁻¹ᵁ U, hU.preimage_of_isIso (inv f), ?_⟩
    rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]
    simp
  have hcomp : (deningerCharPointsMap (C := C) f) ∘
      (DeningerCharOver.val (X := X) (C := C) (U := f ⁻¹ᵁ V))
      = (DeningerCharOver.val (X := Y) (C := C) (U := V)) ∘ deningerCharOverMap f V := rfl
  rw [hcomp]
  exact (deningerCharOverVal_continuous ⟨V, hV⟩).comp (deningerCharOverMap_continuous f V)

/-- **Deninger, Lemma 7.3 (`t9`).**  An isomorphism of schemes induces a homeomorphism of
character points. -/
noncomputable def deningerCharPointsHomeomorph (f : X ⟶ Y) [IsIso f] :
    DeningerCharPoints X C ≃ₜ DeningerCharPoints Y C where
  toFun := deningerCharPointsMap f
  invFun := deningerCharPointsMap (inv f)
  left_inv P := by
    rw [← deningerCharPointsMap_comp, IsIso.hom_inv_id, deningerCharPointsMap_id]
  right_inv Q := by
    rw [← deningerCharPointsMap_comp, IsIso.inv_hom_id, deningerCharPointsMap_id]
  continuous_toFun := deningerCharPointsMap_continuous f
  continuous_invFun := deningerCharPointsMap_continuous (inv f)

/-! ### The colimit -/

variable {N₀ : Submonoid ℕ}

variable (N₀) in
/-- The map induced on the colimit by a morphism of schemes. -/
noncomputable def deningerColimMap (f : X ⟶ Y) (z : DeningerColimPoints N₀ X C) :
    DeningerColimPoints N₀ Y C := by
  refine Quotient.liftOn z (fun P => deningerColimMk N₀ P.1 (deningerCharPointsMap f P.2)) ?_
  rintro ⟨μ, P⟩ ⟨μ', Q⟩ ⟨a, b, h1, h2⟩
  refine deningerColimMk_eq_iff.2 ⟨a, b, h1, ?_⟩
  rw [← deningerCharPointsMap_frobenius, ← deningerCharPointsMap_frobenius, h2]

omit [TopologicalSpace C] in
@[simp] theorem deningerColimMap_mk (f : X ⟶ Y) (μ : N₀) (P : DeningerCharPoints X C) :
    deningerColimMap N₀ f (deningerColimMk N₀ μ P)
      = deningerColimMk N₀ μ (deningerCharPointsMap f P) := rfl

theorem deningerColimMap_continuous (f : X ⟶ Y) [IsIso f] :
    Continuous (deningerColimMap (C := C) N₀ f) := by
  rw [continuous_iSup_dom]
  intro μ
  rw [continuous_coinduced_dom]
  have hcomp : (deningerColimMap (C := C) N₀ f) ∘ (deningerColimMk N₀ μ)
      = (deningerColimMk N₀ μ) ∘ (deningerCharPointsMap (C := C) f) := rfl
  rw [hcomp]
  exact (deningerColimMk_continuous μ).comp (deningerCharPointsMap_continuous f)

/-- **Deninger, Proposition 7.4(c) (`t10`).**  An isomorphism of schemes induces a homeomorphism
of `X̌ (C)`; in particular a group acting by automorphisms acts by homeomorphisms. -/
noncomputable def deningerColimHomeomorph (f : X ⟶ Y) [IsIso f] :
    DeningerColimPoints N₀ X C ≃ₜ DeningerColimPoints N₀ Y C where
  toFun := deningerColimMap N₀ f
  invFun := deningerColimMap N₀ (inv f)
  left_inv z := by
    obtain ⟨μ, P, rfl⟩ := deningerColimMk_surjective z
    rw [deningerColimMap_mk, deningerColimMap_mk, ← deningerCharPointsMap_comp,
      IsIso.hom_inv_id, deningerCharPointsMap_id]
  right_inv z := by
    obtain ⟨μ, P, rfl⟩ := deningerColimMk_surjective z
    rw [deningerColimMap_mk, deningerColimMap_mk, ← deningerCharPointsMap_comp,
      IsIso.inv_hom_id, deningerCharPointsMap_id]
  continuous_toFun := deningerColimMap_continuous f
  continuous_invFun := deningerColimMap_continuous (inv f)

end RHTower
