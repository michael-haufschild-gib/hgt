import GaloisForLFunctions.RHTower.Deninger.DeningerSheafGluing

/-!
# Extension by zero and the injectivity of sections

Two more ingredients of the partition-of-unity argument.

A section of a subsheaf is determined by its image in the ambient sheaf, because a monomorphism of
sheaves is injective on sections: the free abelian sheaf on an open set corepresents sections, so a
section killed by a monomorphism corresponds to a map killed by it, hence to the zero map.

And if the support of a continuous function lies in an open set `W`, then the product of that
function with a section over `V ⊓ W` extends by zero to a section over `V`: the two open sets
`V ⊓ W` and `V ∖ supp ρ` cover `V`, and on their overlap the product vanishes because the function
does.

* `RHTower.deningerSections_injective` : a monomorphism of sheaves is injective on sections.
* `RHTower.deningerFineAction_extendByZero` : extension by zero of a section multiplied by a bump
  function.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}}

section Injective

/-- **A monomorphism of sheaves is injective on sections.** -/
theorem deningerSections_injective {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (φ : F ⟶ G)
    [Mono φ] (W : Opens X) {a b : ToType (F.1.obj (op W))}
    (h : ConcreteCategory.hom (φ.1.app (op W)) a = ConcreteCategory.hom (φ.1.app (op W)) b) :
    a = b := by
  set α : deningerOpenFree W ⟶ F := (deningerOpenFreeHomEquiv W F).symm a with hα
  set β : deningerOpenFree W ⟶ F := (deningerOpenFreeHomEquiv W F).symm b with hβ
  have hαa : deningerOpenFreeHomEquiv W F α = a := by rw [hα, Equiv.apply_symm_apply]
  have hβb : deningerOpenFreeHomEquiv W F β = b := by rw [hβ, Equiv.apply_symm_apply]
  have hcomp : α ≫ φ = β ≫ φ := by
    refine (deningerOpenFreeHomEquiv W G).injective ?_
    rw [deningerOpenFreeHomEquiv_naturality_right, deningerOpenFreeHomEquiv_naturality_right,
      hαa, hβb, h]
  have : α = β := (cancel_mono φ).1 hcomp
  rw [← hαa, ← hβb, this]

end Injective

section ExtendByZero

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X} {R : AddSubgroup C(X, ℝ)}

/-- The open complement of the support of a continuous function. -/
def deningerOffSupport (ρ : C(X, ℝ)) : Opens X :=
  ⟨(tsupport ρ)ᶜ, isClosed_closure.isOpen_compl⟩

theorem deningerOffSupport_apply_eq_zero {ρ : C(X, ℝ)} {x : X} (hx : x ∈ deningerOffSupport (ρ : C(X, ℝ))) :
    ρ x = 0 := by
  by_contra h
  exact hx (subset_tsupport ρ h)

/-- **Extension by zero.**  If the support of `ρ` lies in `W`, the product of `ρ` with a section
over `V ⊓ W` extends by zero to a section over `V`. -/
theorem deningerFineAction_extendByZero (A : DeningerFineAction F R) (ρ : ↥R) {V W : Opens X}
    (hsupp : tsupport (ρ : C(X, ℝ)) ⊆ (W : Set X)) (t : ToType (F.1.obj (op (V ⊓ W)))) :
    ∃ E : ToType (F.1.obj (op V)),
      deningerRes F (inf_le_left : V ⊓ W ≤ V) E = A.smul ρ (V ⊓ W) t ∧
      ∀ (Z : Opens X) (hZV : Z ≤ V), Z ≤ deningerOffSupport (ρ : C(X, ℝ)) →
        deningerRes F hZV E = 0 := by
  have hcov : V ≤ (V ⊓ W) ⊔ (V ⊓ deningerOffSupport (ρ : C(X, ℝ))) := by
    intro x hx
    by_cases hxs : x ∈ tsupport (ρ : C(X, ℝ))
    · exact Or.inl ⟨hx, hsupp hxs⟩
    · exact Or.inr ⟨hx, hxs⟩
  have hoverlap : deningerRes F
      (inf_le_left : (V ⊓ W) ⊓ (V ⊓ deningerOffSupport (ρ : C(X, ℝ))) ≤ V ⊓ W) (A.smul ρ (V ⊓ W) t)
      = deningerRes F (inf_le_right : (V ⊓ W) ⊓ (V ⊓ deningerOffSupport (ρ : C(X, ℝ)))
          ≤ V ⊓ deningerOffSupport (ρ : C(X, ℝ))) 0 := by
    rw [A.smul_res' ρ (inf_le_left : (V ⊓ W) ⊓ (V ⊓ deningerOffSupport (ρ : C(X, ℝ))) ≤ V ⊓ W) t,
      A.smul_eq_zero ρ ((V ⊓ W) ⊓ (V ⊓ deningerOffSupport (ρ : C(X, ℝ)))) _
        (fun y hy => deningerOffSupport_apply_eq_zero hy.2.2),
      deningerRes_zero]
  obtain ⟨E, hE1, hE2⟩ :=
    deningerGlue_two (F := F) (inf_le_left : V ⊓ W ≤ V)
      (inf_le_left : V ⊓ deningerOffSupport ρ ≤ V) hcov (A.smul ρ (V ⊓ W) t) 0 hoverlap
  refine ⟨E, hE1, fun Z hZV hZs => ?_⟩
  have hZ : Z ≤ V ⊓ deningerOffSupport ρ := le_inf hZV hZs
  rw [← deningerRes_res (inf_le_left : V ⊓ deningerOffSupport ρ ≤ V) hZ E, hE2,
    deningerRes_zero]

end ExtendByZero

end RHTower
