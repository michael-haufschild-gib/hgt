import GaloisForLFunctions.Core

/-!
# Linearizing a set-indexed attachment

Attaching one generator for every element of the underlying set of a module produces the free
module on that set.  The evaluation map back to the module is surjective, and its kernel contains
the three linearity defects of the set-indexed assignment: the generator at zero, the failure of
additivity, and the failure of homogeneity.

Quotienting by the span of exactly those three families returns the module itself.  So replacing
a set-indexed attachment by the module removes the additive attachment syzygies and nothing else.

* `deningerFreeEval` : the evaluation of the free module on the underlying set.
* `deningerLinearityRelations` : the three linearity defects.
* `deningerLinearizationEquiv` : **the quotient by them is the module.**
-/

namespace RHTower

open Finsupp

noncomputable section

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

/-- The evaluation map of the free module on the underlying set of `V`. -/
def deningerFreeEval : (V →₀ k) →ₗ[k] V :=
  Finsupp.linearCombination k id

@[simp]
theorem deningerFreeEval_single (v : V) (a : k) :
    deningerFreeEval k V (Finsupp.single v a) = a • v := by
  rw [deningerFreeEval, Finsupp.linearCombination_single]
  rfl

theorem deningerFreeEval_surjective : Function.Surjective (deningerFreeEval k V) := by
  intro v
  refine ⟨Finsupp.single v 1, ?_⟩
  rw [deningerFreeEval_single, one_smul]

/-- **The three linearity defects** of a set-indexed attachment. -/
def deningerLinearityRelations : Submodule k (V →₀ k) :=
  Submodule.span k
    ({Finsupp.single (0 : V) (1 : k)} ∪
      {x | ∃ u v : V, x = Finsupp.single (u + v) (1 : k)
        - Finsupp.single u (1 : k) - Finsupp.single v (1 : k)} ∪
      {x | ∃ (a : k) (u : V), x = Finsupp.single (a • u) (1 : k)
        - a • Finsupp.single u (1 : k)})

theorem deningerLinearityRelations_le_ker :
    deningerLinearityRelations k V ≤ LinearMap.ker (deningerFreeEval k V) := by
  rw [deningerLinearityRelations, Submodule.span_le]
  rintro x (hx | hx)
  · rcases hx with hx | hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      show deningerFreeEval k V (Finsupp.single (0 : V) (1 : k)) = 0
      rw [deningerFreeEval_single, smul_zero]
    · obtain ⟨u, v, rfl⟩ := hx
      show deningerFreeEval k V _ = 0
      rw [map_sub, map_sub, deningerFreeEval_single, deningerFreeEval_single,
        deningerFreeEval_single, one_smul, one_smul, one_smul]
      abel
  · obtain ⟨a, u, rfl⟩ := hx
    show deningerFreeEval k V _ = 0
    rw [map_sub, map_smul, deningerFreeEval_single, deningerFreeEval_single, one_smul,
      one_smul, sub_self]

/-- The class of the basis vector at a point, as a map from the module. -/
private def deningerLinearizationSection :
    V →ₗ[k] ((V →₀ k) ⧸ deningerLinearityRelations k V) where
  toFun v := Submodule.Quotient.mk (Finsupp.single v (1 : k))
  map_add' u v := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    have hmem : Finsupp.single (u + v) (1 : k)
        - (Finsupp.single u (1 : k) + Finsupp.single v (1 : k))
        ∈ deningerLinearityRelations k V := by
      have hrel : Finsupp.single (u + v) (1 : k)
          - (Finsupp.single u (1 : k) + Finsupp.single v (1 : k))
          = Finsupp.single (u + v) (1 : k) - Finsupp.single u (1 : k)
            - Finsupp.single v (1 : k) := by abel
      rw [hrel, deningerLinearityRelations]
      exact Submodule.subset_span (Or.inl (Or.inr ⟨u, v, rfl⟩))
    exact hmem
  map_smul' a v := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    have hmem : Finsupp.single (a • v) (1 : k) - a • Finsupp.single v (1 : k)
        ∈ deningerLinearityRelations k V := by
      rw [deningerLinearityRelations]
      exact Submodule.subset_span (Or.inr ⟨a, v, rfl⟩)
    exact hmem

/-- **Quotienting the set-indexed free module by the linearity relations returns the module.** -/
def deningerLinearizationEquiv :
    ((V →₀ k) ⧸ deningerLinearityRelations k V) ≃ₗ[k] V :=
  LinearEquiv.ofLinear
    (Submodule.liftQ _ (deningerFreeEval k V) (deningerLinearityRelations_le_ker k V))
    (deningerLinearizationSection k V)
    (by
      ext v
      show deningerFreeEval k V (Finsupp.single v (1 : k)) = v
      rw [deningerFreeEval_single, one_smul])
    (by
      ext x
      show deningerLinearizationSection k V
          (deningerFreeEval k V (Finsupp.single x (1 : k)))
        = Submodule.Quotient.mk (Finsupp.single x (1 : k))
      rw [deningerFreeEval_single, one_smul]
      rfl)

@[simp]
theorem deningerLinearizationEquiv_mk (v : V) :
    deningerLinearizationEquiv k V
        (Submodule.Quotient.mk (Finsupp.single v (1 : k))) = v := by
  show deningerFreeEval k V (Finsupp.single v (1 : k)) = v
  rw [deningerFreeEval_single, one_smul]

end

end RHTower
