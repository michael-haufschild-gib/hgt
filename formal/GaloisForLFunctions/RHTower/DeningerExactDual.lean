import GaloisForLFunctions.RHTower.DeningerCochainDual

/-!
# Exactness is preserved by dualizing

Over a field, dualizing a pair of composable maps which is exact in the middle gives a pair which is
exact in the middle: a functional killing the image extends along the quotient and then along a
complement of the image.

* `deningerExact_dualMap` : exactness of the dual.
-/

namespace RHTower

universe u

variable {k A B C : Type u} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

/-- **Dualizing preserves exactness in the middle.** -/
theorem deningerExact_dualMap (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (h : LinearMap.ker g = LinearMap.range f) :
    LinearMap.ker f.dualMap = LinearMap.range g.dualMap := by
  apply le_antisymm
  · intro ψ hψ
    have hker : LinearMap.ker g ≤ LinearMap.ker ψ := by
      intro b hb
      rw [h] at hb
      obtain ⟨a, rfl⟩ := hb
      exact congrFun (congrArg DFunLike.coe hψ) a
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range g)
    refine ⟨((Submodule.liftQ (LinearMap.ker g) ψ hker).comp
      (LinearMap.quotKerEquivRange g).symm.toLinearMap).comp
      (Submodule.projectionOnto _ _ hW), ?_⟩
    ext b
    show (Submodule.liftQ (LinearMap.ker g) ψ hker)
      ((LinearMap.quotKerEquivRange g).symm
        (Submodule.projectionOnto _ _ hW (g b))) = ψ b
    rw [show Submodule.projectionOnto (LinearMap.range g) W hW (g b) =
        (⟨g b, ⟨b, rfl⟩⟩ : LinearMap.range g) from
      Submodule.projectionOnto_apply_left hW ⟨g b, ⟨b, rfl⟩⟩]
    rw [show ((LinearMap.quotKerEquivRange g).symm (⟨g b, ⟨b, rfl⟩⟩ : LinearMap.range g)) =
        Submodule.Quotient.mk b from by
      apply (LinearMap.quotKerEquivRange g).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl]
    rfl
  · rintro _ ⟨φ, rfl⟩
    ext a
    have hgf : g (f a) = 0 := by
      have hmem : f a ∈ LinearMap.range f := ⟨a, rfl⟩
      rw [← h] at hmem
      exact hmem
    show φ (g (f a)) = 0
    rw [hgf, map_zero]

end RHTower
