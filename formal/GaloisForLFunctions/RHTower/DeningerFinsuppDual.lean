import GaloisForLFunctions.RHTower.DeningerDualVanishing

/-!
# The dual of a space of finitely supported functions

The dual of the finitely supported functions on a set is the space of all functions on it.  This is
the module level statement behind the cochain complex of a group being the dual of its chain
complex: chains are finitely supported functions on tuples, cochains are all functions on tuples.

* `deningerFinsuppDual` : the identification.
-/

namespace RHTower

universe u

/-- **The dual of the finitely supported functions on a set is all functions on it.** -/
noncomputable def deningerFinsuppDual (k α : Type u) [Field k] :
    Module.Dual k (α →₀ k) ≃ₗ[k] (α → k) :=
  (Finsupp.lsum (R := k) (S := k) (M := k) (N := k) (α := α)).symm.trans
    (LinearEquiv.piCongrRight (fun _ => LinearMap.ringLmapEquivSelf k k k))

@[simp] theorem deningerFinsuppDual_apply (k α : Type u) [Field k] (f : Module.Dual k (α →₀ k))
    (a : α) : deningerFinsuppDual k α f a = f (Finsupp.single a 1) := rfl

end RHTower
