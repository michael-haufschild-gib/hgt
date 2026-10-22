import GaloisForLFunctions.RHTower.Deninger.DeningerExactDual

/-!
# Exactness in the middle transports along an isomorphism of three-term sequences

Exactness in the middle of a three term sequence depends only on the sequence up to isomorphism:
if three linear equivalences carry one pair of composable maps to another, then the kernel of the
second equals the image of the first on one side exactly when it does on the other.

* `deningerKer_eq_range_congr` : the transport.
-/

namespace RHTower

universe u

variable {k A B C A' B' C' : Type u} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
  [AddCommGroup A'] [Module k A'] [AddCommGroup B'] [Module k B'] [AddCommGroup C'] [Module k C']

/-- **Exactness in the middle transports along an isomorphism of three term sequences.** -/
theorem deningerKer_eq_range_congr (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (f' : A' →ₗ[k] B') (g' : B' →ₗ[k] C')
    (eA : A ≃ₗ[k] A') (eB : B ≃ₗ[k] B') (eC : C ≃ₗ[k] C')
    (hf : eB.toLinearMap ∘ₗ f = f' ∘ₗ eA.toLinearMap)
    (hg : eC.toLinearMap ∘ₗ g = g' ∘ₗ eB.toLinearMap)
    (h : LinearMap.ker g = LinearMap.range f) :
    LinearMap.ker g' = LinearMap.range f' := by
  have hfa : ∀ a : A, eB (f a) = f' (eA a) := fun a => congrFun (congrArg DFunLike.coe hf) a
  have hga : ∀ b : B, eC (g b) = g' (eB b) := fun b => congrFun (congrArg DFunLike.coe hg) b
  ext x
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    have hgx : g (eB.symm x) = 0 := by
      apply eC.injective
      rw [hga, eB.apply_symm_apply, hx, map_zero]
    have hmem : eB.symm x ∈ LinearMap.range f := by
      rw [← h]
      exact hgx
    obtain ⟨a, ha⟩ := hmem
    exact ⟨eA a, by rw [← hfa, ha, eB.apply_symm_apply]⟩
  · rintro ⟨a', rfl⟩
    have hfe : f' a' = eB (f (eA.symm a')) := by rw [hfa, eA.apply_symm_apply]
    have hmem : f (eA.symm a') ∈ LinearMap.ker g := by
      rw [h]
      exact ⟨eA.symm a', rfl⟩
    rw [hfe, ← hga, LinearMap.mem_ker.1 hmem, map_zero]

end RHTower
