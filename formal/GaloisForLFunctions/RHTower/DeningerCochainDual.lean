import GaloisForLFunctions.RHTower.DeningerFinsuppDual

/-!
# The cochain differential is dual to the chain differential

For trivial coefficients the differential of the inhomogeneous cochains is the dual of the
differential of the inhomogeneous chains, under the identification of the dual of finitely supported
functions with all functions.  Both are the same alternating sum, one acting on tuples and one
precomposing with them.

* `deningerCochain_d_dual` : the identification of the differentials.
-/

namespace RHTower

universe u

/-- **The cochain differential is dual to the chain differential**, for trivial coefficients. -/
theorem deningerCochain_d_dual (k G : Type u) [Field k] [Group G] (n : ℕ)
    (f : Module.Dual k ((Fin n → G) →₀ k)) (g : Fin (n + 1) → G) :
    deningerFinsuppDual k (Fin (n + 1) → G)
        (f ∘ₗ (groupHomology.inhomogeneousChains.d (Rep.trivial k G k) n).hom) g =
      inhomogeneousCochains.d (Rep.trivial k G k) n
        (deningerFinsuppDual k (Fin n → G) f) g := by
  show f ((groupHomology.inhomogeneousChains.d (Rep.trivial k G k) n).hom (Finsupp.single g 1)) = _
  rw [groupHomology.inhomogeneousChains.d_single]
  show f (Finsupp.single (fun i => g i.succ) _ + _) = _
  rw [map_add, map_sum]
  show _ = (Rep.trivial k G k).ρ (g 0) (deningerFinsuppDual k (Fin n → G) f
    (fun i => g i.succ)) + _
  simp only [deningerFinsuppDual_apply, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine congrArg (fun t => f (Finsupp.single (fun i => g i.succ) 1) + t) ?_
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (Finsupp.single (Fin.contractNth j (· * ·) g) ((-1 : k) ^ ((j : ℕ) + 1))) =
      ((-1 : k) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) (1 : k) by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

end RHTower
