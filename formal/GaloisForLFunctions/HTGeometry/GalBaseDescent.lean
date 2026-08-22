import GaloisForLFunctions.HTGeometry.CubeSwapGaloisAssembly

/-!
# Descending the Galois group along a base field extension

Enlarging the base field can only shrink the Galois group, so a symmetric Galois group over a larger
base forces a symmetric Galois group over the smaller one.  This is how a computation carried out
over `ℚ(i)` returns a statement over `ℚ`.

## Main results

* `card_gal_eq_factorial_of_baseExtension` — the descent.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Descent along a base field extension.**  A generating set of permutations realized by
`L`-automorphisms is realized by `K`-automorphisms, so the Galois group over `K` is symmetric as
soon as the one over `L` is. -/
theorem card_gal_eq_factorial_of_cubeSwaps_baseExtension
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E] {N : ℕ}
    (f : Polynomial K) [Fact (f.map (algebraMap K E)).Splits]
    {θ : (Fin N → Bool) → E} (hinj : Function.Injective θ)
    (hsplit : f.map (algebraMap K E) = ∏ x, (X - C (θ x)))
    (hswap : ∀ (x : Fin N → Bool) (i : Fin N),
      ∃ σ : E ≃ₐ[L] E, ∀ y, σ (θ y) = θ (Equiv.swap x (boolToggle x i) y)) :
    Nat.card f.Gal = (2 ^ N).factorial := by
  refine card_gal_eq_factorial_of_cubeSwaps f hinj hsplit ?_
  intro x i
  obtain ⟨σ, hσ⟩ := hswap x i
  exact ⟨σ.restrictScalars K, hσ⟩

end

end GaloisForLFunctions.HTGeometry
