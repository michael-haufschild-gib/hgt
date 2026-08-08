import GaloisForLFunctions.HTGeometry.SymmetricConjugateIntegral
import GaloisForLFunctions.RHTower.IntegralizedConjugateSet

/-!
# The subset-sum polynomial of a non-monic conjugate set

To run the Lindemann–Weierstrass estimate on the Euler relation `∏_j (1 + e^{θ_j}) = 0`, whose
expanded form is `∑_S e^{σ_S} = 0` with `σ_S = ∑_{j∈S} θ_j`, one needs an integer polynomial whose
complex roots are the subset sums `σ_S`.  For a *non-monic* conjugate set — the `θ_j` are algebraic
but not algebraic integers — the subset sums are not algebraic integers either, so the naive product
`∏_S (X − σ_S)` is not an integer polynomial.  Two integer polynomials are produced here.

* `exists_nonmonic_subsetSum_poly`: the *scaled* subset sums `ℓ·σ_S` are algebraic integers (subset
  sums of the algebraic integers `ℓ·θ_j`, which are the roots of `integralNormalization μ`), so
  `∏_S (X − ℓ·σ_S)` lifts to an integer polynomial `G` via the monic `subsetSum_poly_lifts`.
* `exists_int_poly_subsetSum_roots`: substituting `X ↦ ℓ·X` in `G` produces an integer polynomial `f`
  with `f.map = C(ℓ^{2^d}) · ∏_S (X − σ_S)` — a genuine integer polynomial whose complex roots are the
  *unscaled* subset sums `σ_S`, ready for `exp_polynomial_approx`.
-/

open Polynomial Finset

namespace GaloisForLFunctions
namespace RHTower

/-- **The scaled subset-sum polynomial lifts.**  For nonzero `μ ∈ ℤ[X]` with leading coefficient `ℓ`
and factorization `μ.map = C ℓ · ∏_j (X − θ_j)`, the polynomial `∏_S (X − ℓ·σ_S)` whose roots are the
scaled subset sums `ℓ·σ_S = ∑_{j∈S} ℓ·θ_j` is the image of an integer polynomial — the scaled roots
`ℓ·θ_j` are the roots of the monic `integralNormalization μ`. -/
theorem exists_nonmonic_subsetSum_poly {d : ℕ} (μ : ℤ[X]) (hμ0 : μ ≠ 0) (θ : Fin d → ℂ)
    (hθ : μ.map (Int.castRingHom ℂ)
        = C ((μ.leadingCoeff : ℤ) : ℂ) * (Multiset.map (fun j => X - C (θ j)) Finset.univ.val).prod) :
    ∃ G : ℤ[X], G.map (Int.castRingHom ℂ)
      = ∏ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          (X - C (∑ j ∈ T, ((μ.leadingCoeff : ℤ) : ℂ) * θ j)) := by
  obtain ⟨G, hG⟩ := subsetSum_poly_lifts (integralNormalization μ)
    (fun j => ((μ.leadingCoeff : ℤ) : ℂ) * θ j) (exists_integralized_monic μ hμ0 θ hθ)
  exact ⟨G, hG⟩

/-- **An integer polynomial with the unscaled subset sums as roots.**  For nonzero `μ ∈ ℤ[X]` with
leading coefficient `ℓ` and factorization `μ.map = C ℓ · ∏_j (X − θ_j)`, there is an integer
polynomial `f` with `f.map = C(ℓ^{2^d}) · ∏_S (X − σ_S)`; its complex roots are exactly the subset
sums `σ_S = ∑_{j∈S} θ_j`.  Built by substituting `X ↦ ℓ·X` into the scaled subset-sum polynomial. -/
theorem exists_int_poly_subsetSum_roots {d : ℕ} (μ : ℤ[X]) (hμ0 : μ ≠ 0) (θ : Fin d → ℂ)
    (hθ : μ.map (Int.castRingHom ℂ)
        = C ((μ.leadingCoeff : ℤ) : ℂ) * (Multiset.map (fun j => X - C (θ j)) Finset.univ.val).prod) :
    ∃ f : ℤ[X], f.map (Int.castRingHom ℂ)
      = C (((μ.leadingCoeff : ℤ) : ℂ) ^ (2 ^ d))
        * ∏ T ∈ (Finset.univ : Finset (Fin d)).powerset, (X - C (∑ j ∈ T, θ j)) := by
  set ℓ : ℤ := μ.leadingCoeff with hℓ
  obtain ⟨G, hG⟩ := subsetSum_poly_lifts (integralNormalization μ)
    (fun j => ((ℓ : ℤ) : ℂ) * θ j) (exists_integralized_monic μ hμ0 θ hθ)
  simp only [Polynomial.coe_mapRingHom] at hG
  refine ⟨G.comp (C ℓ * X), ?_⟩
  rw [Polynomial.map_comp, hG, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.prod_comp]
  have hcard : (Finset.univ : Finset (Fin d)).powerset.card = 2 ^ d := by
    rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  calc ∏ T ∈ (Finset.univ : Finset (Fin d)).powerset,
        (X - C (∑ j ∈ T, ((ℓ : ℤ) : ℂ) * θ j)).comp (C ((ℓ : ℤ) : ℂ) * X)
      = ∏ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          C ((ℓ : ℤ) : ℂ) * (X - C (∑ j ∈ T, θ j)) := by
        refine Finset.prod_congr rfl (fun T _ => ?_)
        rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, mul_sub, ← C_mul,
          Finset.mul_sum]
    _ = C (((ℓ : ℤ) : ℂ) ^ (2 ^ d)) * ∏ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          (X - C (∑ j ∈ T, θ j)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, ← C_pow]

end RHTower
end GaloisForLFunctions
