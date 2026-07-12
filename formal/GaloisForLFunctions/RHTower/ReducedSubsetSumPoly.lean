import GaloisForLFunctions.RHTower.SubsetSumPolynomial

/-!
# The reduced subset-sum polynomial

`exp_polynomial_approx` requires an integer polynomial `g` with `g(0) ≠ 0` — the empty subset gives
`σ_∅ = 0`, a root that must be removed.  Starting from the integer polynomial `f` whose complex roots
are the subset sums `σ_S` (`exists_int_poly_subsetSum_roots`), factor out the maximal power of `X`:
`f = X^k · g` with `g(0) ≠ 0`.  Every *nonzero* subset sum `σ_S` remains a root of `g` (dividing by
`σ_S^k ≠ 0`), so `g` is the integer polynomial `exp_polynomial_approx` consumes in the non-monic
Lindemann–Weierstrass finish for the Euler relation `∏_j (1 + e^{θ_j}) = 0`.
-/

open Polynomial Finset

namespace GaloisForLFunctions
namespace RHTower

/-- **The reduced subset-sum polynomial.**  For nonzero `μ ∈ ℤ[X]` with factorization
`μ.map = C ℓ · ∏_j (X − θ_j)`, there is an integer polynomial `g` with `g(0) ≠ 0` such that every
nonzero subset sum `σ_S = ∑_{j∈S} θ_j` is a complex root of `g`.  Obtained by removing the maximal
`X`-power (the `σ_∅ = 0` root) from the subset-sum polynomial. -/
theorem exists_reduced_subsetSum_poly {d : ℕ} (μ : ℤ[X]) (hμ0 : μ ≠ 0) (θ : Fin d → ℂ)
    (hθ : μ.map (Int.castRingHom ℂ)
        = C ((μ.leadingCoeff : ℤ) : ℂ) * (Multiset.map (fun j => X - C (θ j)) Finset.univ.val).prod) :
    ∃ g : ℤ[X], g.eval 0 ≠ 0 ∧
      ∀ S ∈ (Finset.univ : Finset (Fin d)).powerset, (∑ j ∈ S, θ j) ≠ 0 →
        (∑ j ∈ S, θ j) ∈ g.aroots ℂ := by
  obtain ⟨f, hf⟩ := exists_int_poly_subsetSum_roots μ hμ0 θ hθ
  set ℓ : ℤ := μ.leadingCoeff with hℓ
  have hℓ0 : ℓ ≠ 0 := by rw [hℓ]; exact Polynomial.leadingCoeff_ne_zero.mpr hμ0
  have hℓC0 : (((ℓ : ℤ) : ℂ)) ^ (2 ^ d) ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.mpr hℓ0)
  have hfmap_ne : f.map (Int.castRingHom ℂ) ≠ 0 := by
    rw [hf]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hℓC0)
      (Finset.prod_ne_zero_iff.mpr (fun T _ => Polynomial.X_sub_C_ne_zero _))
  have hf0 : f ≠ 0 := fun h => hfmap_ne (by rw [h, Polynomial.map_zero])
  set k := f.natTrailingDegree with hk
  have hdvd : Polynomial.X ^ k ∣ f :=
    Polynomial.X_pow_dvd_iff.mpr (fun e he => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree he)
  obtain ⟨g, hg⟩ := hdvd
  have hg0 : g.coeff 0 ≠ 0 := by
    have hcoeff : f.coeff k = g.coeff 0 := by
      have := Polynomial.coeff_X_pow_mul g k 0; rwa [Nat.zero_add, ← hg] at this
    rw [← hcoeff]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hf0
  have hfactor : f.map (Int.castRingHom ℂ)
      = Polynomial.X ^ k * g.map (Int.castRingHom ℂ) := by
    rw [hg, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  refine ⟨g, by rw [← Polynomial.coeff_zero_eq_eval_zero]; exact hg0, ?_⟩
  intro S hS hne
  have hgne : g ≠ 0 := by intro h; apply hf0; rw [hg, h, mul_zero]
  have hfr : (f.map (Int.castRingHom ℂ)).eval (∑ j ∈ S, θ j) = 0 := by
    rw [hf, Polynomial.eval_mul, Polynomial.eval_C]
    apply mul_eq_zero_of_right
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_zero hS ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
  rw [hfactor, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hfr
  have hgr : (g.map (Int.castRingHom ℂ)).eval (∑ j ∈ S, θ j) = 0 :=
    (mul_eq_zero.mp hfr).resolve_left (pow_ne_zero _ hne)
  rw [Polynomial.mem_aroots]
  refine ⟨hgne, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  exact hgr

end RHTower
end GaloisForLFunctions
