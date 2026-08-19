import GaloisForLFunctions.HTGeometry.GammaShiftSignatureOrder

/-!
# Distinct Gamma monomials have distinct logarithmic derivatives

The logarithmic derivative of `∏_k Γ(s + λ_k)^{e_k}` is `∑_k e_k ψ(s + λ_k)`.  The all-order
separation of `GammaShiftSumSeparation` therefore says exactly that the exponent vector is
determined by the logarithmic derivative, provided only that the shifts are **distinct** — no
independence over `ℤ` is needed anywhere.

This is the form cited by `archimedean-relative-prime-cocycle-curvature` and
`finite-archimedean-gamma-product-boundary-law`: the pairs `Γ(s+α)Γ(s+β)` and `Γ(s+α+β)Γ(s)`, which
share their leading shape, are separated here by the full Stirling signature.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- **The exponent vector is determined by the shifted digamma combination.** -/
theorem exponent_eq_of_digamma_shift_sum_eq {r : ℕ} (lam : Fin r → ℂ)
    (hinj : Function.Injective lam) (e f : Fin r → ℂ) (R : ℝ)
    (h : ∀ t : ℝ, R ≤ t → 1 ≤ t →
      ∑ k, e k * Complex.digamma (((t : ℝ) : ℂ) + lam k)
        = ∑ k, f k * Complex.digamma (((t : ℝ) : ℂ) + lam k)) :
    e = f := by
  have hg : ∀ t : ℝ, R ≤ t → 1 ≤ t →
      ‖∑ k, (e k - f k) * Complex.digamma (((t : ℝ) : ℂ) + lam k)‖ ≤ 0 / t ^ r := by
    intro t hR ht
    have hz : ∑ k, (e k - f k) * Complex.digamma (((t : ℝ) : ℂ) + lam k) = 0 := by
      have hsplit : ∀ k : Fin r, (e k - f k) * Complex.digamma (((t : ℝ) : ℂ) + lam k)
          = e k * Complex.digamma (((t : ℝ) : ℂ) + lam k)
            - f k * Complex.digamma (((t : ℝ) : ℂ) + lam k) := fun k => sub_mul _ _ _
      rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_sub_distrib, h t hR ht,
        sub_self]
    rw [hz]
    simp
  funext k
  have hzero := eq_zero_of_digamma_shift_sum_small lam hinj (fun k => e k - f k) 0 R hg k
  exact sub_eq_zero.mp hzero

/-- The natural-number form: two Gamma monomials with the same logarithmic derivative on a real ray
have the same exponents. -/
theorem natExponent_eq_of_digamma_shift_sum_eq {r : ℕ} (lam : Fin r → ℂ)
    (hinj : Function.Injective lam) (e f : Fin r → ℕ) (R : ℝ)
    (h : ∀ t : ℝ, R ≤ t → 1 ≤ t →
      ∑ k, (e k : ℂ) * Complex.digamma (((t : ℝ) : ℂ) + lam k)
        = ∑ k, (f k : ℂ) * Complex.digamma (((t : ℝ) : ℂ) + lam k)) :
    e = f := by
  have hcast := exponent_eq_of_digamma_shift_sum_eq lam hinj
    (fun k => (e k : ℂ)) (fun k => (f k : ℂ)) R h
  funext k
  have := congrFun hcast k
  exact_mod_cast this

end

end GaloisForLFunctions.HTGeometry
