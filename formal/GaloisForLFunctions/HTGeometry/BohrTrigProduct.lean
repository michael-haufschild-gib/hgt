import GaloisForLFunctions.HTGeometry.BohrSpectralApprox

/-!
# The product of two trigonometric polynomials

The product of two trigonometric polynomials is a trigonometric polynomial whose frequencies are the
sums of the frequencies, so its Bohr coefficient at `λ` is the sum of the products of coefficients
over the pairs with `μ + ν = λ`.

In particular the coefficient vanishes as soon as every such pair has one vanishing factor — the
algebraic half of the spectral product rule.
-/

open MeasureTheory ComplexConjugate

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

theorem bohrExp_mul (mu nu t : ℝ) : bohrExp mu t * bohrExp nu t = bohrExp (mu + nu) t := by
  unfold bohrExp
  rw [bohrChar_mul]
  congr 1
  ring

/-- **The product of two trigonometric polynomials**, expanded over the product index set. -/
theorem trigPoly_mul (S T : Finset ℝ) (a b : ℝ → ℂ) (t : ℝ) :
    trigPoly S a t * trigPoly T b t
      = ∑ p ∈ S ×ˢ T, (a p.1 * b p.2) * bohrExp (p.1 + p.2) t := by
  classical
  rw [trigPoly, trigPoly, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show a p.1 * bohrExp p.1 t * (b p.2 * bohrExp p.2 t)
      = (a p.1 * b p.2) * (bohrExp p.1 t * bohrExp p.2 t) by ring, bohrExp_mul]

/-- **The Bohr coefficients of a product of trigonometric polynomials.** -/
theorem bohrCoefficient_trigPoly_mul (S T : Finset ℝ) (a b : ℝ → ℂ) (lam : ℝ) :
    bohrCoefficient (fun t => trigPoly S a t * trigPoly T b t) lam
      = ∑ p ∈ S ×ˢ T, if p.1 + p.2 = lam then a p.1 * b p.2 else 0 := by
  classical
  have hfun : (fun t : ℝ => trigPoly S a t * trigPoly T b t)
      = fun t : ℝ => ∑ p ∈ S ×ˢ T, (a p.1 * b p.2) * bohrExp (p.1 + p.2) t :=
    funext fun t => trigPoly_mul S T a b t
  rw [hfun]
  exact bohrCoefficient_trigPoly (S ×ˢ T) (fun p => a p.1 * b p.2) (fun p => p.1 + p.2) lam

/-- **The algebraic half of the spectral product rule.**  If every pair of frequencies summing to
`λ` has a vanishing coefficient, the product has no `λ`-mode. -/
theorem bohrCoefficient_trigPoly_mul_eq_zero (S T : Finset ℝ) (a b : ℝ → ℂ) (lam : ℝ)
    (h : ∀ mu ∈ S, ∀ nu ∈ T, mu + nu = lam → a mu * b nu = 0) :
    bohrCoefficient (fun t => trigPoly S a t * trigPoly T b t) lam = 0 := by
  classical
  rw [bohrCoefficient_trigPoly_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_product] at hp
  by_cases hsum : p.1 + p.2 = lam
  · rw [if_pos hsum]
    exact h p.1 hp.1 p.2 hp.2 hsum
  · rw [if_neg hsum]

end

end GaloisForLFunctions
