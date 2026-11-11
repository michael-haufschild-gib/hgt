import Mathlib

/-!
# Two Gauss sums with a quadratic product carry the Möbius sign

A probe of the family continuation has rows whose coefficients are the Gauss sums of a character
`χ` and a row twist `φ`; Poisson summation in the row variable multiplies the coefficient by the
Gauss sum of `φ`. For multiplicative characters `χ, φ` of a finite field with `χ φ ≠ 1`,

`g(χ) g(φ) = J(χ, φ) g(χ φ)`,

and for characters of order dividing `n > 2` the Jacobi sum is `−1` modulo `(μ − 1)²` in `ℤ[μ]`,
`μ` a primitive `n`-th root of unity. When `χ φ` is the quadratic character its Gauss sum is
explicit, `g(χ φ)² = (χ φ)(−1) · card F`: the product of the two Gauss sums is the Möbius sign
times explicit factors. One Jacobi sum carries the sign.

* `exists_gaussSum_mul_gaussSum_eq`: `g(χ) g(φ) = (−1 + z (μ − 1)²) g(χ φ)`.
* `exists_gaussSum_mul_gaussSum_sq_eq`: for `χ φ` quadratic,
  `(g(χ) g(φ))² = (−1 + z (μ − 1)²)² (χ φ)(−1) card F`.
* `exists_gaussSum_sq_eq`: the case `φ = χ`. For a character of order four the square of the
  Gauss sum is the sign times the quadratic Gauss sum.
* `sq_eq_one_of_mul_sq_eq_one`: the twist is not quadratic unless the coefficient is: if
  `φ² = 1` and `(χ φ)² = 1` then `χ² = 1`.

The twist is `φ = (χ φ) χ⁻¹`. A cubic coefficient has a sextic twist, a coefficient of order four
has itself as twist, a sextic coefficient has a cubic twist.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory

variable {F : Type*} [Field F] [Fintype F] {R : Type*} [CommRing R] [IsDomain R]

/-- **The source identity.** The product of two Gauss sums is the Gauss sum of the product
character times a Jacobi sum `≡ −1` modulo `(μ − 1)²`. -/
theorem exists_gaussSum_mul_gaussSum_eq {n : ℕ} (hn : 2 < n) {χ φ : MulChar F R} {μ : R}
    (hχ : χ ^ n = 1) (hφ : φ ^ n = 1) (hn' : n ∣ Fintype.card F - 1)
    (hμ : IsPrimitiveRoot μ n) (h : χ * φ ≠ 1) (ψ : AddChar F R) :
    ∃ z ∈ Algebra.adjoin ℤ {μ},
      gaussSum χ ψ * gaussSum φ ψ = (-1 + z * (μ - 1) ^ 2) * gaussSum (χ * φ) ψ := by
  obtain ⟨z, hz, hJ⟩ := exists_jacobiSum_eq_neg_one_add hn hχ hφ hn' hμ
  refine ⟨z, hz, ?_⟩
  rw [← jacobiSum_mul_nontrivial h ψ, hJ, mul_comm]

/-- **A quadratic product.** If `χ φ` is the quadratic character, the square of the product of
the two Gauss sums is the square of the sign factor times `(χ φ)(−1) · card F`. -/
theorem exists_gaussSum_mul_gaussSum_sq_eq {n : ℕ} (hn : 2 < n) {χ φ : MulChar F R} {μ : R}
    (hχ : χ ^ n = 1) (hφ : φ ^ n = 1) (hn' : n ∣ Fintype.card F - 1)
    (hμ : IsPrimitiveRoot μ n) (h : χ * φ ≠ 1) (hq : (χ * φ).IsQuadratic)
    {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    ∃ z ∈ Algebra.adjoin ℤ {μ},
      (gaussSum χ ψ * gaussSum φ ψ) ^ 2 =
        (-1 + z * (μ - 1) ^ 2) ^ 2 * ((χ * φ) (-1) * (Fintype.card F : R)) := by
  obtain ⟨z, hz, hg⟩ := exists_gaussSum_mul_gaussSum_eq hn hχ hφ hn' hμ h ψ
  refine ⟨z, hz, ?_⟩
  rw [hg, mul_pow, gaussSum_sq h hq hψ]

/-- **The square of a Gauss sum.** For a character whose square is nontrivial,
`g(χ)² = (−1 + z (μ − 1)²) g(χ²)`. -/
theorem exists_gaussSum_sq_eq {n : ℕ} (hn : 2 < n) {χ : MulChar F R} {μ : R} (hχ : χ ^ n = 1)
    (hn' : n ∣ Fintype.card F - 1) (hμ : IsPrimitiveRoot μ n) (h : χ ^ 2 ≠ 1)
    (ψ : AddChar F R) :
    ∃ z ∈ Algebra.adjoin ℤ {μ},
      gaussSum χ ψ ^ 2 = (-1 + z * (μ - 1) ^ 2) * gaussSum (χ ^ 2) ψ := by
  have h' : χ * χ ≠ 1 := by rwa [← pow_two]
  obtain ⟨z, hz, hg⟩ := exists_gaussSum_mul_gaussSum_eq hn hχ hχ hn' hμ h' ψ
  refine ⟨z, hz, ?_⟩
  rw [pow_two (gaussSum χ ψ), hg, pow_two χ]

omit [Fintype F] [IsDomain R] in
/-- If the twist `φ` and the product `χ φ` are both of order at most two, so is `χ`. -/
theorem sq_eq_one_of_mul_sq_eq_one {χ φ : MulChar F R} (hφ : φ ^ 2 = 1)
    (h : (χ * φ) ^ 2 = 1) : χ ^ 2 = 1 := by
  rwa [mul_pow, hφ, mul_one] at h

end GaloisForLFunctions.FamilyContinuationTheory
