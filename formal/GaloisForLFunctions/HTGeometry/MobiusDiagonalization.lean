import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A Möbius map with two fixed points is a scaling

If a `C`-algebra automorphism `σ` of `E` acts on a generator `q` by a Möbius transform
`σ q · (c q + d) = a q + b`, and `p₁, p₂ ∈ C` are two fixed points (roots of the fixed-point
quadratic `c p² + (d − a) p − b = 0`), then in the fixed-point coordinate
`x = (q − p₁)/(q − p₂)` the action is a pure scaling:

`σ x = ((a − c p₁)/(a − c p₂)) · x`.

This is the diagonalization step of the `PGL₂`-cocharacter classification (§3): once the clock's
Möbius family has a common fixed-point pair, each member acts diagonally, so the family is a
character `χ(λ)` — which the monomial lemma then identifies with `λ^k`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {C E : Type*} [Field C] [Field E] [Algebra C E]

/-- A fixed point `p` of the Möbius map sends the difference `q − p` to a scalar multiple:
`σ(q − p) · (c q + d) = (a − c p)·(q − p)`. -/
theorem mobius_fixed_point_difference (σ : E ≃ₐ[C] E) {a b c d p : C} {q : E}
    (hσq : σ q * (algebraMap C E c * q + algebraMap C E d)
      = algebraMap C E a * q + algebraMap C E b)
    (hfix : c * p ^ (2 : ℕ) + (d - a) * p - b = 0) :
    σ (q - algebraMap C E p) * (algebraMap C E c * q + algebraMap C E d)
      = algebraMap C E (a - c * p) * (q - algebraMap C E p) := by
  have hfixE : algebraMap C E c * (algebraMap C E p) ^ (2 : ℕ)
      + (algebraMap C E d - algebraMap C E a) * algebraMap C E p
      - algebraMap C E b = 0 := by
    have h := congrArg (algebraMap C E) hfix
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
    linear_combination h
  rw [map_sub, AlgEquiv.commutes,
    show (σ q - algebraMap C E p) * (algebraMap C E c * q + algebraMap C E d)
      = σ q * (algebraMap C E c * q + algebraMap C E d)
        - algebraMap C E p * (algebraMap C E c * q + algebraMap C E d) from by ring,
    hσq, map_sub, map_mul]
  linear_combination -hfixE

/-- **Two fixed points diagonalize a Möbius map.**  With `p₁, p₂` fixed points, the fixed-point
coordinate is a scaling eigenvector: `σ x = χ · x`, `χ = (a − c p₁)/(a − c p₂)`. -/
theorem mobius_two_fixed_points_scaling (σ : E ≃ₐ[C] E) {a b c d p₁ p₂ : C} {q : E}
    (hσq : σ q * (algebraMap C E c * q + algebraMap C E d)
      = algebraMap C E a * q + algebraMap C E b)
    (hfix1 : c * p₁ ^ (2 : ℕ) + (d - a) * p₁ - b = 0)
    (hfix2 : c * p₂ ^ (2 : ℕ) + (d - a) * p₂ - b = 0)
    (hden : algebraMap C E c * q + algebraMap C E d ≠ 0)
    (hq2 : q - algebraMap C E p₂ ≠ 0) :
    σ ((q - algebraMap C E p₁) / (q - algebraMap C E p₂))
      = algebraMap C E ((a - c * p₁) / (a - c * p₂))
        * ((q - algebraMap C E p₁) / (q - algebraMap C E p₂)) := by
  have hE1 := mobius_fixed_point_difference σ hσq hfix1
  have hE2 := mobius_fixed_point_difference σ hσq hfix2
  have hσ2 : σ (q - algebraMap C E p₂) ≠ 0 := by
    rw [map_ne_zero_iff σ σ.injective]; exact hq2
  -- the multiplier denominator is nonzero
  have hac2 : algebraMap C E (a - c * p₂) ≠ 0 := by
    have hne : σ (q - algebraMap C E p₂) * (algebraMap C E c * q + algebraMap C E d) ≠ 0 :=
      mul_ne_zero hσ2 hden
    rw [hE2] at hne
    exact left_ne_zero_of_mul hne
  have hac2' : (a - c * p₂ : C) ≠ 0 := fun h => hac2 (by rw [h, map_zero])
  -- solve for `σ (q - p_i)`
  have hs1 : σ (q - algebraMap C E p₁)
      = algebraMap C E (a - c * p₁) * (q - algebraMap C E p₁)
        / (algebraMap C E c * q + algebraMap C E d) :=
    (eq_div_iff hden).mpr hE1
  have hs2 : σ (q - algebraMap C E p₂)
      = algebraMap C E (a - c * p₂) * (q - algebraMap C E p₂)
        / (algebraMap C E c * q + algebraMap C E d) :=
    (eq_div_iff hden).mpr hE2
  rw [map_div₀, hs1, hs2, map_div₀]
  rw [div_div_div_cancel_right₀]
  · field_simp
  · exact hden

end GaloisForLFunctions.HTGeometry
