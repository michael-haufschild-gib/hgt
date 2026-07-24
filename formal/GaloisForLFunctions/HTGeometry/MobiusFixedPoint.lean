import Mathlib.FieldTheory.IsAlgClosed.Basic
import GaloisForLFunctions.HTGeometry.MobiusDiagonalization

/-!
# Fixed points of a Möbius map over an algebraically closed field

The fixed points of the Möbius map `q ↦ (a q + b)/(c q + d)` are the roots of the quadratic
`c p² + (d − a) p − b`.  Over an algebraically closed field of characteristic zero a non-parabolic
map (`c ≠ 0`, nonzero discriminant) has two distinct fixed points, supplied here by the quadratic
formula.  Feeding these into `mobius_two_fixed_points_scaling` diagonalizes the map: in the
fixed-point coordinate it is a pure scaling.  This is the §3 `PGL₂`-cocharacter output — a clock
family with a common fixed-point pair acts by a character.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Two distinct fixed points.**  Over an algebraically closed field of characteristic zero, if
`c ≠ 0` and the discriminant `(d − a)² + 4 c b ≠ 0`, the Möbius fixed-point quadratic has two
distinct roots. -/
theorem mobius_two_distinct_fixed_points {C : Type*} [Field C] [IsAlgClosed C] [CharZero C]
    {a b c d : C} (hc : c ≠ 0) (hdisc : (d - a) ^ 2 + 4 * c * b ≠ 0) :
    ∃ p₁ p₂ : C, p₁ ≠ p₂ ∧ c * p₁ ^ 2 + (d - a) * p₁ - b = 0
      ∧ c * p₂ ^ 2 + (d - a) * p₂ - b = 0 := by
  obtain ⟨δ, hδ⟩ :=
    IsAlgClosed.exists_pow_nat_eq ((d - a) ^ 2 + 4 * c * b) (n := 2) (by norm_num)
  have hδ0 : δ ≠ 0 := fun h => hdisc (by rw [← hδ, h]; ring)
  have hc2 : (2 * c : C) ≠ 0 := mul_ne_zero two_ne_zero hc
  refine ⟨(-(d - a) + δ) / (2 * c), (-(d - a) - δ) / (2 * c), ?_, ?_, ?_⟩
  · -- distinct
    intro heq
    rw [div_eq_div_iff hc2 hc2] at heq
    have hnum : -(d - a) + δ = -(d - a) - δ := mul_right_cancel₀ hc2 heq
    have h2δ : (2 : C) * δ = 0 := by linear_combination hnum
    exact hδ0 ((mul_eq_zero.mp h2δ).resolve_left two_ne_zero)
  · -- first fixed point
    field_simp
    linear_combination hδ
  · -- second fixed point
    field_simp
    linear_combination hδ

/-- **Non-parabolic Möbius maps are scalings.**  Combining fixed-point existence with the
diagonalization payoff: over an algebraically closed field of characteristic zero, a `C`-algebra
automorphism `σ` acting on a generator `q` by a Möbius transform with `c ≠ 0`, nonzero discriminant,
and `q` outside `C` (`q − algebraMap p ≠ 0` for every `p`, so both denominators are nonzero) becomes
a pure scaling in the fixed-point coordinate `x = (q − p₁)/(q − p₂)`. -/
theorem mobius_nonparabolic_scaling {C E : Type*} [Field C] [IsAlgClosed C] [CharZero C]
    [Field E] [Algebra C E] (σ : E ≃ₐ[C] E) {a b c d : C} {q : E}
    (hσq : σ q * (algebraMap C E c * q + algebraMap C E d)
      = algebraMap C E a * q + algebraMap C E b)
    (hc : c ≠ 0) (hdisc : (d - a) ^ 2 + 4 * c * b ≠ 0)
    (hden : algebraMap C E c * q + algebraMap C E d ≠ 0)
    (hq_ne : ∀ p : C, q - algebraMap C E p ≠ 0) :
    ∃ p₁ p₂ : C, p₁ ≠ p₂ ∧
      σ ((q - algebraMap C E p₁) / (q - algebraMap C E p₂))
        = algebraMap C E ((a - c * p₁) / (a - c * p₂))
          * ((q - algebraMap C E p₁) / (q - algebraMap C E p₂)) := by
  obtain ⟨p₁, p₂, hne, hf1, hf2⟩ := mobius_two_distinct_fixed_points hc hdisc
  exact ⟨p₁, p₂, hne,
    mobius_two_fixed_points_scaling σ hσq hf1 hf2 hden (hq_ne p₂)⟩

end GaloisForLFunctions.HTGeometry
