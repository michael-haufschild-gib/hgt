import GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic.CongruentValuation
import GaloisForLFunctions.HTGeometry.Arithmetic.SquareDenominator

/-!
# Soundness of the two-twist square-denominator witness

The witness consists of actual rational points on two congruent-number
curves. Its soundness uses only valuation parity; no assertion about ranks
or existence of points enters the proof. At every prime where the two
multipliers are units, the witnessed rational has no negative odd valuation.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

open HTGeometry.Arithmetic

/-- Möbius parameter used to couple the two curves. -/
def twistSlope (μ δ b t : ℚ) : ℚ :=
  (1 - δ * b * t ^ 2) / (μ * (1 + δ * b * t ^ 2))

/-- Norm of `1 + U√(μb)`, giving the second twisting parameter. -/
def twistNorm (μ δ b t : ℚ) : ℚ := 1 - (μ * b) * twistSlope μ δ b t ^ 2

/-- An existential condition expressed entirely by rational curve equations
and nonvanishing conditions. -/
def TwoTwistWitness (μ δ b : ℚ) : Prop :=
  b = 0 ∨ ∃ t e v w y z : ℚ,
    1 + δ * b * t ^ 2 ≠ 0 ∧ e * twistNorm μ δ b t ≠ 0 ∧
    v ≠ 0 ∧ w ≠ 0 ∧
    y ^ 2 = ((μ * b) * v ^ 2) ^ 3 - e ^ 2 * ((μ * b) * v ^ 2) ∧
    z ^ 2 = ((μ * b) * w ^ 2) ^ 3 -
      (e * twistNorm μ δ b t) ^ 2 * ((μ * b) * w ^ 2)

variable {p : ℕ} [Fact p.Prime]

private theorem twistSlope_unit {μ δ b : ℚ} (hμ : μ ≠ 0) (hδ : δ ≠ 0)
    (hvμ : padicValRat p μ = 0) (hvδ : padicValRat p δ = 0)
    (hodd : ¬ Even (padicValRat p b)) (t : ℚ) :
    twistSlope μ δ b t ≠ 0 ∧ padicValRat p (twistSlope μ δ b t) = 0 := by
  by_cases ht : t = 0
  · simp [twistSlope, ht, hμ, padicValRat.inv, hvμ]
  have hb : b ≠ 0 := by
    intro h
    exact hodd (by simp [h])
  have hδb : padicValRat p (δ * b) = padicValRat p b := by
    rw [padicValRat.mul hδ hb, hvδ, zero_add]
  have hsodd : ¬ Even (padicValRat p (δ * b * t ^ 2)) := by
    apply not_even_val_mul_sq _ ht
    rwa [hδb]
  have hs : padicValRat p (δ * b * t ^ 2) ≠ 0 := by
    intro h
    exact hsodd (h ▸ Even.zero)
  have hval : padicValRat p 1 ≠ padicValRat p (δ * b * t ^ 2) := by
    simpa only [padicValRat.one] using hs.symm
  have hsub := sub_ne_zero_of_val_ne hval
  have hadd := add_ne_zero_of_val_ne hval
  have hs0 := mul_ne_zero (mul_ne_zero hδ hb) (pow_ne_zero 2 ht)
  refine ⟨div_ne_zero hsub (mul_ne_zero hμ hadd), ?_⟩
  rw [twistSlope, padicValRat.div hsub (mul_ne_zero hμ hadd),
    padicValRat.mul hμ hadd, hvμ, zero_add,
    val_sub_eq_min one_ne_zero hs0 hval,
    padicValRat.add_eq_min hadd one_ne_zero hs0 hval, sub_self]

/-- Every actual two-twist witness excludes a negative odd valuation at
each prime where its multipliers are units, including the prime two. -/
theorem twoTwistWitness_local_sound {μ δ b : ℚ} (hμ : μ ≠ 0) (hδ : δ ≠ 0)
    (hvμ : padicValRat p μ = 0) (hvδ : padicValRat p δ = 0)
    (hwitness : TwoTwistWitness μ δ b) :
    0 ≤ padicValRat p b ∨ Even (padicValRat p b) := by
  rcases hwitness with rfl | ⟨t, e, v, w, y, z, _, heH, hv, hw, hfirst, hsecond⟩
  · simp
  by_contra h
  push Not at h
  obtain ⟨hneg, hodd⟩ := h
  have hb : b ≠ 0 := by
    intro h
    exact hodd (by simp [h])
  obtain ⟨hU, hvU⟩ := twistSlope_unit hμ hδ hvμ hvδ hodd t
  have hb' : μ * b ≠ 0 := mul_ne_zero hμ hb
  have hvb : padicValRat p (μ * b) = padicValRat p b := by
    rw [padicValRat.mul hμ hb, hvμ, zero_add]
  have hvterm : padicValRat p ((μ * b) * twistSlope μ δ b t ^ 2) =
      padicValRat p b := by
    rw [padicValRat.mul hb' (pow_ne_zero 2 hU), padicValRat.pow, hvU, hvb,
      mul_zero, add_zero]
  have hvdiff : padicValRat p 1 ≠
      padicValRat p ((μ * b) * twistSlope μ δ b t ^ 2) := by
    rw [padicValRat.one, hvterm]
    omega
  have hvH : padicValRat p (twistNorm μ δ b t) = padicValRat p b := by
    rw [twistNorm, val_sub_eq_min one_ne_zero
      (mul_ne_zero hb' (pow_ne_zero 2 hU)) hvdiff, padicValRat.one, hvterm,
      min_eq_right hneg.le]
  have heven := shared_odd_class_twist_even (mul_ne_zero_iff.mp heH).1
    (mul_ne_zero_iff.mp heH).2 hv hw (hvb ▸ hodd) hfirst hsecond
  exact hodd (hvH ▸ heven)

/-- With unit multipliers equal to one, the existential curve predicate
is contained in the square-denominator set with no exceptional primes. -/
theorem twoTwistWitness_one_sound (b : ℚ) :
    TwoTwistWitness 1 1 b → SquareDenominator b := by
  intro h
  apply (squareDenominator_iff b).mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact twoTwistWitness_local_sound one_ne_zero one_ne_zero
    padicValRat.one padicValRat.one h

#print axioms twoTwistWitness_local_sound
#print axioms twoTwistWitness_one_sound

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
