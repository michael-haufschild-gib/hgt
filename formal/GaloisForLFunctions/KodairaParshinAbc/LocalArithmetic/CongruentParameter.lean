import GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic.CongruentValuation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Fibres of the local parameter on congruent-number curves

On `y² = x³ - e²x`, the parameter `-x/y` has at most two points in each
nonzero-coordinate fibre. The second point is `T-Q`, with `T=(0,0)`,
and has coordinates `(-e²/x, -e²y/x²)`. Over the rationals the two
x-coordinates have opposite signs, so the positive-x branch is injective.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

section Field

variable {F : Type*} [Field F]

/-- The usual parameter at the point at infinity. -/
def congruentParameter (x y : F) : F := -x / y

/-- Fixing the parameter confines the x-coordinate to a quadratic. -/
theorem congruentParameter_quadratic {e x y : F} (hy : y ≠ 0)
    (hcurve : y ^ 2 = x ^ 3 - e ^ 2 * x) :
    congruentParameter x y ^ 2 * x ^ 2 - x - e ^ 2 * congruentParameter x y ^ 2 = 0 := by
  unfold congruentParameter
  field_simp
  linear_combination -x * hcurve

/-- The exact two-point fibre of the parameter. No rank, torsion, or
arithmetic assumptions enter this coordinate identity. -/
theorem congruentParameter_fiber_iff {e x₁ y₁ x₂ y₂ : F}
    (hx₁ : x₁ ≠ 0) (hy₁ : y₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hy₂ : y₂ ≠ 0)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - e ^ 2 * x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - e ^ 2 * x₂) :
    congruentParameter x₁ y₁ = congruentParameter x₂ y₂ ↔
      (x₂ = x₁ ∧ y₂ = y₁) ∨
        (x₂ = -e ^ 2 / x₁ ∧ y₂ = -e ^ 2 * y₁ / x₁ ^ 2) := by
  rw [congruentParameter, congruentParameter, div_eq_div_iff hy₁ hy₂]
  constructor
  · intro hz
    have hcross : x₁ * y₂ = x₂ * y₁ := by
      simpa only [neg_mul, neg_inj] using hz
    have hsq : x₁ ^ 2 * y₂ ^ 2 = x₂ ^ 2 * y₁ ^ 2 := by
      linear_combination (x₁ * y₂ + x₂ * y₁) * hcross
    have hfactor : x₁ * x₂ * ((x₂ - x₁) * (x₁ * x₂ + e ^ 2)) = 0 := by
      linear_combination -x₁ ^ 2 * h₂ + x₂ ^ 2 * h₁ + hsq
    have hsplit := mul_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero hx₁ hx₂))
    rcases hsplit with hsame | hother
    · have hx : x₂ = x₁ := sub_eq_zero.mp hsame
      refine Or.inl ⟨hx, ?_⟩
      rw [hx] at hcross
      exact mul_left_cancel₀ hx₁ hcross
    · have hx : x₂ = -e ^ 2 / x₁ := by
        apply (eq_div_iff hx₁).mpr
        linear_combination hother
      refine Or.inr ⟨hx, ?_⟩
      apply (eq_div_iff (pow_ne_zero 2 hx₁)).mpr
      have hxprod : x₁ * x₂ = -e ^ 2 := eq_neg_of_add_eq_zero_left hother
      calc
        y₂ * x₁ ^ 2 = (x₁ * y₂) * x₁ := by ring
        _ = (x₂ * y₁) * x₁ := by rw [hcross]
        _ = (x₁ * x₂) * y₁ := by ring
        _ = -e ^ 2 * y₁ := by rw [hxprod]
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · rw [hx, hy]
    · rw [hx, hy]
      field_simp

/-- The partner point lies on the same cubic. -/
theorem congruentParameter_partner_on_curve {e x y : F} (hx : x ≠ 0)
    (hcurve : y ^ 2 = x ^ 3 - e ^ 2 * x) :
    (-e ^ 2 * y / x ^ 2) ^ 2 = (-e ^ 2 / x) ^ 3 - e ^ 2 * (-e ^ 2 / x) := by
  field_simp
  linear_combination e ^ 4 * hcurve

end Field

/-- The parameter is injective on the positive-x rational branch. The
other point in a fibre has nonpositive x-coordinate. -/
theorem congruentParameter_injective_positive {e x₁ y₁ x₂ y₂ : ℚ}
    (hx₁ : 0 < x₁) (hy₁ : y₁ ≠ 0) (hx₂ : 0 < x₂) (hy₂ : y₂ ≠ 0)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - e ^ 2 * x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - e ^ 2 * x₂)
    (hz : congruentParameter x₁ y₁ = congruentParameter x₂ y₂) :
    x₂ = x₁ ∧ y₂ = y₁ := by
  rcases (congruentParameter_fiber_iff hx₁.ne' hy₁ hx₂.ne' hy₂ h₁ h₂).mp hz with h | h
  · exact h
  · have hnonpos : -e ^ 2 / x₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg e)) hx₁.le
    rw [← h.1] at hnonpos
    exact (not_le_of_gt hx₂ hnonpos).elim

/-- A pole of x on an integral-parameter model gives the exact local
parameter valuation. This coordinate law includes the prime two. -/
theorem congruentParameter_val_of_neg {p : ℕ} [Fact p.Prime] {e x y : ℚ}
    (he : 0 ≤ padicValRat p e) (hx : padicValRat p x < 0)
    (hcurve : y ^ 2 = x ^ 3 - e ^ 2 * x) :
    y ≠ 0 ∧ 2 * padicValRat p (congruentParameter x y) = -padicValRat p x ∧
      0 < padicValRat p (congruentParameter x y) := by
  have hxne : x ≠ 0 := by
    intro h
    simp only [h, padicValRat.zero, lt_self_iff_false] at hx
  have hval : 2 * padicValRat p y = 3 * padicValRat p x := by
    by_cases he0 : e = 0
    · have hv := congrArg (padicValRat p) hcurve
      simpa only [he0, zero_pow (by omega : 2 ≠ 0), zero_mul, sub_zero,
        padicValRat.pow, Nat.cast_ofNat] using hv
    · have hvals : padicValRat p (x ^ 3) ≠ padicValRat p (e ^ 2 * x) := by
        rw [padicValRat.pow, padicValRat.mul (pow_ne_zero 2 he0) hxne, padicValRat.pow]
        simp only [Nat.cast_ofNat]
        omega
      have hv := congrArg (padicValRat p) hcurve
      rw [padicValRat.pow, HTGeometry.Arithmetic.val_sub_eq_min (pow_ne_zero 3 hxne)
        (mul_ne_zero (pow_ne_zero 2 he0) hxne) hvals, padicValRat.pow,
        padicValRat.mul (pow_ne_zero 2 he0) hxne, padicValRat.pow] at hv
      simp only [Nat.cast_ofNat] at hv
      rwa [min_eq_left (by omega)] at hv
  have hy : y ≠ 0 := by
    intro h
    rw [h, padicValRat.zero] at hval
    omega
  refine ⟨hy, ?_⟩
  rw [congruentParameter, padicValRat.div (neg_ne_zero.mpr hxne) hy, padicValRat.neg]
  omega

#print axioms congruentParameter_fiber_iff
#print axioms congruentParameter_partner_on_curve
#print axioms congruentParameter_injective_positive
#print axioms congruentParameter_val_of_neg

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
