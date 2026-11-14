import GaloisForLFunctions.HTGeometry.Arithmetic.IntegralTests
import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationParity
import Mathlib.Tactic.Linarith

/-!
# Exact denominators on `y²+y=xᵐ`

For positive degree, the two coordinates are integral at exactly the same
primes. At their poles the equation reads `2v(y)=mv(x)`. Thus the reduced
denominators satisfy `den(y)²=den(x)ᵐ`. Odd degree forces `den(x)` to be a
square, and the two denominators are powers of a common integer.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

open HTGeometry.Arithmetic

variable {p : ℕ} [Fact p.Prime]

private theorem val_sq_add_self_of_neg {y : ℚ} (hy : padicValRat p y < 0) :
    padicValRat p (y ^ 2 + y) = 2 * padicValRat p y := by
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have hne : padicValRat p (y ^ 2) ≠ padicValRat p y := by
    rw [padicValRat.pow]
    norm_cast
    omega
  rw [padicValRat.add_eq_min (add_ne_zero_of_val_ne hne)
    (pow_ne_zero 2 hy0) hy0 hne, padicValRat.pow, min_eq_left (by omega)]
  rfl

/-- Integrality of the x-coordinate forces integrality of the y-coordinate. -/
theorem power_curve_y_integral {m : ℕ} {x y : ℚ}
    (hcurve : y ^ 2 + y = x ^ m) (hx : 0 ≤ padicValRat p x) :
    0 ≤ padicValRat p y := by
  by_contra hy
  have hv := congrArg (padicValRat p) hcurve
  rw [val_sq_add_self_of_neg (lt_of_not_ge hy), padicValRat.pow] at hv
  have hm : 0 ≤ (m : ℤ) := Nat.cast_nonneg _
  have hprod := mul_nonneg hm hx
  omega

/-- Positive degree makes integrality of the two coordinates equivalent. -/
theorem power_curve_integral_iff {m : ℕ} (hm : 0 < m) {x y : ℚ}
    (hcurve : y ^ 2 + y = x ^ m) :
    0 ≤ padicValRat p x ↔ 0 ≤ padicValRat p y := by
  constructor
  · exact power_curve_y_integral hcurve
  · intro hy
    by_cases hx0 : x = 0
    · simp [hx0]
    have hs : y ^ 2 + y ≠ 0 := by rw [hcurve]; exact pow_ne_zero m hx0
    have hv := padicValRat.min_le_padicValRat_add (p := p) hs
    rw [hcurve, padicValRat.pow, padicValRat.pow] at hv
    have hmin : 0 ≤ min ((2 : ℤ) * padicValRat p y) (padicValRat p y) := by omega
    have hprod := hmin.trans hv
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    by_contra hx
    have := mul_neg_of_pos_of_neg hm' (lt_of_not_ge hx)
    omega

/-- Pole orders satisfy the weighted homogeneous relation exactly. -/
theorem power_curve_pole_orders {m : ℕ} (hm : 0 < m) {x y : ℚ}
    (hcurve : y ^ 2 + y = x ^ m) (hx : padicValRat p x < 0) :
    padicValRat p y < 0 ∧ 2 * padicValRat p y = (m : ℤ) * padicValRat p x := by
  have hy : padicValRat p y < 0 := by
    by_contra hy
    have := (power_curve_integral_iff hm hcurve).mpr (le_of_not_gt hy)
    omega
  refine ⟨hy, ?_⟩
  have h := congrArg (padicValRat p) hcurve
  rwa [val_sq_add_self_of_neg hy, padicValRat.pow] at h

/-- Exact global denominator identity for every positive degree. -/
theorem power_curve_denominator_identity {m : ℕ} (hm : 0 < m) {x y : ℚ}
    (hcurve : y ^ 2 + y = x ^ m) : y.den ^ 2 = x.den ^ m := by
  apply (Nat.eq_iff_prime_padicValNat_eq _ _ (pow_ne_zero _ y.den_nz)
    (pow_ne_zero _ x.den_nz)).mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.pow, padicValNat.pow]
  have hxden := den_valuation_eq_negative_part p x
  have hyden := den_valuation_eq_negative_part p y
  by_cases hx : 0 ≤ padicValRat p x
  · have hy := power_curve_y_integral hcurve hx
    rw [max_eq_right (by omega)] at hxden hyden
    have hx0 : padicValNat p x.den = 0 := by omega
    have hy0 : padicValNat p y.den = 0 := by omega
    simp [hx0, hy0]
  · obtain ⟨hy, horders⟩ := power_curve_pole_orders hm hcurve (lt_of_not_ge hx)
    rw [max_eq_left (by omega)] at hxden hyden
    have hZ : (2 : ℤ) * (padicValNat p y.den : ℤ) =
        (m : ℤ) * (padicValNat p x.den : ℤ) := by
      rw [hxden, hyden]
      nlinarith only [horders]
    exact_mod_cast hZ

/-- Odd degree forces a square reduced x-denominator. -/
theorem power_curve_squareDenominator {m : ℕ} (hm : Odd m) {x y : ℚ}
    (hcurve : y ^ 2 + y = x ^ m) : SquareDenominator x := by
  obtain ⟨k, hk⟩ := hm
  have hmpos : 0 < m := by omega
  apply (squareDenominator_iff x).mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hx : 0 ≤ padicValRat p x
  · exact Or.inl hx
  · right
    have horders := (power_curve_pole_orders hmpos hcurve (lt_of_not_ge hx)).2
    rw [hk] at horders
    push_cast at horders
    ring_nf at horders
    rw [Int.even_iff]
    omega

/-- Both denominators are powers of one integer on an odd-degree curve. -/
theorem power_curve_common_denominator {m : ℕ} (hm : Odd m) {x y : ℚ}
    (hcurve : y ^ 2 + y = x ^ m) :
    ∃ d : ℕ, x.den = d ^ 2 ∧ y.den = d ^ m := by
  obtain ⟨d, hd⟩ := power_curve_squareDenominator hm hcurve
  have hxden : x.den = d ^ 2 := by simpa only [sq] using hd
  refine ⟨d, hxden, ?_⟩
  have hmpos : 0 < m := by obtain ⟨k, hk⟩ := hm; omega
  have h := power_curve_denominator_identity hmpos hcurve
  rw [hxden, ← pow_mul, mul_comm 2 m, pow_mul] at h
  exact Nat.mul_self_inj.mp (by simpa only [sq] using h)

/-- The genus-two equation `y²+y=x⁵` has denominators `d²` and `d⁵`. -/
theorem quintic_common_denominator {x y : ℚ} (hcurve : y ^ 2 + y = x ^ 5) :
    ∃ d : ℕ, x.den = d ^ 2 ∧ y.den = d ^ 5 :=
  power_curve_common_denominator ⟨2, rfl⟩ hcurve

#print axioms power_curve_denominator_identity
#print axioms quintic_common_denominator

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
