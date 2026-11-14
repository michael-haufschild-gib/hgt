import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationParity

/-!
# Valuation rigidity on congruent-number curves

For `y² = x³ - e²x`, a nonzero x-coordinate of odd valuation must have the
same valuation as the parameter `e`. Outside this equality locus, the two
terms in `x²-e²` have distinct valuations, so the curve equation forces
the valuation of `x` to be even.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

open HTGeometry.Arithmetic

variable {p : ℕ} [Fact p.Prime]

/-- Away from equal valuations of `x` and `e`, the curve equation forces
even valuation of its nonzero x-coordinate. -/
theorem congruent_x_even_of_val_ne {e x y : ℚ} (hx : x ≠ 0) (he : e ≠ 0)
    (hcurve : y ^ 2 = x ^ 3 - e ^ 2 * x)
    (hv : padicValRat p x ≠ padicValRat p e) : Even (padicValRat p x) := by
  have hv2 : padicValRat p (x ^ 2) ≠ padicValRat p (e ^ 2) := by
    simp only [padicValRat.pow, Nat.cast_ofNat]
    omega
  have hd := sub_ne_zero_of_val_ne hv2
  have hfactor : y ^ 2 = x * (x ^ 2 - e ^ 2) := by
    calc
      y ^ 2 = x ^ 3 - e ^ 2 * x := hcurve
      _ = x * (x ^ 2 - e ^ 2) := by ring
  have h := congrArg (padicValRat p) hfactor
  rw [padicValRat.pow, padicValRat.mul hx hd,
    val_sub_eq_min (pow_ne_zero 2 hx) (pow_ne_zero 2 he) hv2,
    padicValRat.pow, padicValRat.pow] at h
  simp only [Nat.cast_ofNat] at h
  rw [Int.even_iff]
  rcases le_total (padicValRat p x) (padicValRat p e) with hle | hle
  · rw [min_eq_left (by omega)] at h
    omega
  · rw [min_eq_right (by omega)] at h
    omega

/-- Odd valuation of an x-coordinate is confined to the parameter's own
valuation, a sharper statement than even-parameter parity alone. -/
theorem congruent_odd_x_val_eq_parameter {e x y : ℚ} (hx : x ≠ 0)
    (hcurve : y ^ 2 = x ^ 3 - e ^ 2 * x)
    (hodd : ¬ Even (padicValRat p x)) :
    padicValRat p x = padicValRat p e := by
  by_cases he : e = 0
  · have h := congrArg (padicValRat p) hcurve
    simp only [he, zero_pow (by omega : 2 ≠ 0), zero_mul, sub_zero,
      padicValRat.pow, Nat.cast_ofNat] at h
    rw [Int.even_iff] at hodd
    omega
  · by_contra hv
    exact hodd (congruent_x_even_of_val_ne hx he hcurve hv)

/-- Every rational point on an even-valuation parameter curve has even
x-valuation. Zero coordinates are included by the total valuation convention. -/
theorem congruent_x_even_of_parameter_even {e x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - e ^ 2 * x) (he : Even (padicValRat p e)) :
    Even (padicValRat p x) := by
  by_cases hx : x = 0
  · simp [hx]
  by_contra hodd
  exact hodd ((congruent_odd_x_val_eq_parameter hx hcurve hodd).symm ▸ he)

/-- Two congruent-number curves admitting x-coordinates in the same odd
valuation square class can differ only by an even-valuation twist. -/
theorem shared_odd_class_twist_even {b e H v w y z : ℚ}
    (he : e ≠ 0) (hH : H ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hodd : ¬ Even (padicValRat p b))
    (hfirst : y ^ 2 = (b * v ^ 2) ^ 3 - e ^ 2 * (b * v ^ 2))
    (hsecond : z ^ 2 = (b * w ^ 2) ^ 3 - (e * H) ^ 2 * (b * w ^ 2)) :
    Even (padicValRat p H) := by
  have hb : b ≠ 0 := by
    intro h
    exact hodd (by simp [h])
  have h₁ := congruent_odd_x_val_eq_parameter
    (mul_ne_zero hb (pow_ne_zero 2 hv)) hfirst (not_even_val_mul_sq hodd hv)
  have h₂ := congruent_odd_x_val_eq_parameter
    (mul_ne_zero hb (pow_ne_zero 2 hw)) hsecond (not_even_val_mul_sq hodd hw)
  rw [padicValRat.mul hb (pow_ne_zero 2 hv), padicValRat.pow] at h₁
  rw [padicValRat.mul hb (pow_ne_zero 2 hw), padicValRat.pow,
    padicValRat.mul he hH] at h₂
  simp only [Nat.cast_ofNat] at h₁ h₂
  exact ⟨padicValRat p w - padicValRat p v, by omega⟩

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
