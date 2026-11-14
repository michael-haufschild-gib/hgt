import GaloisForLFunctions.HTGeometry.Arithmetic.SquareDenominator
import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationProducts

/-!
# Denominators on split hyperelliptic curves

At a nonintegral x-coordinate, a monic split polynomial with integral roots
has valuation equal to its degree times the x-valuation. For odd degree,
the equation of a quadratic cover identifies the parity of the x-valuation
with that of the twisting parameter. Untwisted curves therefore have square
reduced x-denominators.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

open HTGeometry.Arithmetic Finset

variable {p : ℕ} [Fact p.Prime]

/-- Odd-degree quadratic covers transfer twist parity to every negative
x-valuation. The roots need only be integral at the prime in question. -/
theorem odd_split_curve_negative_parity {ι : Type*} (s : Finset ι) (a : ι → ℚ)
    (hn : Odd s.card) {d x y : ℚ} (hd : d ≠ 0)
    (ha : ∀ i ∈ s, 0 ≤ padicValRat p (a i)) (hx : padicValRat p x < 0)
    (hcurve : d * y ^ 2 = ∏ i ∈ s, (x - a i)) :
    Even (padicValRat p x) ↔ Even (padicValRat p d) := by
  have hprod : (∏ i ∈ s, (x - a i)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro i hi
    apply sub_ne_zero_of_val_ne (p := p)
    have h := ha i hi
    omega
  have hy : y ≠ 0 := by
    intro hy
    apply hprod
    rw [← hcurve, hy, zero_pow (by omega : 2 ≠ 0), mul_zero]
  have h := congrArg (padicValRat p) hcurve
  rw [padicValRat.mul hd (pow_ne_zero 2 hy), padicValRat.pow,
    val_split_product_of_neg s a hx ha] at h
  obtain ⟨k, hk⟩ := hn
  rw [hk] at h
  push_cast at h
  ring_nf at h
  rw [Int.even_iff, Int.even_iff]
  omega

/-- Every rational point on an odd-degree split curve with integral roots
has square reduced x-denominator. Repeated roots are allowed. -/
theorem squareDenominator_of_odd_split_curve {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (hn : Odd s.card) {x y : ℚ}
    (hcurve : y ^ 2 = ∏ i ∈ s, (x - (a i : ℚ))) : SquareDenominator x := by
  apply (squareDenominator_iff x).mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hx : 0 ≤ padicValRat p x
  · exact Or.inl hx
  · right
    apply (odd_split_curve_negative_parity s (fun i => (a i : ℚ)) hn
      (d := 1) one_ne_zero (fun i _ => by simp) (lt_of_not_ge hx)
      (by simpa only [one_mul] using hcurve)).mpr
    simp

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
