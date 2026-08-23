import GaloisForLFunctions.RHTower.MellinLineMass
import GaloisForLFunctions.RHTower.BurnolChiFactorIdentity

/-!
# The continued Mellin transform at the trivial zeros

The functional-equation factor `χ(s) = Γ(1−s)(2π)^{s−1}·2cos(π(s−1)/2)` vanishes at
`s = 0, −2, −4, …`, because `cos(π(s−1)/2) = sin(πs/2)`.  Left of the critical line the numerator
`s(1−s)M(f)(s)` is `(1−s)χ(s)(…)`, so it vanishes there too: the continued Mellin transform of a
vector of the extended Sonine space has a zero at every trivial zero of `ζ`, and its numerator
vanishes at `s = 0`, which is why `M(f)` is regular there.

This is exactly the input that makes the trivial zeros and `s = 0` *not* contribute residues to
Burnol's contour in Theorem 5.2.

## Main results

* `burnolChiFactor_neg_two_mul_nat`
* `extendedMellinNumerator_neg_two_mul_nat`, `extendedMellinContinuation_neg_two_mul_nat`
* `extendedMellinNumerator_zero`
-/

open Complex

namespace RHTower

noncomputable section

theorem extendedMellinNumerator_eq_zero_of_chi_zero (a : ℝ) (c d : ℂ) (f : SoninL2) {s : ℂ}
    (hs : s.re < 1 / 2) (hchi : burnolChiFactor s = 0) :
    extendedMellinNumerator a c d f s = 0 := by
  rw [extendedMellinNumerator_eq_left a c d f hs, extendedMellinNumeratorLeft, hchi]
  ring

/-- `χ` vanishes at every trivial zero and at the origin. -/
theorem burnolChiFactor_neg_two_mul_nat (k : ℕ) : burnolChiFactor (-(2 * (k : ℂ))) = 0 := by
  rw [burnolChiFactor, cos_pi_mul_sub_one_div_two]
  have hsin : Complex.sin ((Real.pi : ℂ) * ((-(2 * (k : ℂ))) / 2)) = 0 := by
    have harg : (Real.pi : ℂ) * ((-(2 * (k : ℂ))) / 2) = -((k : ℂ) * (Real.pi : ℂ)) := by
      ring
    rw [harg, Complex.sin_neg]
    have : Complex.sin ((k : ℂ) * (Real.pi : ℂ)) = 0 := by
      simpa using Complex.sin_nat_mul_pi k
    rw [this, neg_zero]
  rw [hsin]
  ring

theorem re_neg_two_mul_nat (k : ℕ) : (-(2 * (k : ℂ))).re = -(2 * (k : ℝ)) := by
  simp

/-- **The numerator vanishes at every trivial zero and at the origin.** -/
theorem extendedMellinNumerator_neg_two_mul_nat (a : ℝ) (c d : ℂ) (f : SoninL2) (k : ℕ) :
    extendedMellinNumerator a c d f (-(2 * (k : ℂ))) = 0 := by
  refine extendedMellinNumerator_eq_zero_of_chi_zero a c d f ?_ (burnolChiFactor_neg_two_mul_nat k)
  rw [re_neg_two_mul_nat]
  have : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
  linarith

theorem extendedMellinNumerator_zero (a : ℝ) (c d : ℂ) (f : SoninL2) :
    extendedMellinNumerator a c d f 0 = 0 := by
  have h := extendedMellinNumerator_neg_two_mul_nat a c d f 0
  simpa using h

/-- **The continued Mellin transform vanishes at every trivial zero of `ζ`.** -/
theorem extendedMellinContinuation_neg_two_mul_nat (a : ℝ) (c d : ℂ) (f : SoninL2) {k : ℕ}
    (hk : k ≠ 0) : extendedMellinContinuation a c d f (-(2 * (k : ℂ))) = 0 := by
  rw [extendedMellinContinuation, extendedMellinNumerator_neg_two_mul_nat a c d f k, zero_div]

end

end RHTower
