import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorSymbolSplitsAtTheZeros

/-!
# The zero-side pairing of two power tails

The Mellin factors of `t⁻ᵃ` give `1/((ρ-a)(1-ρ-a))` at a reflected
pair of zero arguments. The symmetrized partial fraction of `ξ'/ξ`
identifies their sum and proves absolute summability under RH.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower (XiZeroCopy xi)

/-- The reflected zero pairing of the Mellin transform of `t⁻ᵃ`. -/
def powerTailZeroPairing (a : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, 1 / (((q.1 : ℂ) - a) * (1 - (q.1 : ℂ) - a))

private theorem powerTail_pair_fraction (hRH : RiemannHypothesis) {a : ℝ}
    (ha2 : a < 1 / 2) (q : XiZeroCopy) :
    1 / (((q.1 : ℂ) - a) * (1 - (q.1 : ℂ) - a)) =
      (1 - 2 * (a : ℂ))⁻¹ *
        (((1 - (a : ℂ)) - (q.1 : ℂ))⁻¹ + ((1 - (a : ℂ)) - 1 + (q.1 : ℂ))⁻¹) := by
  have hre := _root_.RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have hleft : (q.1 : ℂ) - a ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re, hre] at hh
    linarith only [ha2, hh]
  have hright : 1 - (q.1 : ℂ) - a ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re, hre] at hh
    linarith only [ha2, hh]
  have hden : 1 - 2 * (a : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) - 2 * a ≠ 0 by linarith only [ha2])
  rw [show (1 - (a : ℂ)) - (q.1 : ℂ) = 1 - (q.1 : ℂ) - a by ring,
    show (1 - (a : ℂ)) - 1 + (q.1 : ℂ) = (q.1 : ℂ) - a by ring]
  field_simp
  ring

private theorem xi_ne_zero_at_powerTail (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) : xi (1 - (a : ℂ)) ≠ 0 := by
  apply ArithmeticCorrespondencePositivity.xi_ne_zero_of_riemannHypothesis hRH
  · simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [ha2]
  · intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hh
    linarith only [ha, hh]

/-- The zero pairing of a subcritical power is absolutely summable under RH. -/
theorem summable_powerTailZeroPairing (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) :
    Summable (fun q : XiZeroCopy => 1 / (((q.1 : ℂ) - a) * (1 - (q.1 : ℂ) - a))) := by
  have h := (_root_.RHTower.summable_xiPairTerm (xi_ne_zero_at_powerTail hRH ha ha2))
    .mul_left ((1 - 2 * (a : ℂ))⁻¹)
  exact h.congr fun q => (powerTail_pair_fraction hRH ha2 q).symm

/-- The zero-side Mellin pairing is the logarithmic derivative at the reflected
power parameter. -/
theorem powerTailZeroPairing_eq_logDeriv (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) :
    powerTailZeroPairing a = (2 / (1 - 2 * (a : ℂ))) * logDeriv xi (1 - (a : ℂ)) := by
  rw [powerTailZeroPairing, tsum_congr (powerTail_pair_fraction hRH ha2), tsum_mul_left,
    ← _root_.RHTower.two_logDeriv_xi_eq_pair_tsum (xi_ne_zero_at_powerTail hRH ha ha2)]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
