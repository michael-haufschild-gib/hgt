import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# The zero-side pairing of two power tails

The Mellin factors of `t⁻ᵃ` give `1/((ρ-a)(1-ρ-a))` at a reflected
pair of zero arguments. The symmetrized partial fraction of `ξ'/ξ`
identifies their sum and proves absolute summability. Nonvanishing of ξ
on the real axis supplies every denominator without assuming RH.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower (XiZeroCopy xi)

/-- The reflected zero pairing of the Mellin transform of `t⁻ᵃ`. -/
def powerTailZeroPairing (a : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, 1 / (((q.1 : ℂ) - a) * (1 - (q.1 : ℂ) - a))

private theorem powerTail_pair_fraction {a : ℝ}
    (ha2 : a < 1 / 2) (q : XiZeroCopy) :
    1 / (((q.1 : ℂ) - a) * (1 - (q.1 : ℂ) - a)) =
      (1 - 2 * (a : ℂ))⁻¹ *
        (((1 - (a : ℂ)) - (q.1 : ℂ))⁻¹ + ((1 - (a : ℂ)) - 1 + (q.1 : ℂ))⁻¹) := by
  have hqreal (r : ℝ) : (q.1 : ℂ) ≠ (r : ℂ) := by
    intro h
    apply _root_.RHTower.xi_ne_zero_of_real r
    rw [← h]
    exact _root_.RHTower.xi_eq_zero_of_mem_divisor_support q.1
  have hleft : (q.1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (hqreal a)
  have hright : 1 - (q.1 : ℂ) - a ≠ 0 := by
    intro h
    apply hqreal (1 - a)
    push_cast
    linear_combination -h
  have hden : 1 - 2 * (a : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) - 2 * a ≠ 0 by linarith only [ha2])
  rw [show (1 - (a : ℂ)) - (q.1 : ℂ) = 1 - (q.1 : ℂ) - a by ring,
    show (1 - (a : ℂ)) - 1 + (q.1 : ℂ) = (q.1 : ℂ) - a by ring]
  apply (mul_left_cancel₀ hden)
  rw [← mul_assoc, mul_inv_cancel₀ hden, one_mul]
  field_simp [hleft, hright]
  ring

private theorem xi_ne_zero_at_powerTail (a : ℝ) : xi (1 - (a : ℂ)) ≠ 0 := by
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
    _root_.RHTower.xi_ne_zero_of_real (1 - a)

/-- The zero pairing of a subcritical power is absolutely summable,
independently of RH. -/
theorem summable_powerTailZeroPairing {a : ℝ} (ha2 : a < 1 / 2) :
    Summable (fun q : XiZeroCopy => 1 / (((q.1 : ℂ) - a) * (1 - (q.1 : ℂ) - a))) := by
  have h := (_root_.RHTower.summable_xiPairTerm
    (xi_ne_zero_at_powerTail a)).mul_left ((1 - 2 * (a : ℂ))⁻¹)
  exact h.congr fun q => (powerTail_pair_fraction ha2 q).symm

/-- The zero-side Mellin pairing is the logarithmic derivative at the reflected
power parameter. -/
theorem powerTailZeroPairing_eq_logDeriv {a : ℝ} (ha2 : a < 1 / 2) :
    powerTailZeroPairing a = (2 / (1 - 2 * (a : ℂ))) * logDeriv xi (1 - (a : ℂ)) := by
  rw [powerTailZeroPairing, tsum_congr (powerTail_pair_fraction ha2), tsum_mul_left,
    ← _root_.RHTower.two_logDeriv_xi_eq_pair_tsum (xi_ne_zero_at_powerTail a)]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
