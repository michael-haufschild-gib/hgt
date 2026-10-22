/-
# Off-line quartet resolvent polarization

This file formalizes the scalar algebra by which a functional-equation quartet
splits into causal and anti-causal resolvent packets.  Their cross packet is
exactly one positive square minus one negative square.  The negative coordinate
is proportional to `λ + conj λ`, so it is precisely transverse displacement
from the critical line in the centered coordinate.

The result is independent of any conjecture about zeta zeros.  It supplies the
local indefinite block that a global CCM carrier must detect.
-/
import Mathlib

open Complex

namespace RHTower

noncomputable section

/-- The centered functional-equation pair resolvent. -/
def ccmQuartetPairResolvent (lam z : ℂ) : ℂ :=
  (z - lam)⁻¹ + (z + lam)⁻¹

/-- The causal half of the bilateral quartet coordinate. -/
def ccmCausalResolvent (lam : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) - lam)⁻¹

/-- The anti-causal reflected half of the bilateral quartet coordinate. -/
def ccmAntiCausalResolvent (lam : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) + star lam)⁻¹

/-- Hermitian cross packet joining the causal and reflected anti-causal halves. -/
def ccmQuartetCrossPacket (lam : ℂ) (x y : ℝ) : ℂ :=
  ccmCausalResolvent lam x * star (ccmAntiCausalResolvent lam y) +
    ccmAntiCausalResolvent lam x * star (ccmCausalResolvent lam y)

/-- Positive light-cone square of the bilateral packet. -/
def ccmQuartetPositiveSquare (lam : ℂ) (x y : ℝ) : ℂ :=
  (ccmCausalResolvent lam x + ccmAntiCausalResolvent lam x) *
      star (ccmCausalResolvent lam y + ccmAntiCausalResolvent lam y) / 2

/-- Negative light-cone square of the bilateral packet. -/
def ccmQuartetNegativeSquare (lam : ℂ) (x y : ℝ) : ℂ :=
  (ccmCausalResolvent lam x - ccmAntiCausalResolvent lam x) *
      star (ccmCausalResolvent lam y - ccmAntiCausalResolvent lam y) / 2

/-- Exact bilateral polarization: one cross packet is one positive square minus
one negative square. -/
theorem ccmQuartetCrossPacket_eq_positive_sub_negative
    (lam : ℂ) (x y : ℝ) :
    ccmQuartetCrossPacket lam x y =
      ccmQuartetPositiveSquare lam x y - ccmQuartetNegativeSquare lam x y := by
  simp [ccmQuartetCrossPacket, ccmQuartetPositiveSquare, ccmQuartetNegativeSquare]
  ring

/-- A pair-resolvent Cauchy quotient is the sum of its two opposite-pole kernels. -/
theorem ccmQuartetPairResolvent_kernel_split
    (lam : ℂ) (x y : ℝ)
    (hxy : (x : ℂ) + y ≠ 0)
    (hxm : (x : ℂ) - lam ≠ 0) (hxp : (x : ℂ) + lam ≠ 0)
    (hym : (y : ℂ) - lam ≠ 0) (hyp : (y : ℂ) + lam ≠ 0) :
    (ccmQuartetPairResolvent lam x + ccmQuartetPairResolvent lam y) /
        ((x : ℂ) + y) =
      ((x : ℂ) - lam)⁻¹ * ((y : ℂ) + lam)⁻¹ +
        ((x : ℂ) + lam)⁻¹ * ((y : ℂ) - lam)⁻¹ := by
  rw [ccmQuartetPairResolvent, ccmQuartetPairResolvent]
  field_simp
  ring

/-- The full Schwarz/functional-equation quartet quotient is exactly the sum of
the `λ` and `conj λ` bilateral cross packets. -/
theorem ccmQuartetResolvent_eq_crossPackets
    (lam : ℂ) (x y : ℝ)
    (hxy : (x : ℂ) + y ≠ 0)
    (hxm : (x : ℂ) - lam ≠ 0) (hxp : (x : ℂ) + lam ≠ 0)
    (hym : (y : ℂ) - lam ≠ 0) (hyp : (y : ℂ) + lam ≠ 0)
    (hxmc : (x : ℂ) - star lam ≠ 0) (hxpc : (x : ℂ) + star lam ≠ 0)
    (hymc : (y : ℂ) - star lam ≠ 0) (hypc : (y : ℂ) + star lam ≠ 0) :
    (ccmQuartetPairResolvent lam x + ccmQuartetPairResolvent lam y +
          ccmQuartetPairResolvent (star lam) x +
          ccmQuartetPairResolvent (star lam) y) /
        ((x : ℂ) + y) =
      ccmQuartetCrossPacket lam x y + ccmQuartetCrossPacket (star lam) x y := by
  have hsplit :
      (ccmQuartetPairResolvent lam x + ccmQuartetPairResolvent lam y +
            ccmQuartetPairResolvent (star lam) x +
            ccmQuartetPairResolvent (star lam) y) /
          ((x : ℂ) + y) =
        (ccmQuartetPairResolvent lam x + ccmQuartetPairResolvent lam y) /
            ((x : ℂ) + y) +
          (ccmQuartetPairResolvent (star lam) x +
              ccmQuartetPairResolvent (star lam) y) /
            ((x : ℂ) + y) := by
    ring
  rw [hsplit,
    ccmQuartetPairResolvent_kernel_split lam x y hxy hxm hxp hym hyp,
    ccmQuartetPairResolvent_kernel_split (star lam) x y hxy hxmc hxpc hymc hypc]
  simp [ccmQuartetCrossPacket, ccmCausalResolvent, ccmAntiCausalResolvent]
  ring

/-- The negative polarization coordinate is the transverse charge
`λ + conj λ = 2 Re λ` divided by the two bilateral resolvent denominators. -/
theorem ccmCausal_sub_antiCausal
    (lam : ℂ) (x : ℝ)
    (hxm : (x : ℂ) - lam ≠ 0) (hxp : (x : ℂ) + star lam ≠ 0) :
    ccmCausalResolvent lam x - ccmAntiCausalResolvent lam x =
      (lam + star lam) /
        (((x : ℂ) - lam) * ((x : ℂ) + star lam)) := by
  rw [ccmCausalResolvent, ccmAntiCausalResolvent]
  field_simp
  ring

/-- A genuinely transverse quartet has a nonzero negative coordinate at every
real sampling point away from its poles. -/
theorem ccmCausal_sub_antiCausal_ne_zero
    (lam : ℂ) (x : ℝ)
    (htransverse : lam + star lam ≠ 0)
    (hxm : (x : ℂ) - lam ≠ 0) (hxp : (x : ℂ) + star lam ≠ 0) :
    ccmCausalResolvent lam x - ccmAntiCausalResolvent lam x ≠ 0 := by
  rw [ccmCausal_sub_antiCausal lam x hxm hxp]
  exact div_ne_zero htransverse (mul_ne_zero hxm hxp)

end

end RHTower
