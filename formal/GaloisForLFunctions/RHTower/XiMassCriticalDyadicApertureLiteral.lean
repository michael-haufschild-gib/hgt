import GaloisForLFunctions.RHTower.XiMassCriticalBesselCarrierBridge
import GaloisForLFunctions.RHTower.MassBesselDyadicAperture
import GaloisForLFunctions.RHTower.XiMassLevinsonPrimeSecantLanding

/-!
# Literal dyadic subpackets of the critical Xi-mass cone

The deep-time Bessel aperture is not an auxiliary model.  Above the first logarithmic cell it is
identically the corresponding finite dyadic subpacket of the literal damped prime current.  The
conversion uses the existing exact half-density identity
`exp (-log n / 2) = 1 / sqrt n`.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- The literal damped prime current restricted to one dyadic arithmetic packet. -/
def xiMassCriticalDyadicPrimePacket (a sigma X u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log n)

/-- Above the first cell, the literal dyadic prime packet is the Bessel aperture exactly. -/
theorem xiMassCriticalDyadicPrimePacket_eq_massBesselDyadicAperture
    {a sigma X u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (hX : 1 ≤ ⌊X⌋₊) :
    xiMassCriticalDyadicPrimePacket a sigma X u = massBesselDyadicAperture a sigma X u := by
  rw [xiMassCriticalDyadicPrimePacket, massBesselDyadicAperture]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnmem := Finset.mem_Ioc.mp hn
  have hnone : 1 < n := lt_of_le_of_lt hX hnmem.1
  have hnpos : 0 < n := lt_trans Nat.zero_lt_one hnone
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hnone)
  rw [xiMassCriticalDampedFourierProfile_eq_massBesselCarrier ha hsigma hlog,
    exp_neg_log_nat_div_two_eq_inv_sqrt hnpos, HTGeometry.apertureSpectralPoint]
  push_cast
  ring

/-- Literal dyadic prime packets are unbounded along the deep-time ray. -/
theorem tendsto_norm_xiMassCriticalDyadicPrimePacket_atTop (a sigma : ℝ)
    (ha : 0 < a) (hsigma : 0 < sigma) :
    Tendsto (fun X : ℝ => ‖xiMassCriticalDyadicPrimePacket a sigma X (Real.log X ^ (4 : ℕ))‖)
      atTop atTop := by
  refine (tendsto_norm_massBesselDyadicAperture_atTop a sigma ha hsigma).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hfloor : 1 ≤ ⌊X⌋₊ := by
    apply Nat.le_floor
    exact_mod_cast hX
  exact congrArg norm
    (xiMassCriticalDyadicPrimePacket_eq_massBesselDyadicAperture ha hsigma hfloor).symm

end

end RHTower
