import GaloisForLFunctions.HTGeometry.DepthTwoHankelCurve
import GaloisForLFunctions.HTGeometry.DepthTwoGeneralPacketBound
import GaloisForLFunctions.HTGeometry.OneDepthHankelBound

/-!
# The bounds at the reciprocal depth

Exchanging the jet with its reciprocal exchanges the two depths and the two observed packets, so
every bound proved at a small *jet* depth transports to the same bound at a small *reciprocal*
depth.  The hypotheses transport with it: what was a condition on the observed reciprocal packet
becomes the same condition on the observed jet packet.

This doubles the regimes covered by the depth-one and depth-two counts at no mathematical cost, and
the resulting hypotheses are genuinely different — at both depths two, finiteness now follows from
either observed packet being critical, not only from the reciprocal one.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-! ## Reciprocal depth one -/

/-- **At reciprocal depth one the fibre has at most the critical binomial multiplicity of
points.** -/
theorem nat_card_criticalFibre_snd_one_le_of_tail (hm : 0 < m) {U V : K[X]}
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ (1 : ℕ) ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0) (hUm : U.coeff m ≠ 0) :
    Nat.card (criticalFibre K m 1 U V) ≤ criticalHorizonMultiplicity m 1 := by
  rw [Nat.card_congr (criticalFibreSwap m 1 U V), criticalHorizonMultiplicity_comm]
  exact nat_card_criticalFibre_one_le_of_tail hm hV hU hV0 hU0 hUm

/-! ## Reciprocal depth two -/

/-- **At reciprocal depth two the fibre is finite, with an explicit bound.** -/
theorem nat_card_criticalFibre_snd_depth_two_le (hm : 0 < m) {U V : K[X]}
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (hgen : ∀ p q : criticalFibre K 2 m V U, p ≠ q →
      Polynomial.resultant (hankelCurve (p.1.1 + V) V m) (hankelCurve (q.1.1 + V) V m) m m ≠ 0 ∧
      Polynomial.resultant (hankelCurveSwap (p.1.1 + V) V m)
        (hankelCurveSwap (q.1.1 + V) V m) m m ≠ 0) :
    Nat.card (criticalFibre K m 2 U V) ≤ 2 + m * m * (m * m) := by
  rw [Nat.card_congr (criticalFibreSwap m 2 U V)]
  exact nat_card_criticalFibre_depth_two_le hm hV hU hV0 hU0 hgen

/-- **At both depths two, a critical observed jet packet already forces finiteness.**  The dual of
the unconditional depth-two bound: the hypothesis moves from the reciprocal packet to the jet
packet. -/
theorem nat_card_criticalFibre_two_two_le_of_critical_fst {U V : K[X]}
    (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V) (hu₂ : U.coeff 2 ≠ 0) :
    Nat.card (criticalFibre K 2 2 U V) ≤ 12 := by
  rw [Nat.card_congr (criticalFibreSwap 2 2 U V)]
  exact nat_card_criticalFibre_two_two_le_of_critical hV hU hu₂

end GaloisForLFunctions.HTGeometry
