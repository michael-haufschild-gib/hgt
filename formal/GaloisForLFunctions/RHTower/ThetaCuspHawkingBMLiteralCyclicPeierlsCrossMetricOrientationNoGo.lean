import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCrossBranchBidegree
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCausalPeierlsPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsOrderedCurrent

/-!
# The complementary metric alone forgets CTP order

The literal cross-branch metric has amplitude `a²d²/64`. Exchanging its two
source legs therefore leaves the entire metric field unchanged. Every
readout of that field, including one using its derivatives or boundaries,
has zero antisymmetrization. The actual full-circle CTP source pairing is
skew under the same exchange. Thus an incidence through this single metric
field for both orders can carry only a zero CTP pairing.

This retires the metric-only version of the complementary-rate B2 carrier.
The ordered two-field Einstein current with its source contact remains a
parity-compatible survivor; its CTP exchange law is already established in
`ThetaCuspHawkingBMLiteralCyclicPeierlsOrderedCurrent`.

Proof-chain role:
`complementary-rate CTP source -> ordered metric/current plus contact ->
cap/cusp boundary -> PW fixed-grade balance -> RH`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsCrossMetricOrientationNoGo

open D4BMLiteralCyclicPeierlsCrossBranchBidegree
open D4BMFullAngularCausalPeierls
open D4BMPhysicalLiftCurrent D4BMLiteralCyclicPeierlsOrderedCurrent

noncomputable section
set_option autoImplicit false

/-- Leg exchange fixes the complete complementary metric field, at every
spacetime point. This is stronger than symmetry of a chosen boundary value. -/
theorem crossBranchMetric_swap (q : XiZeroCopy) (a d : ℂ) :
    (fun x => crossBranchMetric q a d x) =
      (fun x => crossBranchMetric q d a x) := by
  funext x
  unfold crossBranchMetric
  rw [mul_comm (a ^ (2 : ℕ)) (d ^ (2 : ℕ))]

/-- No operation on the single reconstructed metric field can recover the
ordered CTP difference: the two input fields are definitionally equal after
the proved exchange. The readout may inspect the entire field. -/
theorem crossBranchMetric_readout_orderDifference_zero (q : XiZeroCopy)
    (a d : ℂ)
    (readout : ((Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) → ℂ) :
    readout (fun x => crossBranchMetric q a d x) -
      readout (fun x => crossBranchMetric q d a x) = 0 := by
  rw [crossBranchMetric_swap, sub_self]

/-- Exact no-go for a metric-only realization in both CTP orders. If its
single-field readout agrees with the literal full source pairing in both
orientations, that pairing is forced to vanish. -/
theorem metric_only_incidence_forces_fullCausalPair_zero
    (q : XiZeroCopy) (branch : Bool) (a d : ℂ) (X k : ℝ)
    (readout : ((Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) → ℂ)
    (hforward : readout (fun x => crossBranchMetric q a d x) =
      fullCausalSourcePair q branch true false a d X k)
    (hreverse : readout (fun x => crossBranchMetric q d a x) =
      fullCausalSourcePair q branch false true d a X k) :
    fullCausalSourcePair q branch true false a d X k = 0 := by
  have hzero := crossBranchMetric_readout_orderDifference_zero q a d readout
  rw [hforward, hreverse,
    fullCausalSourcePair_skew q branch false true d a X k] at hzero
  have htwo : (2 : ℂ) * fullCausalSourcePair q branch true false a d X k = 0 := by
    linear_combination hzero
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- A displayed pair of literal fields retaining both exchange sectors:
the reconstructed complementary metric and the ordered contact-completed
Einstein current. This pairing alone does not identify their physical
incidence or establish the CTP boundary equality. -/
def complementaryMetricCurrentCarrier (q : XiZeroCopy) (b : Bool) (a d : ℂ)
    (r v : ℝ) (z : D4BMHorizon.Point) :
    (((Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) × (Fin 4 → ℂ)) :=
  ((fun x => crossBranchMetric q a d x),
    liftAngularCurrent q (D4BMModularCore.physicalRate q b)
      (D4BMModularCore.physicalRate q (!b)) a d r v z)

/-- Exchange fixes the metric sector and negates the contact-completed
current sector. The equation records the surviving parity data; it does not
identify the metric's current with the separate ordered current. -/
theorem complementaryMetricCurrentCarrier_exchange (q : XiZeroCopy) (b : Bool)
    (a d : ℂ) (r v : ℝ) (z : D4BMHorizon.Point) :
    complementaryMetricCurrentCarrier q (!b) d a r v z =
      ((complementaryMetricCurrentCarrier q b a d r v z).1,
        -(complementaryMetricCurrentCarrier q b a d r v z).2) := by
  apply Prod.ext
  · exact (crossBranchMetric_swap q a d).symm
  · simpa [complementaryMetricCurrentCarrier] using
      liftAngularCurrent_ctp_swap q
        (D4BMModularCore.physicalRate q (!b))
        (D4BMModularCore.physicalRate q b) d a r v z

end

end RHTower.D4BMLiteralCyclicPeierlsCrossMetricOrientationNoGo
