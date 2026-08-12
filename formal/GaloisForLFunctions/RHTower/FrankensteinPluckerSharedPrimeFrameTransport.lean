import GaloisForLFunctions.RHTower.FrankensteinPluckerCovariantInverseIncidence

/-!
# Source-derived shared-prime transport for Pluecker reporter frames

Identity transport between neighboring physical reporter frames is false.  Arbitrary transport
would be noncanonical.  This module constructs the literal alternative forced by shared-prime
incidence: trivialize each reporter by its positive P-G84/P-G91/P-G92 scale, swap the two prime
pairs, then rescale in the target packet.

After trivialization every reporter is the same universal selected-pair incidence coefficient.
The resulting transport is positive, invertible by reversing source and target, and maps both
retained right reporters exactly to the corresponding next-packet left reporters.  Thus local
transported mismatch vanishes without identifying unequal physical coefficients.

This is a finite source-frame theorem.  Global transported summation and completed Xi target
identification remain separate gates.
-/

open scoped BigOperators

noncomputable section
namespace RHTower.HedenmalmThetaSource

/-! ## Prime-pair involutions and universal incidence -/

/-- Swap the lower and upper prime pairs: `(0,1) ↔ (2,3)`. -/
def fourRatePrimePairSwap : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- Induced involution on the six unordered pairs of four coordinates. -/
def fourRateSelectedPairSwap : Fin 6 → Fin 6 := ![5, 1, 3, 2, 4, 0]

theorem fourRatePrimePairSwap_involutive : Function.Involutive fourRatePrimePairSwap := by
  intro i
  fin_cases i <;> rfl

theorem fourRateSelectedPairSwap_involutive :
    Function.Involutive fourRateSelectedPairSwap := by
  intro s
  fin_cases s <;> rfl

/-- Packet-independent coefficient of coordinate `i` in selected-pair difference `s-t`. -/
def fourRateUniversalCoordinateReporter
    (s t : Fin 6) (i : Fin 4) : ℂ :=
  fourRateSelectedSumC (fun j => if j = i then 1 else 0) s -
    fourRateSelectedSumC (fun j => if j = i then 1 else 0) t

/-- Universal incidence is equivariant under simultaneous prime-pair and selected-pair swap. -/
theorem fourRateUniversalCoordinateReporter_swap
    (s t : Fin 6) (i : Fin 4) :
    fourRateUniversalCoordinateReporter s t i =
      fourRateUniversalCoordinateReporter
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
        (fourRatePrimePairSwap i) := by
  fin_cases s <;> fin_cases t <;> fin_cases i <;>
    simp [fourRateUniversalCoordinateReporter, fourRateSelectedSumC,
      fourRatePrimePairSwap, fourRateSelectedPairSwap,
      RHTower.fourRatePairLeft, RHTower.fourRatePairRight]

/-! ## Positive physical frame and exact trivialization -/

/-- Complete positive reporter scale: raw P-G84 mass, P-G91 probability, and P-G92 node. -/
def frankensteinPluckerReporterScale
    (z : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) : ℝ :=
  Real.sqrt (gammaSewnCriticalAdjacentPrime_DenominatorTerm z) *
    Real.sqrt (frankensteinPluckerProbability z s *
      frankensteinPluckerProbability z t / 2) *
    Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i)

theorem frankensteinPluckerReporterScale_pos
    (z : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    0 < frankensteinPluckerReporterScale z s t i := by
  unfold frankensteinPluckerReporterScale
  exact mul_pos
    (mul_pos
      (Real.sqrt_pos.2 (gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos z))
      (Real.sqrt_pos.2 (div_pos
        (mul_pos (frankensteinPluckerProbability_pos z s)
          (frankensteinPluckerProbability_pos z t)) (by norm_num))))
    (Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos _ _ _ _))

/-- Literal physical reporter equals positive frame scale times universal incidence. -/
theorem frankensteinPluckerPhysicalCoordinateReporter_eq_scale_mul_universal
    (z : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    frankensteinPluckerPhysicalCoordinateReporter z s t i =
      (frankensteinPluckerReporterScale z s t i : ℂ) *
        fourRateUniversalCoordinateReporter s t i := by
  unfold frankensteinPluckerPhysicalCoordinateReporter
  rw [frankensteinPluckerCoordinateReporter,
    fourRatePluckerCoordinateReporter, fourRatePluckerDispersionFeature]
  unfold frankensteinPluckerReporterScale fourRateUniversalCoordinateReporter
  push_cast
  ring

/-! ## Coefficient-faithful non-equivariant transport -/

/-- Division-free transport identity.  Every literal coefficient remains visible on both sides. -/
theorem frankensteinPluckerPhysicalCoordinateReporter_cross_transport
    (z z' : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    (frankensteinPluckerReporterScale z'
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
        (fourRatePrimePairSwap i) : ℂ) *
        frankensteinPluckerPhysicalCoordinateReporter z s t i =
      (frankensteinPluckerReporterScale z s t i : ℂ) *
        frankensteinPluckerPhysicalCoordinateReporter z'
          (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
          (fourRatePrimePairSwap i) := by
  rw [frankensteinPluckerPhysicalCoordinateReporter_eq_scale_mul_universal,
    frankensteinPluckerPhysicalCoordinateReporter_eq_scale_mul_universal,
    fourRateUniversalCoordinateReporter_swap]
  ring

/-- Canonical positive rescaling from source reporter frame to target swapped frame. -/
def frankensteinPluckerReporterTransportCoefficient
    (z z' : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) : ℝ :=
  frankensteinPluckerReporterScale z'
      (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
      (fourRatePrimePairSwap i) /
    frankensteinPluckerReporterScale z s t i

theorem frankensteinPluckerReporterTransportCoefficient_pos
    (z z' : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    0 < frankensteinPluckerReporterTransportCoefficient z z' s t i := by
  exact div_pos (frankensteinPluckerReporterScale_pos _ _ _ _)
    (frankensteinPluckerReporterScale_pos _ _ _ _)

/-- Reversing transport gives the exact multiplicative inverse. -/
theorem frankensteinPluckerReporterTransportCoefficient_mul_reverse
    (z z' : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    frankensteinPluckerReporterTransportCoefficient z z' s t i *
      frankensteinPluckerReporterTransportCoefficient z' z
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
        (fourRatePrimePairSwap i) = 1 := by
  unfold frankensteinPluckerReporterTransportCoefficient
  rw [fourRateSelectedPairSwap_involutive s,
    fourRateSelectedPairSwap_involutive t,
    fourRatePrimePairSwap_involutive i]
  field_simp [
    (frankensteinPluckerReporterScale_pos z s t i).ne',
    (frankensteinPluckerReporterScale_pos z'
      (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
      (fourRatePrimePairSwap i)).ne']

/-- Two consecutive swapped transports have no extra holonomy: intermediate frame scale cancels
and only direct endpoint scale ratio remains. -/
theorem frankensteinPluckerReporterTransportCoefficient_two_step
    (z₀ z₁ z₂ : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    frankensteinPluckerReporterTransportCoefficient z₀ z₁ s t i *
      frankensteinPluckerReporterTransportCoefficient z₁ z₂
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
        (fourRatePrimePairSwap i) =
      frankensteinPluckerReporterScale z₂ s t i /
        frankensteinPluckerReporterScale z₀ s t i := by
  unfold frankensteinPluckerReporterTransportCoefficient
  rw [fourRateSelectedPairSwap_involutive s,
    fourRateSelectedPairSwap_involutive t,
    fourRatePrimePairSwap_involutive i]
  field_simp [
    (frankensteinPluckerReporterScale_pos z₀ s t i).ne',
    (frankensteinPluckerReporterScale_pos z₁
      (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
      (fourRatePrimePairSwap i)).ne']

/-- Ratio form: canonical transport maps every physical coordinate reporter exactly. -/
theorem frankensteinPluckerPhysicalCoordinateReporter_transport
    (z z' : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    frankensteinPluckerPhysicalCoordinateReporter z'
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
        (fourRatePrimePairSwap i) =
      (frankensteinPluckerReporterTransportCoefficient z z' s t i : ℂ) *
        frankensteinPluckerPhysicalCoordinateReporter z s t i := by
  have hcross := frankensteinPluckerPhysicalCoordinateReporter_cross_transport
    z z' s t i
  have hscale : (frankensteinPluckerReporterScale z s t i : ℂ) ≠ 0 := by
    exact_mod_cast (frankensteinPluckerReporterScale_pos z s t i).ne'
  unfold frankensteinPluckerReporterTransportCoefficient
  push_cast
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hscale).2
  calc
    _ = (frankensteinPluckerReporterScale z s t i : ℂ) *
        frankensteinPluckerPhysicalCoordinateReporter z'
          (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
          (fourRatePrimePairSwap i) := by ring
    _ = _ := hcross.symm

/-! ## Metric compatibility -/

/-- Canonical fibre norm in which physical frame scale is retained as metric density. -/
def frankensteinPluckerReporterMetricNorm
    (z : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) (x : ℂ) : ℝ :=
  ‖x‖ / frankensteinPluckerReporterScale z s t i

/-- A physical reporter has exactly its universal-incidence norm in the canonical fibre metric. -/
theorem frankensteinPluckerPhysicalCoordinateReporter_metricNorm
    (z : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    frankensteinPluckerReporterMetricNorm z s t i
        (frankensteinPluckerPhysicalCoordinateReporter z s t i) =
      ‖fourRateUniversalCoordinateReporter s t i‖ := by
  rw [frankensteinPluckerReporterMetricNorm,
    frankensteinPluckerPhysicalCoordinateReporter_eq_scale_mul_universal,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (frankensteinPluckerReporterScale_pos z s t i)]
  field_simp [(frankensteinPluckerReporterScale_pos z s t i).ne']

/-- Non-equivariant shared-prime transport is an exact isometry for the source-derived variable
fibre metric.  Literal coefficient variation is stored in the metric rather than erased. -/
theorem frankensteinPluckerReporterTransport_metricNorm
    (z z' : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) (x : ℂ) :
    frankensteinPluckerReporterMetricNorm z'
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
        (fourRatePrimePairSwap i)
        ((frankensteinPluckerReporterTransportCoefficient z z' s t i : ℂ) * x) =
      frankensteinPluckerReporterMetricNorm z s t i x := by
  rw [frankensteinPluckerReporterMetricNorm,
    frankensteinPluckerReporterMetricNorm, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (frankensteinPluckerReporterTransportCoefficient_pos z z' s t i)]
  unfold frankensteinPluckerReporterTransportCoefficient
  field_simp [
    (frankensteinPluckerReporterScale_pos z s t i).ne',
    (frankensteinPluckerReporterScale_pos z'
      (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t)
      (fourRatePrimePairSwap i)).ne']

/-! ## The two retained shared-prime orientations -/

/-- Right lower reporter of packet `n` transports exactly to left lower reporter of packet `n+1`. -/
theorem frankensteinPluckerLowerSharedPrimeReporter_transport
    (e n : ℕ) (s t : Fin 6) :
    frankensteinPluckerLowerLeftReporter (e := e)
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t) (n + 1) =
      (frankensteinPluckerReporterTransportCoefficient (e, n) (e, n + 1) s t 2 : ℂ) *
        frankensteinPluckerLowerRightReporter e s t n := by
  exact frankensteinPluckerPhysicalCoordinateReporter_transport
    (e, n) (e, n + 1) s t 2

/-- Right upper reporter of packet `n` transports exactly to left upper reporter of packet `n+1`. -/
theorem frankensteinPluckerUpperSharedPrimeReporter_transport
    (e n : ℕ) (s t : Fin 6) :
    frankensteinPluckerUpperLeftReporter (e := e)
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t) (n + 1) =
      (frankensteinPluckerReporterTransportCoefficient (e, n) (e, n + 1) s t 3 : ℂ) *
        frankensteinPluckerUpperRightReporter e s t n := by
  exact frankensteinPluckerPhysicalCoordinateReporter_transport
    (e, n) (e, n + 1) s t 3

def frankensteinPluckerTransportedReporterMismatch
    (target source : ℂ) (transport : ℝ) : ℂ :=
  target - (transport : ℂ) * source

/-- Canonical transport annihilates lower shared-prime frame mismatch exactly. -/
theorem frankensteinPluckerLowerSharedPrime_transport_mismatch_eq_zero
    (e n : ℕ) (s t : Fin 6) :
    frankensteinPluckerTransportedReporterMismatch
      (frankensteinPluckerLowerLeftReporter (e := e)
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t) (n + 1))
      (frankensteinPluckerLowerRightReporter e s t n)
      (frankensteinPluckerReporterTransportCoefficient
        (e, n) (e, n + 1) s t 2) = 0 := by
  rw [frankensteinPluckerTransportedReporterMismatch,
    frankensteinPluckerLowerSharedPrimeReporter_transport]
  ring

/-- Canonical transport annihilates upper shared-prime frame mismatch exactly. -/
theorem frankensteinPluckerUpperSharedPrime_transport_mismatch_eq_zero
    (e n : ℕ) (s t : Fin 6) :
    frankensteinPluckerTransportedReporterMismatch
      (frankensteinPluckerUpperLeftReporter (e := e)
        (fourRateSelectedPairSwap s) (fourRateSelectedPairSwap t) (n + 1))
      (frankensteinPluckerUpperRightReporter e s t n)
      (frankensteinPluckerReporterTransportCoefficient
        (e, n) (e, n + 1) s t 3) = 0 := by
  rw [frankensteinPluckerTransportedReporterMismatch,
    frankensteinPluckerUpperSharedPrimeReporter_transport]
  ring

end RHTower.HedenmalmThetaSource
