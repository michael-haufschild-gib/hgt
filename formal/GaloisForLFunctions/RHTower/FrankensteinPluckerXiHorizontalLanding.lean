import GaloisForLFunctions.RHTower.FrankensteinPluckerCovariantHorizontalCarrier
import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier

/-!
# Frankenstein Plücker Xi horizontal landing

Lands the literal source-zero horizontal prime coefficient in two positive
Plücker charts fixed by the selected-pair involution.  Both chart weights are
strictly positive, so this coefficient-faithful landing preserves the exact
zero radical, every nth-prime label, every depth label, divisor multiplicity,
and both reflection orientations.

The resulting lower and upper edge currents satisfy exact finite incidence
telescopes and are reflection-odd.  No asymptotic summability or annihilation
law is asserted here: the module isolates that remaining analytic producer
without replacing it by a hypothesis.
-/

open scoped BigOperators
noncomputable section
namespace RHTower.HedenmalmThetaSource

theorem iteratedFourRateSelectedPairSwap_one (n : ℕ) :
    iteratedFourRateSelectedPairSwap n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega,
        iteratedFourRateSelectedPairSwap_succ, ih]
      rfl

theorem iteratedFourRateSelectedPairSwap_four (n : ℕ) :
    iteratedFourRateSelectedPairSwap n 4 = 4 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega,
        iteratedFourRateSelectedPairSwap_succ, ih]
      rfl

theorem fourRateUniversalCoordinateReporter_one_four_zero :
    fourRateUniversalCoordinateReporter 1 4 0 = 1 := by
  have hl1 : RHTower.fourRatePairLeft (1 : Fin 6) = 0 := rfl
  have hr1 : RHTower.fourRatePairRight (1 : Fin 6) = 2 := rfl
  have hl4 : RHTower.fourRatePairLeft (4 : Fin 6) = 1 := rfl
  have hr4 : RHTower.fourRatePairRight (4 : Fin 6) = 3 := rfl
  simp [fourRateUniversalCoordinateReporter, fourRateSelectedSumC,
    hl1, hr1, hl4, hr4]

theorem fourRateUniversalCoordinateReporter_four_one_one :
    fourRateUniversalCoordinateReporter 4 1 1 = 1 := by
  have hl1 : RHTower.fourRatePairLeft (1 : Fin 6) = 0 := rfl
  have hr1 : RHTower.fourRatePairRight (1 : Fin 6) = 2 := rfl
  have hl4 : RHTower.fourRatePairLeft (4 : Fin 6) = 1 := rfl
  have hr4 : RHTower.fourRatePairRight (4 : Fin 6) = 3 := rfl
  simp [fourRateUniversalCoordinateReporter, fourRateSelectedSumC,
    hl1, hr1, hl4, hr4]

theorem frankensteinPluckerLowerVertexReporter_one_four_eq_scale
    (e n : ℕ) :
    frankensteinPluckerLowerVertexReporter e 1 4 n =
      (frankensteinPluckerReporterScale (e, n) 1 4 0 : ℂ) := by
  rw [frankensteinPluckerLowerVertexReporter,
    iteratedFourRateSelectedPairSwap_one,
    iteratedFourRateSelectedPairSwap_four,
    frankensteinPluckerLowerLeftReporter,
    frankensteinPluckerPhysicalCoordinateReporter_eq_scale_mul_universal,
    fourRateUniversalCoordinateReporter_one_four_zero, mul_one]

theorem frankensteinPluckerUpperVertexReporter_four_one_eq_scale
    (e n : ℕ) :
    frankensteinPluckerUpperVertexReporter e 4 1 n =
      (frankensteinPluckerReporterScale (e, n) 4 1 1 : ℂ) := by
  rw [frankensteinPluckerUpperVertexReporter,
    iteratedFourRateSelectedPairSwap_four,
    iteratedFourRateSelectedPairSwap_one,
    frankensteinPluckerUpperLeftReporter,
    frankensteinPluckerPhysicalCoordinateReporter_eq_scale_mul_universal,
    fourRateUniversalCoordinateReporter_four_one_one, mul_one]

theorem frankensteinPluckerLowerVertexReporter_one_four_ne_zero
    (e n : ℕ) : frankensteinPluckerLowerVertexReporter e 1 4 n ≠ 0 := by
  rw [frankensteinPluckerLowerVertexReporter_one_four_eq_scale]
  exact_mod_cast (frankensteinPluckerReporterScale_pos (e, n) 1 4 0).ne'

theorem frankensteinPluckerUpperVertexReporter_four_one_ne_zero
    (e n : ℕ) : frankensteinPluckerUpperVertexReporter e 4 1 n ≠ 0 := by
  rw [frankensteinPluckerUpperVertexReporter_four_one_eq_scale]
  exact_mod_cast (frankensteinPluckerReporterScale_pos (e, n) 4 1 1).ne'

def frankensteinXiLowerPrimeCarrier
    (q : RHTower.XiZeroCopy) (e n : ℕ) : ℂ :=
  frankensteinPluckerLowerVertexReporter e 1 4 n *
    (RHTower.sourceZeroHorizontalPrimeCarrier q (RHTower.nthPrimeSubtype n) : ℂ)

def frankensteinXiUpperPrimeCarrier
    (q : RHTower.XiZeroCopy) (e n : ℕ) : ℂ :=
  frankensteinPluckerUpperVertexReporter e 4 1 n *
    (RHTower.sourceZeroHorizontalPrimeCarrier q (RHTower.nthPrimeSubtype n) : ℂ)

theorem frankensteinXiLowerPrimeCarrier_eq_zero_iff
    (q : RHTower.XiZeroCopy) (e n : ℕ) :
    frankensteinXiLowerPrimeCarrier q e n = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [frankensteinXiLowerPrimeCarrier, mul_eq_zero,
    or_iff_right (frankensteinPluckerLowerVertexReporter_one_four_ne_zero e n),
    Complex.ofReal_eq_zero,
    RHTower.sourceZeroHorizontalPrimeCarrier_eq_zero_iff]

theorem frankensteinXiUpperPrimeCarrier_eq_zero_iff
    (q : RHTower.XiZeroCopy) (e n : ℕ) :
    frankensteinXiUpperPrimeCarrier q e n = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [frankensteinXiUpperPrimeCarrier, mul_eq_zero,
    or_iff_right (frankensteinPluckerUpperVertexReporter_four_one_ne_zero e n),
    Complex.ofReal_eq_zero,
    RHTower.sourceZeroHorizontalPrimeCarrier_eq_zero_iff]

theorem frankensteinXiLowerPrimeCarrier_reflection
    (q : RHTower.XiZeroCopy) (e n : ℕ) :
    frankensteinXiLowerPrimeCarrier (RHTower.xiZeroCopyLineConjEquiv q) e n =
      -frankensteinXiLowerPrimeCarrier q e n := by
  rw [frankensteinXiLowerPrimeCarrier, frankensteinXiLowerPrimeCarrier,
    RHTower.sourceZeroHorizontalPrimeCarrier_reflection]
  push_cast
  ring

theorem frankensteinXiUpperPrimeCarrier_reflection
    (q : RHTower.XiZeroCopy) (e n : ℕ) :
    frankensteinXiUpperPrimeCarrier (RHTower.xiZeroCopyLineConjEquiv q) e n =
      -frankensteinXiUpperPrimeCarrier q e n := by
  rw [frankensteinXiUpperPrimeCarrier, frankensteinXiUpperPrimeCarrier,
    RHTower.sourceZeroHorizontalPrimeCarrier_reflection]
  push_cast
  ring

def frankensteinXiPhysicalHorizontalCarrierAt
    (q : RHTower.XiZeroCopy) (e n : ℕ) : ℂ × ℂ :=
  (frankensteinXiLowerPrimeCarrier q e n,
    frankensteinXiUpperPrimeCarrier q e n)

def frankensteinXiPhysicalHorizontalCarrier
    (q : RHTower.XiZeroCopy) : ℕ → ℕ → ℂ × ℂ :=
  fun e n => frankensteinXiPhysicalHorizontalCarrierAt q e n

theorem frankensteinXiPhysicalHorizontalCarrierAt_eq_zero_iff
    (q : RHTower.XiZeroCopy) (e n : ℕ) :
    frankensteinXiPhysicalHorizontalCarrierAt q e n = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    exact (frankensteinXiLowerPrimeCarrier_eq_zero_iff q e n).1
      (congrArg Prod.fst hzero)
  · intro hline
    apply Prod.ext
    · exact (frankensteinXiLowerPrimeCarrier_eq_zero_iff q e n).2 hline
    · exact (frankensteinXiUpperPrimeCarrier_eq_zero_iff q e n).2 hline

theorem frankensteinXiPhysicalHorizontalCarrierAt_reflection
    (q : RHTower.XiZeroCopy) (e n : ℕ) :
    frankensteinXiPhysicalHorizontalCarrierAt
        (RHTower.xiZeroCopyLineConjEquiv q) e n =
      -frankensteinXiPhysicalHorizontalCarrierAt q e n := by
  apply Prod.ext
  · exact frankensteinXiLowerPrimeCarrier_reflection q e n
  · exact frankensteinXiUpperPrimeCarrier_reflection q e n

theorem frankensteinXiPhysicalHorizontalCarrier_eq_zero_iff
    (q : RHTower.XiZeroCopy) :
    frankensteinXiPhysicalHorizontalCarrier q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have h00 := congrFun (congrFun hzero 0) 0
    exact (frankensteinXiPhysicalHorizontalCarrierAt_eq_zero_iff q 0 0).1 h00
  · intro hline
    funext e n
    exact (frankensteinXiPhysicalHorizontalCarrierAt_eq_zero_iff q e n).2 hline

def frankensteinXiLowerCovariantEdgeCurrent
    (q : RHTower.XiZeroCopy) (e n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) *
    (frankensteinXiLowerPrimeCarrier q e n -
      frankensteinXiLowerPrimeCarrier q e (n + 1))

def frankensteinXiUpperCovariantEdgeCurrent
    (q : RHTower.XiZeroCopy) (e n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) *
    (frankensteinXiUpperPrimeCarrier q e n -
      frankensteinXiUpperPrimeCarrier q e (n + 1))

theorem sum_range_frankensteinXiLowerCovariantEdgeCurrent
    (q : RHTower.XiZeroCopy) (e N : ℕ) :
    (∑ n ∈ Finset.range N, frankensteinXiLowerCovariantEdgeCurrent q e n) =
      (∑ n ∈ Finset.range N, frankensteinXiLowerPrimeCarrier q e n) -
        (N : ℂ) * frankensteinXiLowerPrimeCarrier q e N := by
  exact complex_sum_range_weighted_vertex_incidence
    (frankensteinXiLowerPrimeCarrier q e) N

theorem sum_range_frankensteinXiUpperCovariantEdgeCurrent
    (q : RHTower.XiZeroCopy) (e N : ℕ) :
    (∑ n ∈ Finset.range N, frankensteinXiUpperCovariantEdgeCurrent q e n) =
      (∑ n ∈ Finset.range N, frankensteinXiUpperPrimeCarrier q e n) -
        (N : ℂ) * frankensteinXiUpperPrimeCarrier q e N := by
  exact complex_sum_range_weighted_vertex_incidence
    (frankensteinXiUpperPrimeCarrier q e) N

theorem frankensteinXiLowerCovariantEdgeCurrent_reflection
    (q : RHTower.XiZeroCopy) (e n : ℕ) :
    frankensteinXiLowerCovariantEdgeCurrent
        (RHTower.xiZeroCopyLineConjEquiv q) e n =
      -frankensteinXiLowerCovariantEdgeCurrent q e n := by
  rw [frankensteinXiLowerCovariantEdgeCurrent,
    frankensteinXiLowerCovariantEdgeCurrent,
    frankensteinXiLowerPrimeCarrier_reflection,
    frankensteinXiLowerPrimeCarrier_reflection]
  ring

theorem frankensteinXiUpperCovariantEdgeCurrent_reflection
    (q : RHTower.XiZeroCopy) (e n : ℕ) :
    frankensteinXiUpperCovariantEdgeCurrent
        (RHTower.xiZeroCopyLineConjEquiv q) e n =
      -frankensteinXiUpperCovariantEdgeCurrent q e n := by
  rw [frankensteinXiUpperCovariantEdgeCurrent,
    frankensteinXiUpperCovariantEdgeCurrent,
    frankensteinXiUpperPrimeCarrier_reflection,
    frankensteinXiUpperPrimeCarrier_reflection]
  ring

end RHTower.HedenmalmThetaSource

