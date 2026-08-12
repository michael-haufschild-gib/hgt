import GaloisForLFunctions.RHTower.FrankensteinPluckerInverseIncidenceCurrent

/-!
# Covariant inverse incidence for the Frankenstein Pluecker current

Physical P-G84/P-G91/P-G92 reporters vary from one adjacent-prime packet to the next and distinguish
the two ends of each packet.  They therefore cannot pass through P-G86 inverse incidence as a
constant scalar.  This module gives the exact replacement.

Every finite asymmetric reporter current splits into diagonal source response, a moving-reporter
connection, left/right reporter mismatch, and terminal flux.  The generic law is then instantiated
with the literal four-coordinate Pluecker reporters, proving that the actual Frankenstein current
is the sum of two such covariant inverse-incidence channels, one at each retained depth.

No sign is assigned to connection or mismatch.  The module exposes the exact remaining source
terms; it does not assume their cancellation, identify a completed Xi target, or prove RH.
-/

open scoped BigOperators

noncomputable section
namespace RHTower.HedenmalmThetaSource

/-! ## Literal coordinate reporters -/

/-- Coefficient of coordinate `i` in the four-rate pair-dispersion feature. -/
def fourRatePluckerCoordinateReporter
    (weight : Fin 6 → ℝ) (s t : Fin 6) (i : Fin 4) : ℂ :=
  fourRatePluckerDispersionFeature weight (fun j => if j = i then 1 else 0) s t

/-- Exact four-coordinate expansion of the pair-dispersion feature. -/
theorem fourRatePluckerDispersionFeature_eq_sum_coordinateReporter
    (weight : Fin 6 → ℝ) (x : Fin 4 → ℂ) (s t : Fin 6) :
    fourRatePluckerDispersionFeature weight x s t =
      ∑ i, fourRatePluckerCoordinateReporter weight s t i * x i := by
  fin_cases s <;> fin_cases t <;>
    simp [fourRatePluckerCoordinateReporter, fourRatePluckerDispersionFeature,
      fourRateSelectedSumC, RHTower.fourRatePairLeft, RHTower.fourRatePairRight,
      Fin.sum_univ_succ] <;>
    ring

/-- Literal Pluecker coordinate reporter after P-G92 reciprocal-node congruence. -/
def frankensteinPluckerCoordinateReporter
    (z : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) : ℂ :=
  fourRatePluckerCoordinateReporter (frankensteinPluckerProbability z) s t i *
    (Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i) : ℂ)

/-- P-G91/P-G92 feature is exactly the sum of its four literal coordinate reporters. -/
theorem frankensteinPluckerPacketFeature_eq_sum_coordinateReporter
    (a : RHTower.DeningerHeightKothe) (z : ℕ × ℕ) (s t : Fin 6) :
    frankensteinPluckerPacketFeature a z s t =
      ∑ i, frankensteinPluckerCoordinateReporter z s t i *
        frankensteinPluckerSignedPacket a z i := by
  rw [frankensteinPluckerPacketFeature,
    fourRatePluckerDispersionFeature_eq_sum_coordinateReporter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [frankensteinPluckerCoordinateReporter,
    frankensteinPluckerNodeWeightedSignedPacket,
    frankensteinPluckerNodeWeight]
  ring

/-! ## Generic covariant inverse incidence -/

/-- Weighted inverse incidence with a packet-dependent common reporter. -/
theorem complex_sum_range_weighted_moving_reporter
    (L a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        ((n + 1 : ℕ) : ℂ) * L n * (a n - a (n + 1))) =
      (∑ n ∈ Finset.range N, L n * a n) +
        (∑ n ∈ Finset.range (N - 1),
          ((n + 1 : ℕ) : ℂ) * (L (n + 1) - L n) * a (n + 1)) -
        (N : ℂ) * L (N - 1) * a N := by
  induction N with
  | zero => simp
  | succ N ih =>
      cases N with
      | zero => simp; ring
      | succ N =>
          simp only [Nat.succ_sub_one] at ih ⊢
          rw [Finset.sum_range_succ, ih]
          simp only [Finset.sum_range_succ]
          push_cast
          ring

/-- Exact asymmetric reporter law.  Third term is left/right mismatch, independent of the
moving-frame connection in the second term. -/
theorem complex_sum_range_asymmetric_reporter
    (L R a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        ((n + 1 : ℕ) : ℂ) * (L n * a n - R n * a (n + 1))) =
      (∑ n ∈ Finset.range N, L n * a n) +
        (∑ n ∈ Finset.range (N - 1),
          ((n + 1 : ℕ) : ℂ) * (L (n + 1) - L n) * a (n + 1)) +
        (∑ n ∈ Finset.range N,
          ((n + 1 : ℕ) : ℂ) * (L n - R n) * a (n + 1)) -
        (N : ℂ) * L (N - 1) * a N := by
  rw [show (∑ n ∈ Finset.range N,
      ((n + 1 : ℕ) : ℂ) * (L n * a n - R n * a (n + 1))) =
      (∑ n ∈ Finset.range N,
        ((n + 1 : ℕ) : ℂ) * L n * (a n - a (n + 1))) +
      (∑ n ∈ Finset.range N,
        ((n + 1 : ℕ) : ℂ) * (L n - R n) * a (n + 1)) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring,
    complex_sum_range_weighted_moving_reporter]
  ring

def covariantAsymmetricReporterCurrent
    (L R a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) * (L n * a n - R n * a (n + 1))

/-- Diagonal source response retained by covariant inverse incidence. -/
def covariantAsymmetricReporterDiagonal
    (L a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, L n * a n

/-- Discrete connection produced by motion of the left reporter frame. -/
def covariantAsymmetricReporterConnection
    (L a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N - 1),
    ((n + 1 : ℕ) : ℂ) * (L (n + 1) - L n) * a (n + 1)

/-- Orientation mismatch between the two physical ends of each packet. -/
def covariantAsymmetricReporterMismatch
    (L R a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ((n + 1 : ℕ) : ℂ) * (L n - R n) * a (n + 1)

/-- Terminal flux of a finite inverse-incidence prefix. -/
def covariantAsymmetricReporterTerminalFlux
    (L a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) * L (N - 1) * a N

def covariantAsymmetricReporterDecomposition
    (L R a : ℕ → ℂ) (N : ℕ) : ℂ :=
  covariantAsymmetricReporterDiagonal L a N +
    covariantAsymmetricReporterConnection L a N +
    covariantAsymmetricReporterMismatch L R a N -
    covariantAsymmetricReporterTerminalFlux L a N

/-- Named-channel form of exact covariant inverse incidence. -/
theorem sum_range_covariantAsymmetricReporterCurrent
    (L R a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, covariantAsymmetricReporterCurrent L R a n) =
      covariantAsymmetricReporterDecomposition L R a N := by
  exact complex_sum_range_asymmetric_reporter L R a N

/-- A frozen reporter has no connection term. -/
theorem covariantAsymmetricReporterConnection_const
    (c : ℂ) (a : ℕ → ℂ) (N : ℕ) :
    covariantAsymmetricReporterConnection (fun _ => c) a N = 0 := by
  simp [covariantAsymmetricReporterConnection]

/-- Identical left/right reporters have no mismatch term. -/
theorem covariantAsymmetricReporterMismatch_self
    (L a : ℕ → ℂ) (N : ℕ) :
    covariantAsymmetricReporterMismatch L L a N = 0 := by
  simp [covariantAsymmetricReporterMismatch]

/-! ## Literal P-G84/P-G91/P-G92/P-G86 instantiation -/

/-- Full physical reporter, including P-G84 raw denominator mass. -/
def frankensteinPluckerPhysicalCoordinateReporter
    (z : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) : ℂ :=
  (Real.sqrt (gammaSewnCriticalAdjacentPrime_DenominatorTerm z) : ℂ) *
    frankensteinPluckerCoordinateReporter z s t i

def frankensteinPluckerLowerLeftReporter
    (e : ℕ) (s t : Fin 6) (n : ℕ) : ℂ :=
  frankensteinPluckerPhysicalCoordinateReporter (e, n) s t 0

def frankensteinPluckerLowerRightReporter
    (e : ℕ) (s t : Fin 6) (n : ℕ) : ℂ :=
  frankensteinPluckerPhysicalCoordinateReporter (e, n) s t 2

def frankensteinPluckerUpperLeftReporter
    (e : ℕ) (s t : Fin 6) (n : ℕ) : ℂ :=
  frankensteinPluckerPhysicalCoordinateReporter (e, n) s t 1

def frankensteinPluckerUpperRightReporter
    (e : ℕ) (s t : Fin 6) (n : ℕ) : ℂ :=
  frankensteinPluckerPhysicalCoordinateReporter (e, n) s t 3

/-- Lower left/right physical reporters are genuinely different.  Pair labels `0=(0,1)` and
`3=(1,2)` see the two packet ends with opposite strictly nonzero coefficients. -/
theorem frankensteinPluckerPhysicalCoordinateReporter_zero_ne_two
    (z : ℕ × ℕ) :
    frankensteinPluckerPhysicalCoordinateReporter z 0 3 0 ≠
      frankensteinPluckerPhysicalCoordinateReporter z 0 3 2 := by
  intro h
  simp [frankensteinPluckerPhysicalCoordinateReporter,
    frankensteinPluckerCoordinateReporter, fourRatePluckerCoordinateReporter,
    fourRatePluckerDispersionFeature, fourRateSelectedSumC,
    RHTower.fourRatePairLeft, RHTower.fourRatePairRight] at h
  have hD : 0 < Real.sqrt (gammaSewnCriticalAdjacentPrime_DenominatorTerm z) :=
    Real.sqrt_pos.2 (gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos z)
  have hP : 0 < Real.sqrt
      (frankensteinPluckerProbability z 0 * frankensteinPluckerProbability z 3) :=
    Real.sqrt_pos.2 (mul_pos
      (frankensteinPluckerProbability_pos z 0)
      (frankensteinPluckerProbability_pos z 3))
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hN0 : 0 < Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) 0) :=
    Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos _ _ _ _)
  have hN2 : 0 < Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) 2) :=
    Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos _ _ _ _)
  norm_cast at h
  nlinarith [div_pos hP h2, mul_pos (mul_pos hD (div_pos hP h2)) hN0,
    mul_pos (mul_pos hD (div_pos hP h2)) hN2]

/-- Upper left/right physical reporters are genuinely different.  Pair labels `0=(0,1)` and
`2=(0,3)` again produce opposite strictly nonzero coefficients. -/
theorem frankensteinPluckerPhysicalCoordinateReporter_one_ne_three
    (z : ℕ × ℕ) :
    frankensteinPluckerPhysicalCoordinateReporter z 0 2 1 ≠
      frankensteinPluckerPhysicalCoordinateReporter z 0 2 3 := by
  intro h
  simp [frankensteinPluckerPhysicalCoordinateReporter,
    frankensteinPluckerCoordinateReporter, fourRatePluckerCoordinateReporter,
    fourRatePluckerDispersionFeature, fourRateSelectedSumC,
    RHTower.fourRatePairLeft, RHTower.fourRatePairRight] at h
  have hD : 0 < Real.sqrt (gammaSewnCriticalAdjacentPrime_DenominatorTerm z) :=
    Real.sqrt_pos.2 (gammaSewnCriticalAdjacentPrime_DenominatorTerm_pos z)
  have hP : 0 < Real.sqrt
      (frankensteinPluckerProbability z 0 * frankensteinPluckerProbability z 2) :=
    Real.sqrt_pos.2 (mul_pos
      (frankensteinPluckerProbability_pos z 0)
      (frankensteinPluckerProbability_pos z 2))
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hN1 : 0 < Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) 1) :=
    Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos _ _ _ _)
  have hN3 : 0 < Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) 3) :=
    Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos _ _ _ _)
  norm_cast at h
  nlinarith [div_pos hP h2, mul_pos (mul_pos hD (div_pos hP h2)) hN1,
    mul_pos (mul_pos hD (div_pos hP h2)) hN3]

/-- Identity transport cannot glue the lower shared-prime reporters. -/
theorem frankensteinPluckerLowerLeftReporter_ne_right
    (e n : ℕ) :
    frankensteinPluckerLowerLeftReporter e 0 3 n ≠
      frankensteinPluckerLowerRightReporter e 0 3 n :=
  frankensteinPluckerPhysicalCoordinateReporter_zero_ne_two (e, n)

/-- Identity transport cannot glue the upper shared-prime reporters. -/
theorem frankensteinPluckerUpperLeftReporter_ne_right
    (e n : ℕ) :
    frankensteinPluckerUpperLeftReporter e 0 2 n ≠
      frankensteinPluckerUpperRightReporter e 0 2 n :=
  frankensteinPluckerPhysicalCoordinateReporter_one_ne_three (e, n)

/-- Every literal current term is exactly the sum of the two retained asymmetric depth channels.
No packet coefficient is frozen or discarded. -/
theorem frankensteinPluckerInverseIncidenceTerm_eq_two_asymmetricReporterCurrents
    (a : RHTower.DeningerHeightKothe) (e n : ℕ) (s t : Fin 6) :
    frankensteinPluckerInverseIncidenceTerm a (e, n) s t =
      covariantAsymmetricReporterCurrent
        (frankensteinPluckerLowerLeftReporter e s t)
        (frankensteinPluckerLowerRightReporter e s t)
        (RHTower.gammaValuationNthPrimeCoord e a) n +
      covariantAsymmetricReporterCurrent
        (frankensteinPluckerUpperLeftReporter e s t)
        (frankensteinPluckerUpperRightReporter e s t)
        (RHTower.gammaValuationNthPrimeCoord (e + 1) a) n := by
  rw [frankensteinPluckerInverseIncidenceTerm,
    frankensteinPluckerPacketFeature_eq_sum_coordinateReporter]
  simp [covariantAsymmetricReporterCurrent,
    frankensteinPluckerLowerLeftReporter, frankensteinPluckerLowerRightReporter,
    frankensteinPluckerUpperLeftReporter, frankensteinPluckerUpperRightReporter,
    frankensteinPluckerPhysicalCoordinateReporter, frankensteinPluckerSignedPacket,
    RHTower.gammaValuationNthPrimeCoord, RHTower.gammaValuationNthPrimeAxis,
    RHTower.gammaValuationAdjacentLowerAxis, RHTower.gammaValuationAdjacentUpperAxis,
    frankensteinPluckerLowerNextAxis, frankensteinPluckerUpperNextAxis,
    Fin.sum_univ_succ]
  ring

/-- Exact finite covariant decomposition of the actual coefficient-faithful Pluecker current.
The two connection and two mismatch channels are now explicit source-derived terms. -/
theorem sum_range_frankensteinPluckerInverseIncidenceTerm_eq_covariantDecompositions
    (a : RHTower.DeningerHeightKothe) (e N : ℕ) (s t : Fin 6) :
    (∑ n ∈ Finset.range N,
      frankensteinPluckerInverseIncidenceTerm a (e, n) s t) =
      covariantAsymmetricReporterDecomposition
        (frankensteinPluckerLowerLeftReporter e s t)
        (frankensteinPluckerLowerRightReporter e s t)
        (RHTower.gammaValuationNthPrimeCoord e a) N +
      covariantAsymmetricReporterDecomposition
        (frankensteinPluckerUpperLeftReporter e s t)
        (frankensteinPluckerUpperRightReporter e s t)
        (RHTower.gammaValuationNthPrimeCoord (e + 1) a) N := by
  simp_rw [frankensteinPluckerInverseIncidenceTerm_eq_two_asymmetricReporterCurrents]
  rw [Finset.sum_add_distrib,
    sum_range_covariantAsymmetricReporterCurrent,
    sum_range_covariantAsymmetricReporterCurrent]

end RHTower.HedenmalmThetaSource
