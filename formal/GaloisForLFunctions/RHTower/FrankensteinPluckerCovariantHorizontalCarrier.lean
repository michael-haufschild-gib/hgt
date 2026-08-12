import GaloisForLFunctions.RHTower.FrankensteinPluckerSharedPrimeFrameTransport

/-!
# Covariant source-horizontal carrier from shared-prime Pluecker transport

Fixed-label physical reporters do not telescope across adjacent-prime packets.  This module applies
the canonical source-derived frame transport before inverse incidence.  Iterated pair-label swap
makes transported right endpoint of edge `n` exactly the left endpoint of edge `n+1`, at both
retained divisor depths.

The resulting finite current telescopes to a prime-labelled diagonal carrier plus terminal flux.
Uniform literal reporter bounds and Deninger Koethe index-weight summability make edge and diagonal
series absolutely summable and force terminal flux to zero.  Hence each infinite covariant
horizontal carrier equals its exact prime-labelled diagonal source sum.

This constructs the missing source-zero-to-horizontal-carrier bridge.  It does not identify that
carrier with completed Xi divisor transport, force reflected annihilation, or prove RH.
-/

open scoped BigOperators
open Filter Topology
noncomputable section
namespace RHTower.HedenmalmThetaSource

def iteratedFourRateSelectedPairSwap (n : ℕ) (s : Fin 6) : Fin 6 :=
  (fourRateSelectedPairSwap^[n]) s

theorem iteratedFourRateSelectedPairSwap_succ (n : ℕ) (s : Fin 6) :
    iteratedFourRateSelectedPairSwap (n + 1) s =
      fourRateSelectedPairSwap (iteratedFourRateSelectedPairSwap n s) := by
  rw [iteratedFourRateSelectedPairSwap, iteratedFourRateSelectedPairSwap,
    Function.iterate_succ_apply']

def frankensteinPluckerLowerVertexReporter
    (e : ℕ) (s t : Fin 6) (n : ℕ) : ℂ :=
  frankensteinPluckerLowerLeftReporter e
    (iteratedFourRateSelectedPairSwap n s)
    (iteratedFourRateSelectedPairSwap n t) n

def frankensteinPluckerUpperVertexReporter
    (e : ℕ) (s t : Fin 6) (n : ℕ) : ℂ :=
  frankensteinPluckerUpperLeftReporter e
    (iteratedFourRateSelectedPairSwap n s)
    (iteratedFourRateSelectedPairSwap n t) n

def frankensteinPluckerLowerEdgeTransportCoefficient
    (e : ℕ) (s t : Fin 6) (n : ℕ) : ℝ :=
  frankensteinPluckerReporterTransportCoefficient (e, n) (e, n + 1)
    (iteratedFourRateSelectedPairSwap n s)
    (iteratedFourRateSelectedPairSwap n t) 2

def frankensteinPluckerUpperEdgeTransportCoefficient
    (e : ℕ) (s t : Fin 6) (n : ℕ) : ℝ :=
  frankensteinPluckerReporterTransportCoefficient (e, n) (e, n + 1)
    (iteratedFourRateSelectedPairSwap n s)
    (iteratedFourRateSelectedPairSwap n t) 3

theorem frankensteinPluckerLowerEdge_transport_eq_nextVertex
    (e : ℕ) (s t : Fin 6) (n : ℕ) :
    (frankensteinPluckerLowerEdgeTransportCoefficient e s t n : ℂ) *
        frankensteinPluckerLowerRightReporter e
          (iteratedFourRateSelectedPairSwap n s)
          (iteratedFourRateSelectedPairSwap n t) n =
      frankensteinPluckerLowerVertexReporter e s t (n + 1) := by
  rw [frankensteinPluckerLowerVertexReporter,
    iteratedFourRateSelectedPairSwap_succ,
    iteratedFourRateSelectedPairSwap_succ,
    frankensteinPluckerLowerEdgeTransportCoefficient]
  exact (frankensteinPluckerLowerSharedPrimeReporter_transport e n
    (iteratedFourRateSelectedPairSwap n s)
    (iteratedFourRateSelectedPairSwap n t)).symm

theorem frankensteinPluckerUpperEdge_transport_eq_nextVertex
    (e : ℕ) (s t : Fin 6) (n : ℕ) :
    (frankensteinPluckerUpperEdgeTransportCoefficient e s t n : ℂ) *
        frankensteinPluckerUpperRightReporter e
          (iteratedFourRateSelectedPairSwap n s)
          (iteratedFourRateSelectedPairSwap n t) n =
      frankensteinPluckerUpperVertexReporter e s t (n + 1) := by
  rw [frankensteinPluckerUpperVertexReporter,
    iteratedFourRateSelectedPairSwap_succ,
    iteratedFourRateSelectedPairSwap_succ,
    frankensteinPluckerUpperEdgeTransportCoefficient]
  exact (frankensteinPluckerUpperSharedPrimeReporter_transport e n
    (iteratedFourRateSelectedPairSwap n s)
    (iteratedFourRateSelectedPairSwap n t)).symm

def frankensteinPluckerLowerCovariantEdgeCurrent
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) *
    (frankensteinPluckerLowerVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord e a n -
      (frankensteinPluckerLowerEdgeTransportCoefficient e s t n : ℂ) *
        frankensteinPluckerLowerRightReporter e
          (iteratedFourRateSelectedPairSwap n s)
          (iteratedFourRateSelectedPairSwap n t) n *
        RHTower.gammaValuationNthPrimeCoord e a (n + 1))

def frankensteinPluckerUpperCovariantEdgeCurrent
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) *
    (frankensteinPluckerUpperVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord (e + 1) a n -
      (frankensteinPluckerUpperEdgeTransportCoefficient e s t n : ℂ) *
        frankensteinPluckerUpperRightReporter e
          (iteratedFourRateSelectedPairSwap n s)
          (iteratedFourRateSelectedPairSwap n t) n *
        RHTower.gammaValuationNthPrimeCoord (e + 1) a (n + 1))

theorem frankensteinPluckerLowerCovariantEdgeCurrent_eq_vertexIncidence
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) (n : ℕ) :
    frankensteinPluckerLowerCovariantEdgeCurrent a e s t n =
      ((n + 1 : ℕ) : ℂ) *
        (frankensteinPluckerLowerVertexReporter e s t n *
            RHTower.gammaValuationNthPrimeCoord e a n -
          frankensteinPluckerLowerVertexReporter e s t (n + 1) *
            RHTower.gammaValuationNthPrimeCoord e a (n + 1)) := by
  rw [frankensteinPluckerLowerCovariantEdgeCurrent,
    frankensteinPluckerLowerEdge_transport_eq_nextVertex]

theorem frankensteinPluckerUpperCovariantEdgeCurrent_eq_vertexIncidence
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) (n : ℕ) :
    frankensteinPluckerUpperCovariantEdgeCurrent a e s t n =
      ((n + 1 : ℕ) : ℂ) *
        (frankensteinPluckerUpperVertexReporter e s t n *
            RHTower.gammaValuationNthPrimeCoord (e + 1) a n -
          frankensteinPluckerUpperVertexReporter e s t (n + 1) *
            RHTower.gammaValuationNthPrimeCoord (e + 1) a (n + 1)) := by
  rw [frankensteinPluckerUpperCovariantEdgeCurrent,
    frankensteinPluckerUpperEdge_transport_eq_nextVertex]

theorem complex_sum_range_weighted_vertex_incidence
    (b : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ((n + 1 : ℕ) : ℂ) * (b n - b (n + 1))) =
      (∑ n ∈ Finset.range N, b n) - (N : ℂ) * b N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      push_cast
      ring

theorem sum_range_frankensteinPluckerLowerCovariantEdgeCurrent
    (a : RHTower.DeningerHeightKothe) (e N : ℕ) (s t : Fin 6) :
    (∑ n ∈ Finset.range N,
      frankensteinPluckerLowerCovariantEdgeCurrent a e s t n) =
      (∑ n ∈ Finset.range N,
        frankensteinPluckerLowerVertexReporter e s t n *
          RHTower.gammaValuationNthPrimeCoord e a n) -
      (N : ℂ) * frankensteinPluckerLowerVertexReporter e s t N *
        RHTower.gammaValuationNthPrimeCoord e a N := by
  simp_rw [frankensteinPluckerLowerCovariantEdgeCurrent_eq_vertexIncidence]
  rw [complex_sum_range_weighted_vertex_incidence]
  ring

theorem sum_range_frankensteinPluckerUpperCovariantEdgeCurrent
    (a : RHTower.DeningerHeightKothe) (e N : ℕ) (s t : Fin 6) :
    (∑ n ∈ Finset.range N,
      frankensteinPluckerUpperCovariantEdgeCurrent a e s t n) =
      (∑ n ∈ Finset.range N,
        frankensteinPluckerUpperVertexReporter e s t n *
          RHTower.gammaValuationNthPrimeCoord (e + 1) a n) -
      (N : ℂ) * frankensteinPluckerUpperVertexReporter e s t N *
        RHTower.gammaValuationNthPrimeCoord (e + 1) a N := by
  simp_rw [frankensteinPluckerUpperCovariantEdgeCurrent_eq_vertexIncidence]
  rw [complex_sum_range_weighted_vertex_incidence]
  ring

def frankensteinPluckerReporterUniformBound : ℝ :=
  2 * Real.sqrt gammaSewnCriticalAdjacentPrime_CofinalDenominator *
    (Real.log 2)⁻¹

theorem frankensteinPluckerReporterUniformBound_nonneg :
    0 ≤ frankensteinPluckerReporterUniformBound := by
  unfold frankensteinPluckerReporterUniformBound
  positivity

theorem norm_fourRatePluckerCoordinateReporter_le_two
    (weight : Fin 6 → ℝ) (hweight : ∀ s, 0 ≤ weight s)
    (hsum : ∑ s, weight s = 1) (s t : Fin 6) (i : Fin 4) :
    ‖fourRatePluckerCoordinateReporter weight s t i‖ ≤ 2 := by
  have h := fourRatePluckerDispersionFeature_norm_le weight hweight hsum
    (fun j : Fin 4 => if j = i then 1 else 0) s t
  rw [fourRatePluckerCoordinateReporter]
  calc
    _ ≤ 2 * ∑ j : Fin 4, ‖(if j = i then (1 : ℂ) else 0)‖ := h
    _ = 2 := by
      classical
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [hji]
      · simp

theorem norm_frankensteinPluckerPhysicalCoordinateReporter_le_uniform
    (z : ℕ × ℕ) (s t : Fin 6) (i : Fin 4) :
    ‖frankensteinPluckerPhysicalCoordinateReporter z s t i‖ ≤
      frankensteinPluckerReporterUniformBound := by
  have hcoord := norm_fourRatePluckerCoordinateReporter_le_two
    (frankensteinPluckerProbability z)
    (fun u => (frankensteinPluckerProbability_pos z u).le)
    (sum_frankensteinPluckerProbability z) s t i
  have hD := sqrt_gammaSewnCriticalAdjacentPrime_DenominatorTerm_le_cofinal z
  have hnode := sqrt_frankensteinPluckerNode_le_logTwoInv z i
  have hlog : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  rw [frankensteinPluckerPhysicalCoordinateReporter,
    frankensteinPluckerCoordinateReporter, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  unfold frankensteinPluckerReporterUniformBound
  calc
    Real.sqrt (gammaSewnCriticalAdjacentPrime_DenominatorTerm z) *
        (‖fourRatePluckerCoordinateReporter (frankensteinPluckerProbability z) s t i‖ *
          Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
            (gammaSewnCriticalAdjacentPrime_lower z.2)
            (gammaSewnCriticalAdjacentPrime_upper z.2) i)) ≤
      Real.sqrt gammaSewnCriticalAdjacentPrime_CofinalDenominator *
        (2 * (Real.log 2)⁻¹) := by
          gcongr
    _ = 2 * Real.sqrt gammaSewnCriticalAdjacentPrime_CofinalDenominator *
        (Real.log 2)⁻¹ := by ring

theorem norm_frankensteinPluckerLowerVertexReporter_le_uniform
    (e : ℕ) (s t : Fin 6) (n : ℕ) :
    ‖frankensteinPluckerLowerVertexReporter e s t n‖ ≤
      frankensteinPluckerReporterUniformBound := by
  exact norm_frankensteinPluckerPhysicalCoordinateReporter_le_uniform
    (e, n) (iteratedFourRateSelectedPairSwap n s)
      (iteratedFourRateSelectedPairSwap n t) 0

theorem norm_frankensteinPluckerUpperVertexReporter_le_uniform
    (e : ℕ) (s t : Fin 6) (n : ℕ) :
    ‖frankensteinPluckerUpperVertexReporter e s t n‖ ≤
      frankensteinPluckerReporterUniformBound := by
  exact norm_frankensteinPluckerPhysicalCoordinateReporter_le_uniform
    (e, n) (iteratedFourRateSelectedPairSwap n s)
      (iteratedFourRateSelectedPairSwap n t) 1

theorem summable_frankensteinPluckerLowerVertexCarrier
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    Summable (fun n : ℕ =>
      frankensteinPluckerLowerVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord e a n) := by
  have hbase := RHTower.summable_gammaValuationNthPrimeCoord_indexWeight e a
  have hmajor : Summable (fun n : ℕ =>
      frankensteinPluckerReporterUniformBound *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord e a n‖)) :=
    hbase.mul_left frankensteinPluckerReporterUniformBound
  refine Summable.of_norm_bounded hmajor fun n => ?_
  rw [norm_mul]
  calc
    ‖frankensteinPluckerLowerVertexReporter e s t n‖ *
        ‖RHTower.gammaValuationNthPrimeCoord e a n‖ ≤
      frankensteinPluckerReporterUniformBound *
        ‖RHTower.gammaValuationNthPrimeCoord e a n‖ := by
          gcongr
          exact norm_frankensteinPluckerLowerVertexReporter_le_uniform e s t n
    _ ≤ frankensteinPluckerReporterUniformBound *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord e a n‖) := by
          apply mul_le_mul_of_nonneg_left _
            frankensteinPluckerReporterUniformBound_nonneg
          nlinarith [norm_nonneg (RHTower.gammaValuationNthPrimeCoord e a n)]

theorem summable_frankensteinPluckerUpperVertexCarrier
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    Summable (fun n : ℕ =>
      frankensteinPluckerUpperVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord (e + 1) a n) := by
  have hbase := RHTower.summable_gammaValuationNthPrimeCoord_indexWeight (e + 1) a
  have hmajor : Summable (fun n : ℕ =>
      frankensteinPluckerReporterUniformBound *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a n‖)) :=
    hbase.mul_left frankensteinPluckerReporterUniformBound
  refine Summable.of_norm_bounded hmajor fun n => ?_
  rw [norm_mul]
  calc
    ‖frankensteinPluckerUpperVertexReporter e s t n‖ *
        ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a n‖ ≤
      frankensteinPluckerReporterUniformBound *
        ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a n‖ := by
          gcongr
          exact norm_frankensteinPluckerUpperVertexReporter_le_uniform e s t n
    _ ≤ frankensteinPluckerReporterUniformBound *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a n‖) := by
          apply mul_le_mul_of_nonneg_left _
            frankensteinPluckerReporterUniformBound_nonneg
          nlinarith [norm_nonneg (RHTower.gammaValuationNthPrimeCoord (e + 1) a n)]

theorem tendsto_frankensteinPluckerLowerVertexCarrier_terminalFlux_zero
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    Tendsto (fun N : ℕ =>
      (N : ℂ) * frankensteinPluckerLowerVertexReporter e s t N *
        RHTower.gammaValuationNthPrimeCoord e a N) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hzero := (RHTower.summable_gammaValuationNthPrimeCoord_indexWeight e a).tendsto_atTop_zero
  have hzero' : Tendsto (fun N : ℕ =>
      frankensteinPluckerReporterUniformBound *
        ((N + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord e a N‖)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hzero)
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _)
    (Eventually.of_forall fun N => ?_) hzero'
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hN : (N : ℝ) ≤ (N + 1 : ℝ) := by norm_num
  calc
    (N : ℝ) * ‖frankensteinPluckerLowerVertexReporter e s t N‖ *
        ‖RHTower.gammaValuationNthPrimeCoord e a N‖ ≤
      (N : ℝ) * frankensteinPluckerReporterUniformBound *
        ‖RHTower.gammaValuationNthPrimeCoord e a N‖ := by
          gcongr
          exact norm_frankensteinPluckerLowerVertexReporter_le_uniform e s t N
    _ ≤ frankensteinPluckerReporterUniformBound *
        ((N + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord e a N‖) := by
          nlinarith [frankensteinPluckerReporterUniformBound_nonneg,
            norm_nonneg (RHTower.gammaValuationNthPrimeCoord e a N)]

theorem tendsto_frankensteinPluckerUpperVertexCarrier_terminalFlux_zero
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    Tendsto (fun N : ℕ =>
      (N : ℂ) * frankensteinPluckerUpperVertexReporter e s t N *
        RHTower.gammaValuationNthPrimeCoord (e + 1) a N) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hzero :=
    (RHTower.summable_gammaValuationNthPrimeCoord_indexWeight (e + 1) a).tendsto_atTop_zero
  have hzero' : Tendsto (fun N : ℕ =>
      frankensteinPluckerReporterUniformBound *
        ((N + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a N‖)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hzero)
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _)
    (Eventually.of_forall fun N => ?_) hzero'
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hN : (N : ℝ) ≤ (N + 1 : ℝ) := by norm_num
  calc
    (N : ℝ) * ‖frankensteinPluckerUpperVertexReporter e s t N‖ *
        ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a N‖ ≤
      (N : ℝ) * frankensteinPluckerReporterUniformBound *
        ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a N‖ := by
          gcongr
          exact norm_frankensteinPluckerUpperVertexReporter_le_uniform e s t N
    _ ≤ frankensteinPluckerReporterUniformBound *
        ((N + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a N‖) := by
          nlinarith [frankensteinPluckerReporterUniformBound_nonneg,
            norm_nonneg (RHTower.gammaValuationNthPrimeCoord (e + 1) a N)]

theorem summable_complex_weighted_vertex_incidence
    (b : ℕ → ℂ) (hweight : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖b n‖)) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * (b n - b (n + 1))) := by
  let w : ℕ → ℝ := fun n => (n + 1 : ℝ) * ‖b n‖
  have hw : Summable w := hweight
  have hshift : Summable (fun n : ℕ => w (n + 1)) :=
    hw.comp_injective Nat.succ_injective
  have hmajor : Summable (fun n : ℕ => w n + w (n + 1)) := hw.add hshift
  refine Summable.of_norm_bounded hmajor fun n => ?_
  rw [norm_mul, Complex.norm_natCast]
  push_cast
  calc
    (n + 1 : ℝ) * ‖b n - b (n + 1)‖ ≤
      (n + 1 : ℝ) * (‖b n‖ + ‖b (n + 1)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ w n + w (n + 1) := by
      dsimp [w]
      rw [mul_add]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))

theorem summable_indexWeight_frankensteinPluckerLowerVertexCarrier
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    Summable (fun n : ℕ => (n + 1 : ℝ) *
      ‖frankensteinPluckerLowerVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord e a n‖) := by
  have hbase := RHTower.summable_gammaValuationNthPrimeCoord_indexWeight e a
  have hmajor : Summable (fun n : ℕ =>
      frankensteinPluckerReporterUniformBound *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord e a n‖)) :=
    hbase.mul_left frankensteinPluckerReporterUniformBound
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (fun n => ?_) hmajor
  rw [norm_mul]
  calc
    (n + 1 : ℝ) *
        (‖frankensteinPluckerLowerVertexReporter e s t n‖ *
          ‖RHTower.gammaValuationNthPrimeCoord e a n‖) =
      ‖frankensteinPluckerLowerVertexReporter e s t n‖ *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord e a n‖) := by ring
    _ ≤ frankensteinPluckerReporterUniformBound *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord e a n‖) :=
      mul_le_mul_of_nonneg_right
        (norm_frankensteinPluckerLowerVertexReporter_le_uniform e s t n)
        (mul_nonneg (by positivity) (norm_nonneg _))

theorem summable_indexWeight_frankensteinPluckerUpperVertexCarrier
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    Summable (fun n : ℕ => (n + 1 : ℝ) *
      ‖frankensteinPluckerUpperVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord (e + 1) a n‖) := by
  have hbase := RHTower.summable_gammaValuationNthPrimeCoord_indexWeight (e + 1) a
  have hmajor : Summable (fun n : ℕ =>
      frankensteinPluckerReporterUniformBound *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a n‖)) :=
    hbase.mul_left frankensteinPluckerReporterUniformBound
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (fun n => ?_) hmajor
  rw [norm_mul]
  calc
    (n + 1 : ℝ) *
        (‖frankensteinPluckerUpperVertexReporter e s t n‖ *
          ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a n‖) =
      ‖frankensteinPluckerUpperVertexReporter e s t n‖ *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a n‖) := by ring
    _ ≤ frankensteinPluckerReporterUniformBound *
        ((n + 1 : ℝ) * ‖RHTower.gammaValuationNthPrimeCoord (e + 1) a n‖) :=
      mul_le_mul_of_nonneg_right
        (norm_frankensteinPluckerUpperVertexReporter_le_uniform e s t n)
        (mul_nonneg (by positivity) (norm_nonneg _))

theorem summable_frankensteinPluckerLowerCovariantEdgeCurrent
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    Summable (frankensteinPluckerLowerCovariantEdgeCurrent a e s t) := by
  let b : ℕ → ℂ := fun n => frankensteinPluckerLowerVertexReporter e s t n *
    RHTower.gammaValuationNthPrimeCoord e a n
  have h := summable_complex_weighted_vertex_incidence b
    (summable_indexWeight_frankensteinPluckerLowerVertexCarrier a e s t)
  exact h.congr fun n => by
    rw [frankensteinPluckerLowerCovariantEdgeCurrent_eq_vertexIncidence]

theorem summable_frankensteinPluckerUpperCovariantEdgeCurrent
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    Summable (frankensteinPluckerUpperCovariantEdgeCurrent a e s t) := by
  let b : ℕ → ℂ := fun n => frankensteinPluckerUpperVertexReporter e s t n *
    RHTower.gammaValuationNthPrimeCoord (e + 1) a n
  have h := summable_complex_weighted_vertex_incidence b
    (summable_indexWeight_frankensteinPluckerUpperVertexCarrier a e s t)
  exact h.congr fun n => by
    rw [frankensteinPluckerUpperCovariantEdgeCurrent_eq_vertexIncidence]

def frankensteinPluckerLowerCovariantHorizontalCarrier
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) : ℂ :=
  ∑' n : ℕ, frankensteinPluckerLowerCovariantEdgeCurrent a e s t n

def frankensteinPluckerUpperCovariantHorizontalCarrier
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) : ℂ :=
  ∑' n : ℕ, frankensteinPluckerUpperCovariantEdgeCurrent a e s t n

theorem frankensteinPluckerLowerCovariantHorizontalCarrier_eq_diagonal
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    frankensteinPluckerLowerCovariantHorizontalCarrier a e s t =
      ∑' n : ℕ, frankensteinPluckerLowerVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord e a n := by
  have hedge := summable_frankensteinPluckerLowerCovariantEdgeCurrent a e s t
  have hdiag := summable_frankensteinPluckerLowerVertexCarrier a e s t
  have hedgeLimit := (hedge.hasSum_iff_tendsto_nat).mp hedge.hasSum
  have hdiagLimit := (hdiag.hasSum_iff_tendsto_nat).mp hdiag.hasSum
  have hboundary :=
    tendsto_frankensteinPluckerLowerVertexCarrier_terminalFlux_zero a e s t
  have hlimit : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N,
        frankensteinPluckerLowerCovariantEdgeCurrent a e s t n) atTop
      (𝓝 (∑' n : ℕ, frankensteinPluckerLowerVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord e a n)) := by
    have hsub := hdiagLimit.sub hboundary
    simpa only [sum_range_frankensteinPluckerLowerCovariantEdgeCurrent, sub_zero] using hsub
  exact tendsto_nhds_unique hedgeLimit hlimit

theorem frankensteinPluckerUpperCovariantHorizontalCarrier_eq_diagonal
    (a : RHTower.DeningerHeightKothe) (e : ℕ) (s t : Fin 6) :
    frankensteinPluckerUpperCovariantHorizontalCarrier a e s t =
      ∑' n : ℕ, frankensteinPluckerUpperVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord (e + 1) a n := by
  have hedge := summable_frankensteinPluckerUpperCovariantEdgeCurrent a e s t
  have hdiag := summable_frankensteinPluckerUpperVertexCarrier a e s t
  have hedgeLimit := (hedge.hasSum_iff_tendsto_nat).mp hedge.hasSum
  have hdiagLimit := (hdiag.hasSum_iff_tendsto_nat).mp hdiag.hasSum
  have hboundary :=
    tendsto_frankensteinPluckerUpperVertexCarrier_terminalFlux_zero a e s t
  have hlimit : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N,
        frankensteinPluckerUpperCovariantEdgeCurrent a e s t n) atTop
      (𝓝 (∑' n : ℕ, frankensteinPluckerUpperVertexReporter e s t n *
        RHTower.gammaValuationNthPrimeCoord (e + 1) a n)) := by
    have hsub := hdiagLimit.sub hboundary
    simpa only [sum_range_frankensteinPluckerUpperCovariantEdgeCurrent, sub_zero] using hsub
  exact tendsto_nhds_unique hedgeLimit hlimit

end RHTower.HedenmalmThetaSource
