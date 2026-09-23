import GaloisForLFunctions.RHTower.GammaJordanXiTangentResponseGap
import GaloisForLFunctions.RHTower.GammaSewnFourRatePluckerJordanTransition

/-!
# Four-rate Gamma/Jordan father--detail transfer

The four-rate boundary Fisher mass is a diagonal quantity, whereas the Gamma/Xi response gap is
pairwise.  The exact relation between them is not domination by a graph Laplacian.  Each normalized
boundary packet has a canonical father--detail decomposition for both the joined Gamma response
and the actual all-depth Xi tangent response.  The nonnegative response gap transfers exactly the
same mass from Xi detail to Gamma father while preserving the total Fisher mass.

On a four-depth cell supported at one prime, every response-gap term vanishes but the Fisher mass
is strictly positive.  In fact the entire mass is father mass for both responses.  Thus no
unpointed response-gap energy can control the signed Jordan boundary mass; a correct crossing must
retain the rooted/common-mode channel identified by HTGeometry.
-/

open scoped BigOperators
open GaloisForLFunctions.HilbertMetric

namespace RHTower

noncomputable section

/-! ## Prime responses and Fisher amplitudes -/

/-- The joined variance-biased Gamma response on two prime tangent states. -/
def gammaJordanXiPrimeJoinedResponse (p q : Nat.Primes) : ℝ :=
  gammaJordanResponseFromBase (gammaXiFisherBaseCorrelation p q)

theorem gammaJordanXiPrimeJoinedResponse_self (p : Nat.Primes) :
    gammaJordanXiPrimeJoinedResponse p p = 1 := by
  rw [gammaJordanXiPrimeJoinedResponse,
    (gammaXiFisherBaseCorrelation_eq_one_iff p p).2 rfl]
  norm_num [gammaJordanResponseFromBase]

theorem gammaJordanXiPrimeJoinedResponse_nonneg (p q : Nat.Primes) :
    0 ≤ gammaJordanXiPrimeJoinedResponse p q := by
  let k := gammaXiFisherBaseCorrelation p q
  have hk0 : 0 < k := gammaXiFisherBaseCorrelation_pos p q
  have hkLoc : 3 / 4 < k ^ (2 : ℕ) :=
    gammaXiFisherBaseCorrelation_sq_gt_three_fourths p q
  unfold gammaJordanXiPrimeJoinedResponse gammaJordanResponseFromBase
  change 0 ≤ Real.sqrt k * (3 * k ^ (2 : ℕ) - 1) / 2
  exact div_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (by nlinarith)) (by norm_num)

theorem gammaJordanXiPrimeJoinedResponse_le_one (p q : Nat.Primes) :
    gammaJordanXiPrimeJoinedResponse p q ≤ 1 := by
  let k := gammaXiFisherBaseCorrelation p q
  have hk0 : 0 < k := gammaXiFisherBaseCorrelation_pos p q
  have hk1 : k ≤ 1 := gammaXiFisherBaseCorrelation_le_one p q
  have hkLoc : 3 / 4 < k ^ (2 : ℕ) :=
    gammaXiFisherBaseCorrelation_sq_gt_three_fourths p q
  have hsqrt0 : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt k ≤ 1 := Real.sqrt_le_one.mpr hk1
  have hksq1 : k ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr hk1)]
  have hfactor0 : 0 ≤ (3 * k ^ (2 : ℕ) - 1) / 2 := by nlinarith
  have hfactor1 : (3 * k ^ (2 : ℕ) - 1) / 2 ≤ 1 := by nlinarith
  unfold gammaJordanXiPrimeJoinedResponse gammaJordanResponseFromBase
  change Real.sqrt k * (3 * k ^ (2 : ℕ) - 1) / 2 ≤ 1
  nlinarith [mul_nonneg hsqrt0 (sub_nonneg.mpr hfactor1)]

theorem gammaSewnXiShiftEndpointUnitTangentKernel_nonneg (p q : Nat.Primes) :
    0 ≤ gammaSewnXiShiftEndpointUnitTangentKernel p q := by
  let k := gammaXiFisherBaseCorrelation p q
  have hk0 : 0 < k := gammaXiFisherBaseCorrelation_pos p q
  have hkLoc : 3 / 4 < k ^ (2 : ℕ) :=
    gammaXiFisherBaseCorrelation_sq_gt_three_fourths p q
  rw [gammaSewnXiShiftEndpointUnitTangentKernel_eq_responseFromBase]
  unfold xiShiftTangentResponseFromBase
  exact mul_nonneg hk0.le (by nlinarith)

/-- Square root of the prime-only Gamma-sewn Fisher clock. -/
def gammaSewnBoundaryFisherAmplitude (p : Nat.Primes) : ℝ :=
  Real.sqrt (gammaSewnMobiusApertureBoundaryFisherClock p)

theorem gammaSewnBoundaryFisherAmplitude_nonneg (p : Nat.Primes) :
    0 ≤ gammaSewnBoundaryFisherAmplitude p :=
  Real.sqrt_nonneg _

theorem gammaSewnBoundaryFisherAmplitude_pos (p : Nat.Primes) :
    0 < gammaSewnBoundaryFisherAmplitude p := by
  rw [gammaSewnBoundaryFisherAmplitude, Real.sqrt_pos]
  exact gammaSewnMobiusApertureBoundaryFisherClock_pos p

theorem gammaSewnBoundaryFisherAmplitude_sq (p : Nat.Primes) :
    gammaSewnBoundaryFisherAmplitude p ^ (2 : ℕ) =
      gammaSewnMobiusApertureBoundaryFisherClock p := by
  rw [gammaSewnBoundaryFisherAmplitude,
    Real.sq_sqrt (gammaSewnMobiusApertureBoundaryFisherClock_pos p).le]

/-! ## Canonical complementary-pair response geometry -/

/-- Correlation of two complementary boundary pairs.  The two complementary endpoints are placed
in their canonical increasing slots, so this is a two-channel response rather than a scalar
collapse of the pair. -/
def gammaSewnFourRateComplementaryResponseKernel
    (response : Nat.Primes → Nat.Primes → ℝ)
    (cell : Fin 4 → Nat.Primes × ℕ) (s t : Fin 6) : ℝ :=
  gammaSewnBoundaryFisherAmplitude
      (cell (fourRatePairComplementLeft s)).1 *
    gammaSewnBoundaryFisherAmplitude
      (cell (fourRatePairComplementLeft t)).1 *
    response (cell (fourRatePairComplementLeft s)).1
      (cell (fourRatePairComplementLeft t)).1 +
  gammaSewnBoundaryFisherAmplitude
      (cell (fourRatePairComplementRight s)).1 *
    gammaSewnBoundaryFisherAmplitude
      (cell (fourRatePairComplementRight t)).1 *
    response (cell (fourRatePairComplementRight s)).1
      (cell (fourRatePairComplementRight t)).1

theorem gammaSewnFourRateComplementaryResponseKernel_self
    (response : Nat.Primes → Nat.Primes → ℝ)
    (hself : ∀ p, response p p = 1)
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) :
    gammaSewnFourRateComplementaryResponseKernel response cell s s =
      gammaSewnFourRateComplementaryFisher cell s := by
  unfold gammaSewnFourRateComplementaryResponseKernel
    gammaSewnFourRateComplementaryFisher fourRateComplementarySum
  rw [hself, hself]
  have hleft := gammaSewnBoundaryFisherAmplitude_sq
    (cell (fourRatePairComplementLeft s)).1
  have hright := gammaSewnBoundaryFisherAmplitude_sq
    (cell (fourRatePairComplementRight s)).1
  nlinarith

/-- Correlated father energy of a normalized packet of complementary pairs. -/
def gammaSewnFourRateComplementaryResponseFatherEnergy
    (weight : Fin 6 → ℝ) (response : Nat.Primes → Nat.Primes → ℝ)
    (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  ∑ s, ∑ t, weight s * weight t *
    gammaSewnFourRateComplementaryResponseKernel response cell s t

/-- Pairwise detail energy complementary to the response father. -/
def gammaSewnFourRateComplementaryResponseDetailEnergy
    (weight : Fin 6 → ℝ) (response : Nat.Primes → Nat.Primes → ℝ)
    (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, ∑ t, weight s * weight t *
    (gammaSewnFourRateComplementaryFisher cell s +
      gammaSewnFourRateComplementaryFisher cell t -
      2 * gammaSewnFourRateComplementaryResponseKernel response cell s t)

private theorem finite_weighted_diagonal_eq_detail_add_father
    {β : Type*} [Fintype β] (weight diagonal : β → ℝ)
    (kernel : β → β → ℝ) (hweight : ∑ b, weight b = 1) :
    (∑ b, weight b * diagonal b) =
      (1 / 2 : ℝ) * ∑ b, ∑ c, weight b * weight c *
        (diagonal b + diagonal c - 2 * kernel b c) +
      ∑ b, ∑ c, weight b * weight c * kernel b c := by
  let mean := ∑ b, weight b * diagonal b
  let father := ∑ b, ∑ c, weight b * weight c * kernel b c
  have hleft :
      (∑ b, ∑ c, weight b * weight c * diagonal b) = mean := by
    calc
      (∑ b, ∑ c, weight b * weight c * diagonal b) =
          ∑ b, (weight b * diagonal b) * (∑ c, weight c) := by
            apply Finset.sum_congr rfl
            intro b _hb
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _hc
            ring
      _ = mean := by simp [mean, hweight]
  have hright :
      (∑ b, ∑ c, weight b * weight c * diagonal c) = mean := by
    calc
      (∑ b, ∑ c, weight b * weight c * diagonal c) =
          ∑ c, ∑ b, weight c * weight b * diagonal c := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _hc
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = mean := hleft
  have hexpand :
      (∑ b, ∑ c, weight b * weight c *
        (diagonal b + diagonal c - 2 * kernel b c)) =
      (∑ b, ∑ c, weight b * weight c * diagonal b) +
        (∑ b, ∑ c, weight b * weight c * diagonal c) - 2 * father := by
    have hpoint (b c : β) :
        weight b * weight c *
            (diagonal b + diagonal c - 2 * kernel b c) =
          weight b * weight c * diagonal b +
            weight b * weight c * diagonal c -
              2 * (weight b * weight c * kernel b c) := by ring
    simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rfl
  change mean = _
  rw [hexpand, hleft, hright]
  change mean = (1 / 2 : ℝ) * (mean + mean - 2 * father) + father
  ring

/-- **Father--detail conservation.**  Any normalized complementary-pair packet splits its total
Fisher mass exactly into response detail and correlated father mass. -/
theorem gammaSewnFourRateComplementaryFisherMean_eq_detail_add_father
    (weight : Fin 6 → ℝ) (response : Nat.Primes → Nat.Primes → ℝ)
    (cell : Fin 4 → Nat.Primes × ℕ) (hweight : ∑ s, weight s = 1) :
    complementaryFisherMean weight
        (gammaSewnFourRateComplementaryFisher cell) =
      gammaSewnFourRateComplementaryResponseDetailEnergy weight response cell +
        gammaSewnFourRateComplementaryResponseFatherEnergy weight response cell := by
  simpa [complementaryFisherMean,
    gammaSewnFourRateComplementaryResponseDetailEnergy,
    gammaSewnFourRateComplementaryResponseFatherEnergy] using
    finite_weighted_diagonal_eq_detail_add_father weight
      (gammaSewnFourRateComplementaryFisher cell)
      (gammaSewnFourRateComplementaryResponseKernel response cell) hweight

private theorem fisherAmplitude_response_defect_nonneg
    (p q : Nat.Primes) {r : ℝ} (hr : r ≤ 1) :
    0 ≤ gammaSewnMobiusApertureBoundaryFisherClock p +
        gammaSewnMobiusApertureBoundaryFisherClock q -
      2 * gammaSewnBoundaryFisherAmplitude p *
        gammaSewnBoundaryFisherAmplitude q * r := by
  have hp := gammaSewnBoundaryFisherAmplitude_sq p
  have hq := gammaSewnBoundaryFisherAmplitude_sq q
  have hnonneg := mul_nonneg
    (mul_nonneg (gammaSewnBoundaryFisherAmplitude_nonneg p)
      (gammaSewnBoundaryFisherAmplitude_nonneg q))
    (sub_nonneg.mpr hr)
  nlinarith [sq_nonneg
    (gammaSewnBoundaryFisherAmplitude p - gammaSewnBoundaryFisherAmplitude q)]

theorem gammaSewnFourRateComplementaryResponsePairMetric_nonneg
    (response : Nat.Primes → Nat.Primes → ℝ)
    (hresponse : ∀ p q, response p q ≤ 1)
    (cell : Fin 4 → Nat.Primes × ℕ) (s t : Fin 6) :
    0 ≤ gammaSewnFourRateComplementaryFisher cell s +
        gammaSewnFourRateComplementaryFisher cell t -
      2 * gammaSewnFourRateComplementaryResponseKernel response cell s t := by
  have hleft := fisherAmplitude_response_defect_nonneg
    (cell (fourRatePairComplementLeft s)).1
    (cell (fourRatePairComplementLeft t)).1
    (r := response (cell (fourRatePairComplementLeft s)).1
      (cell (fourRatePairComplementLeft t)).1)
    (hresponse _ _)
  have hright := fisherAmplitude_response_defect_nonneg
    (cell (fourRatePairComplementRight s)).1
    (cell (fourRatePairComplementRight t)).1
    (r := response (cell (fourRatePairComplementRight s)).1
      (cell (fourRatePairComplementRight t)).1)
    (hresponse _ _)
  unfold gammaSewnFourRateComplementaryFisher fourRateComplementarySum
    gammaSewnFourRateComplementaryResponseKernel
  nlinarith

theorem gammaSewnFourRateComplementaryResponseFatherEnergy_nonneg
    {weight : Fin 6 → ℝ} (hweight : ∀ s, 0 ≤ weight s)
    (response : Nat.Primes → Nat.Primes → ℝ)
    (hresponse : ∀ p q, 0 ≤ response p q)
    (cell : Fin 4 → Nat.Primes × ℕ) :
    0 ≤ gammaSewnFourRateComplementaryResponseFatherEnergy weight response cell := by
  unfold gammaSewnFourRateComplementaryResponseFatherEnergy
  apply Finset.sum_nonneg
  intro s _hs
  apply Finset.sum_nonneg
  intro t _ht
  apply mul_nonneg (mul_nonneg (hweight s) (hweight t))
  unfold gammaSewnFourRateComplementaryResponseKernel
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (gammaSewnBoundaryFisherAmplitude_nonneg _)
        (gammaSewnBoundaryFisherAmplitude_nonneg _)) (hresponse _ _))
    (mul_nonneg
      (mul_nonneg (gammaSewnBoundaryFisherAmplitude_nonneg _)
        (gammaSewnBoundaryFisherAmplitude_nonneg _)) (hresponse _ _))

theorem gammaSewnFourRateComplementaryResponseDetailEnergy_nonneg
    {weight : Fin 6 → ℝ} (hweight : ∀ s, 0 ≤ weight s)
    (response : Nat.Primes → Nat.Primes → ℝ)
    (hresponse : ∀ p q, response p q ≤ 1)
    (cell : Fin 4 → Nat.Primes × ℕ) :
    0 ≤ gammaSewnFourRateComplementaryResponseDetailEnergy weight response cell := by
  unfold gammaSewnFourRateComplementaryResponseDetailEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro s _hs
  apply Finset.sum_nonneg
  intro t _ht
  exact mul_nonneg (mul_nonneg (hweight s) (hweight t))
    (gammaSewnFourRateComplementaryResponsePairMetric_nonneg response hresponse cell s t)

/-! ## Exact Gamma-to-Xi mass transfer -/

/-- Father energy for the joined Gamma response on the actual boundary-minor probability packet. -/
def gammaJordanFourRateJoinedFatherEnergy
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  gammaSewnFourRateComplementaryResponseFatherEnergy
    (gammaSewnFourRateBoundaryPairProbability a rate cell)
    gammaJordanXiPrimeJoinedResponse cell

/-- Detail energy for the joined Gamma response. -/
def gammaJordanFourRateJoinedDetailEnergy
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  gammaSewnFourRateComplementaryResponseDetailEnergy
    (gammaSewnFourRateBoundaryPairProbability a rate cell)
    gammaJordanXiPrimeJoinedResponse cell

/-- Father energy for the actual all-depth Xi-shift tangent response. -/
def xiTangentFourRateFatherEnergy
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  gammaSewnFourRateComplementaryResponseFatherEnergy
    (gammaSewnFourRateBoundaryPairProbability a rate cell)
    gammaSewnXiShiftEndpointUnitTangentKernel cell

/-- Detail energy for the actual all-depth Xi-shift tangent response. -/
def xiTangentFourRateDetailEnergy
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  gammaSewnFourRateComplementaryResponseDetailEnergy
    (gammaSewnFourRateBoundaryPairProbability a rate cell)
    gammaSewnXiShiftEndpointUnitTangentKernel cell

/-- Correlated amount transferred by the joined-Gamma/Xi-tangent response gap. -/
def gammaJordanXiFourRateGapTransfer
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  gammaSewnFourRateComplementaryResponseFatherEnergy
    (gammaSewnFourRateBoundaryPairProbability a rate cell)
    gammaJordanXiPrimeResponseGap cell

theorem gammaSewnFourRateComplementaryKernel_joined_eq_tangent_add_gap
    (cell : Fin 4 → Nat.Primes × ℕ) (s t : Fin 6) :
    gammaSewnFourRateComplementaryResponseKernel
        gammaJordanXiPrimeJoinedResponse cell s t =
      gammaSewnFourRateComplementaryResponseKernel
          gammaSewnXiShiftEndpointUnitTangentKernel cell s t +
        gammaSewnFourRateComplementaryResponseKernel
          gammaJordanXiPrimeResponseGap cell s t := by
  unfold gammaSewnFourRateComplementaryResponseKernel
    gammaJordanXiPrimeJoinedResponse
  rw [gammaJordanXiPrimeResponseGap_eq_joined_sub_tangent,
    gammaJordanXiPrimeResponseGap_eq_joined_sub_tangent]
  ring

theorem gammaJordanFourRateJoinedFather_eq_tangent_add_gap
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    gammaJordanFourRateJoinedFatherEnergy a rate cell =
      xiTangentFourRateFatherEnergy a rate cell +
        gammaJordanXiFourRateGapTransfer a rate cell := by
  unfold gammaJordanFourRateJoinedFatherEnergy xiTangentFourRateFatherEnergy
    gammaJordanXiFourRateGapTransfer
    gammaSewnFourRateComplementaryResponseFatherEnergy
  simp_rw [gammaSewnFourRateComplementaryKernel_joined_eq_tangent_add_gap,
    mul_add, Finset.sum_add_distrib]

theorem gammaJordanFourRateFisherMean_eq_joinedDetail_add_father
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) =
      gammaJordanFourRateJoinedDetailEnergy a rate cell +
        gammaJordanFourRateJoinedFatherEnergy a rate cell := by
  apply gammaSewnFourRateComplementaryFisherMean_eq_detail_add_father
  exact sum_gammaSewnFourRateBoundaryPairProbability hpartition

theorem gammaJordanFourRateFisherMean_eq_tangentDetail_add_father
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) =
      xiTangentFourRateDetailEnergy a rate cell +
        xiTangentFourRateFatherEnergy a rate cell := by
  apply gammaSewnFourRateComplementaryFisherMean_eq_detail_add_father
  exact sum_gammaSewnFourRateBoundaryPairProbability hpartition

/-- **Exact response transfer law.**  The joined response moves precisely the gap-transfer mass
from Xi detail to the father channel; no Fisher/Jordan mass disappears. -/
theorem xiTangentFourRateDetail_eq_joinedDetail_add_gap
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    xiTangentFourRateDetailEnergy a rate cell =
      gammaJordanFourRateJoinedDetailEnergy a rate cell +
        gammaJordanXiFourRateGapTransfer a rate cell := by
  have hjoined := gammaJordanFourRateFisherMean_eq_joinedDetail_add_father hpartition
  have htangent := gammaJordanFourRateFisherMean_eq_tangentDetail_add_father hpartition
  have hfather := gammaJordanFourRateJoinedFather_eq_tangent_add_gap a rate cell
  linarith

/-- Nonvanishing Hilbert-feature volume discharges the raw normalization premise in the exact
Gamma-to-Xi detail transfer. -/
theorem xiTangentFourRateDetail_eq_joinedDetail_add_gap_of_volume_ne_zero
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hvolume : canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
      (fun _ => 1) (fun _ => 0) 1 ≠ 0) :
    xiTangentFourRateDetailEnergy a rate cell =
      gammaJordanFourRateJoinedDetailEnergy a rate cell +
        gammaJordanXiFourRateGapTransfer a rate cell := by
  apply xiTangentFourRateDetail_eq_joinedDetail_add_gap
  rw [gammaSewnFourRateBoundaryPairPartition_eq_canonicalFeatureVolume]
  exact hvolume

/-- **Canonical Pluecker father--detail conservation.**  For every nonzero canonical feature
volume, the same canonical sewing mass is `3/2` of either the joined-Gamma or Xi-tangent
father--detail total, and Schur curvature is `-2` times either total minus the selected-height
dispersion penalty.  Thus the response-gap transfer changes only the father/detail allocation. -/
theorem gammaJordanXiFourRateCanonicalPlucker_energy_conservation_of_volume_ne_zero
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hvolume : canonicalFeatureVolume
      (gammaSewnFourRateBoundaryPluckerFeature a rate cell)
      (fun _ => 1) (fun _ => 0) 1 ≠ 0) :
    gammaSewnFourRateCanonicalPluckerSewingMass a rate cell =
        (3 / 2 : ℝ) *
          (gammaJordanFourRateJoinedDetailEnergy a rate cell +
            gammaJordanFourRateJoinedFatherEnergy a rate cell) ∧
      gammaSewnFourRateCanonicalPluckerSewingMass a rate cell =
        (3 / 2 : ℝ) *
          (xiTangentFourRateDetailEnergy a rate cell +
            xiTangentFourRateFatherEnergy a rate cell) ∧
      gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
        -2 * (gammaJordanFourRateJoinedDetailEnergy a rate cell +
          gammaJordanFourRateJoinedFatherEnergy a rate cell) -
        2 * normalizedFinitePairDispersion
          (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
          (gammaSewnFourRateSelectedHeight cell) ∧
      gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
        -2 * (xiTangentFourRateDetailEnergy a rate cell +
          xiTangentFourRateFatherEnergy a rate cell) -
        2 * normalizedFinitePairDispersion
          (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
          (gammaSewnFourRateSelectedHeight cell) := by
  have hpartition :
      (∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s) ≠ 0 := by
    rw [gammaSewnFourRateBoundaryPairPartition_eq_canonicalFeatureVolume]
    exact hvolume
  have hjoined := gammaJordanFourRateFisherMean_eq_joinedDetail_add_father hpartition
  have htangent := gammaJordanFourRateFisherMean_eq_tangentDetail_add_father hpartition
  have hprob :
      gammaSewnFourRateBoundaryPairProbability a rate cell =
        gammaSewnFourRateCanonicalPluckerProbability a rate cell := by
    funext s
    exact gammaSewnFourRateBoundaryPairProbability_eq_canonicalFeatureVolume_normalized
      a rate cell s
  rw [hprob] at hjoined htangent
  have hcorrected :=
    gammaSewnFourRateSchurCorrectedFisher_eq_canonicalPlucker_of_volume_ne_zero hvolume
  have hsewing :=
    gammaSewnFourRateCanonicalPluckerSewingMass_eq_three_halves_correctedFisher_of_volume_ne_zero
      hvolume
  have hcurvature :=
    gammaSewnFourRateSchurBoundaryLogCurvature_eq_canonicalPluckerJordan_of_volume_ne_zero
      hvolume
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Source nondegeneracy supplies the Hilbert-feature volume in canonical Pluecker father--detail
conservation. -/
theorem gammaJordanXiFourRateCanonicalPlucker_energy_conservation
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    gammaSewnFourRateCanonicalPluckerSewingMass a rate cell =
        (3 / 2 : ℝ) *
          (gammaJordanFourRateJoinedDetailEnergy a rate cell +
            gammaJordanFourRateJoinedFatherEnergy a rate cell) ∧
      gammaSewnFourRateCanonicalPluckerSewingMass a rate cell =
        (3 / 2 : ℝ) *
          (xiTangentFourRateDetailEnergy a rate cell +
            xiTangentFourRateFatherEnergy a rate cell) ∧
      gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
        -2 * (gammaJordanFourRateJoinedDetailEnergy a rate cell +
          gammaJordanFourRateJoinedFatherEnergy a rate cell) -
        2 * normalizedFinitePairDispersion
          (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
          (gammaSewnFourRateSelectedHeight cell) ∧
      gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
        -2 * (xiTangentFourRateDetailEnergy a rate cell +
          xiTangentFourRateFatherEnergy a rate cell) -
        2 * normalizedFinitePairDispersion
          (gammaSewnFourRateCanonicalPluckerProbability a rate cell)
          (gammaSewnFourRateSelectedHeight cell) := by
  exact gammaJordanXiFourRateCanonicalPlucker_energy_conservation_of_volume_ne_zero
    (gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
      (cell := cell) ha hrate hboundary).ne'

theorem gammaJordanXiFourRateGapTransfer_nonneg
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    0 ≤ gammaJordanXiFourRateGapTransfer a rate cell := by
  apply gammaSewnFourRateComplementaryResponseFatherEnergy_nonneg
  · intro s
    exact (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s).le
  · exact gammaJordanXiPrimeResponseGap_nonneg

theorem gammaSewnFourRateComplementaryGapKernel_pos_of_aligned_crossPrime
    {cell : Fin 4 → Nat.Primes × ℕ} {s t : Fin 6}
    (hcross :
      (cell (fourRatePairComplementLeft s)).1 ≠
          (cell (fourRatePairComplementLeft t)).1 ∨
        (cell (fourRatePairComplementRight s)).1 ≠
          (cell (fourRatePairComplementRight t)).1) :
    0 < gammaSewnFourRateComplementaryResponseKernel
      gammaJordanXiPrimeResponseGap cell s t := by
  unfold gammaSewnFourRateComplementaryResponseKernel
  rcases hcross with hleft | hright
  · apply add_pos_of_pos_of_nonneg
    · exact mul_pos
        (mul_pos (gammaSewnBoundaryFisherAmplitude_pos _)
          (gammaSewnBoundaryFisherAmplitude_pos _))
        ((gammaJordanXiPrimeResponseGap_pos_iff _ _).2 hleft)
    · exact mul_nonneg
        (mul_nonneg (gammaSewnBoundaryFisherAmplitude_nonneg _)
          (gammaSewnBoundaryFisherAmplitude_nonneg _))
        (gammaJordanXiPrimeResponseGap_nonneg _ _)
  · apply add_pos_of_nonneg_of_pos
    · exact mul_nonneg
        (mul_nonneg (gammaSewnBoundaryFisherAmplitude_nonneg _)
          (gammaSewnBoundaryFisherAmplitude_nonneg _))
        (gammaJordanXiPrimeResponseGap_nonneg _ _)
    · exact mul_pos
        (mul_pos (gammaSewnBoundaryFisherAmplitude_pos _)
          (gammaSewnBoundaryFisherAmplitude_pos _))
        ((gammaJordanXiPrimeResponseGap_pos_iff _ _).2 hright)

/-- The transfer is strict as soon as two positive-weight complementary pairs differ in one
aligned prime slot.  This is the precise finite nondegeneracy condition; no matching to Xi zeros
is introduced. -/
theorem gammaJordanXiFourRateGapTransfer_pos_of_aligned_crossPrime
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0)
    (hcross : ∃ s t : Fin 6,
      (cell (fourRatePairComplementLeft s)).1 ≠
          (cell (fourRatePairComplementLeft t)).1 ∨
        (cell (fourRatePairComplementRight s)).1 ≠
          (cell (fourRatePairComplementRight t)).1) :
    0 < gammaJordanXiFourRateGapTransfer a rate cell := by
  rcases hcross with ⟨s, t, hst⟩
  unfold gammaJordanXiFourRateGapTransfer
    gammaSewnFourRateComplementaryResponseFatherEnergy
  apply Finset.sum_pos'
  · intro u _hu
    apply Finset.sum_nonneg
    intro v _hv
    exact mul_nonneg
      (mul_nonneg
        (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary u).le
        (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary v).le)
      (by
        unfold gammaSewnFourRateComplementaryResponseKernel
        exact add_nonneg
          (mul_nonneg
            (mul_nonneg (gammaSewnBoundaryFisherAmplitude_nonneg _)
              (gammaSewnBoundaryFisherAmplitude_nonneg _))
            (gammaJordanXiPrimeResponseGap_nonneg _ _))
          (mul_nonneg
            (mul_nonneg (gammaSewnBoundaryFisherAmplitude_nonneg _)
              (gammaSewnBoundaryFisherAmplitude_nonneg _))
            (gammaJordanXiPrimeResponseGap_nonneg _ _)))
  · refine ⟨s, Finset.mem_univ s, ?_⟩
    apply Finset.sum_pos'
    · intro v _hv
      exact mul_nonneg
        (mul_nonneg
          (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s).le
          (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary v).le)
        (by
          unfold gammaSewnFourRateComplementaryResponseKernel
          exact add_nonneg
            (mul_nonneg
              (mul_nonneg (gammaSewnBoundaryFisherAmplitude_nonneg _)
                (gammaSewnBoundaryFisherAmplitude_nonneg _))
              (gammaJordanXiPrimeResponseGap_nonneg _ _))
            (mul_nonneg
              (mul_nonneg (gammaSewnBoundaryFisherAmplitude_nonneg _)
                (gammaSewnBoundaryFisherAmplitude_nonneg _))
              (gammaJordanXiPrimeResponseGap_nonneg _ _)))
    · refine ⟨t, Finset.mem_univ t, ?_⟩
      exact mul_pos
        (mul_pos
          (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s)
          (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary t))
        (gammaSewnFourRateComplementaryGapKernel_pos_of_aligned_crossPrime hst)

theorem gammaJordanFourRateJoinedFather_le_tangentDetail_transfer
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    gammaJordanFourRateJoinedDetailEnergy a rate cell ≤
      xiTangentFourRateDetailEnergy a rate cell := by
  have hvolume := gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
    (cell := cell) ha hrate hboundary
  rw [xiTangentFourRateDetail_eq_joinedDetail_add_gap_of_volume_ne_zero hvolume.ne']
  exact le_add_of_nonneg_right
    (gammaJordanXiFourRateGapTransfer_nonneg ha hrate hboundary)

theorem xiTangentFourRateFather_le_joinedFather
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    xiTangentFourRateFatherEnergy a rate cell ≤
      gammaJordanFourRateJoinedFatherEnergy a rate cell := by
  rw [gammaJordanFourRateJoinedFather_eq_tangent_add_gap]
  exact le_add_of_nonneg_right
    (gammaJordanXiFourRateGapTransfer_nonneg ha hrate hboundary)

theorem gammaJordanFourRateJoinedDetail_lt_tangentDetail_of_aligned_crossPrime
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0)
    (hcross : ∃ s t : Fin 6,
      (cell (fourRatePairComplementLeft s)).1 ≠
          (cell (fourRatePairComplementLeft t)).1 ∨
        (cell (fourRatePairComplementRight s)).1 ≠
          (cell (fourRatePairComplementRight t)).1) :
    gammaJordanFourRateJoinedDetailEnergy a rate cell <
      xiTangentFourRateDetailEnergy a rate cell := by
  have hvolume := gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos
    (cell := cell) ha hrate hboundary
  rw [xiTangentFourRateDetail_eq_joinedDetail_add_gap_of_volume_ne_zero hvolume.ne']
  exact lt_add_of_pos_right _
    (gammaJordanXiFourRateGapTransfer_pos_of_aligned_crossPrime
      ha hrate hboundary hcross)

theorem xiTangentFourRateFather_lt_joinedFather_of_aligned_crossPrime
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0)
    (hcross : ∃ s t : Fin 6,
      (cell (fourRatePairComplementLeft s)).1 ≠
          (cell (fourRatePairComplementLeft t)).1 ∨
        (cell (fourRatePairComplementRight s)).1 ≠
          (cell (fourRatePairComplementRight t)).1) :
    xiTangentFourRateFatherEnergy a rate cell <
      gammaJordanFourRateJoinedFatherEnergy a rate cell := by
  rw [gammaJordanFourRateJoinedFather_eq_tangent_add_gap]
  exact lt_add_of_pos_right _
    (gammaJordanXiFourRateGapTransfer_pos_of_aligned_crossPrime
      ha hrate hboundary hcross)

theorem gammaJordanFourRateJoinedFather_nonneg
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    0 ≤ gammaJordanFourRateJoinedFatherEnergy a rate cell := by
  apply gammaSewnFourRateComplementaryResponseFatherEnergy_nonneg
  · intro s
    exact (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s).le
  · exact gammaJordanXiPrimeJoinedResponse_nonneg

theorem gammaJordanFourRateJoinedDetail_nonneg
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    0 ≤ gammaJordanFourRateJoinedDetailEnergy a rate cell := by
  apply gammaSewnFourRateComplementaryResponseDetailEnergy_nonneg
  · intro s
    exact (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s).le
  · exact gammaJordanXiPrimeJoinedResponse_le_one

theorem xiTangentFourRateFather_nonneg
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    0 ≤ xiTangentFourRateFatherEnergy a rate cell := by
  apply gammaSewnFourRateComplementaryResponseFatherEnergy_nonneg
  · intro s
    exact (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s).le
  · exact gammaSewnXiShiftEndpointUnitTangentKernel_nonneg

theorem xiTangentFourRateDetail_nonneg
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) :
    0 ≤ xiTangentFourRateDetailEnergy a rate cell := by
  apply gammaSewnFourRateComplementaryResponseDetailEnergy_nonneg
  · intro s
    exact (gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary s).le
  · exact gammaSewnXiShiftEndpointUnitTangentKernel_le_one

/-! ## Unconditional transfer on four distinct actual primes -/

/-- A four-prime embedding automatically supplies the aligned cross-prime witness required for
strict father--detail transfer.  This removes the last ad hoc combinatorial proposition from the
actual-prime interface. -/
theorem gammaSewnFourPrimeCell_exists_aligned_crossPrime
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    ∃ s t : Fin 6,
      ((gammaSewnFourPrimeCell prime depth)
          (fourRatePairComplementLeft s)).1 ≠
          ((gammaSewnFourPrimeCell prime depth)
            (fourRatePairComplementLeft t)).1 ∨
        ((gammaSewnFourPrimeCell prime depth)
          (fourRatePairComplementRight s)).1 ≠
          ((gammaSewnFourPrimeCell prime depth)
            (fourRatePairComplementRight t)).1 := by
  refine ⟨0, 1, Or.inl ?_⟩
  simp only [gammaSewnFourPrimeCell, fourRatePairComplementLeft,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact prime.injective.ne (Fin.ne_of_val_ne (Nat.succ_ne_self 1))

/-- **Strict actual-prime father--detail transfer.**  At the canonical physical aperture, every
four-distinct-prime packet transfers a strictly positive response-gap mass from Xi detail to the
joined-Gamma father channel, for every valuation-depth profile.  Source nondegeneracy and the
cross-prime witness are both discharged by existing actual-prime geometry. -/
theorem gammaJordanXiFourPrimeLog_strict_father_detail_transfer
    (prime : Fin 4 ↪ Nat.Primes) (depth : Fin 4 → ℕ) :
    0 < gammaJordanXiFourRateGapTransfer
        (gammaSewnFourPrimeLogHarmonicAperture prime)
        (gammaSewnFourPrimeLogRate prime)
        (gammaSewnFourPrimeCell prime depth) ∧
      gammaJordanFourRateJoinedDetailEnergy
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourPrimeCell prime depth) <
        xiTangentFourRateDetailEnergy
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourPrimeCell prime depth) ∧
      xiTangentFourRateFatherEnergy
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourPrimeCell prime depth) <
        gammaJordanFourRateJoinedFatherEnergy
          (gammaSewnFourPrimeLogHarmonicAperture prime)
          (gammaSewnFourPrimeLogRate prime)
          (gammaSewnFourPrimeCell prime depth) := by
  have hcross := gammaSewnFourPrimeCell_exists_aligned_crossPrime prime depth
  have ha := (gammaSewnFourPrimeLogHarmonicAperture_pos prime).ne'
  have hrate := gammaSewnFourPrimeLogRate_injective prime
  have hboundary := gammaSewnFourPrimeLogHarmonicAperture_boundary_ne prime
  constructor
  · exact gammaJordanXiFourRateGapTransfer_pos_of_aligned_crossPrime
      ha hrate hboundary hcross
  constructor
  · exact gammaJordanFourRateJoinedDetail_lt_tangentDetail_of_aligned_crossPrime
      ha hrate hboundary hcross
  · exact xiTangentFourRateFather_lt_joinedFather_of_aligned_crossPrime
      ha hrate hboundary hcross

/-! ## Same-prime fibre: the exact common-mode obstruction -/

/-- Four arbitrary valuation depths supported at one prime. -/
def gammaSewnFourRateSamePrimeCell
    (p : Nat.Primes) (depth : Fin 4 → ℕ) (i : Fin 4) : Nat.Primes × ℕ :=
  (p, depth i)

theorem gammaSewnFourRateComplementaryFisher_samePrime
    (p : Nat.Primes) (depth : Fin 4 → ℕ) (s : Fin 6) :
    gammaSewnFourRateComplementaryFisher
        (gammaSewnFourRateSamePrimeCell p depth) s =
      2 * gammaSewnMobiusApertureBoundaryFisherClock p := by
  unfold gammaSewnFourRateComplementaryFisher fourRateComplementarySum
    gammaSewnFourRateSamePrimeCell
  ring

theorem gammaSewnFourRateComplementaryResponseKernel_samePrime
    (response : Nat.Primes → Nat.Primes → ℝ) (p : Nat.Primes)
    (hself : response p p = 1) (depth : Fin 4 → ℕ) (s t : Fin 6) :
    gammaSewnFourRateComplementaryResponseKernel response
        (gammaSewnFourRateSamePrimeCell p depth) s t =
      2 * gammaSewnMobiusApertureBoundaryFisherClock p := by
  unfold gammaSewnFourRateComplementaryResponseKernel
    gammaSewnFourRateSamePrimeCell
  rw [hself]
  have hsquare := gammaSewnBoundaryFisherAmplitude_sq p
  nlinarith

theorem gammaSewnFourRateComplementaryFisherMean_samePrime
    {a : ℝ} {rate : Fin 4 → ℝ} (p : Nat.Primes) (depth : Fin 4 → ℕ)
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate
      (gammaSewnFourRateSamePrimeCell p depth) s ≠ 0) :
    complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate
          (gammaSewnFourRateSamePrimeCell p depth))
        (gammaSewnFourRateComplementaryFisher
          (gammaSewnFourRateSamePrimeCell p depth)) =
      2 * gammaSewnMobiusApertureBoundaryFisherClock p := by
  unfold complementaryFisherMean
  simp_rw [gammaSewnFourRateComplementaryFisher_samePrime]
  rw [← Finset.sum_mul,
    sum_gammaSewnFourRateBoundaryPairProbability hpartition]
  ring

theorem gammaSewnFourRateComplementaryResponseDetailEnergy_samePrime
    {a : ℝ} {rate : Fin 4 → ℝ} (response : Nat.Primes → Nat.Primes → ℝ)
    (p : Nat.Primes) (hself : response p p = 1) (depth : Fin 4 → ℕ) :
    gammaSewnFourRateComplementaryResponseDetailEnergy
        (gammaSewnFourRateBoundaryPairProbability a rate
          (gammaSewnFourRateSamePrimeCell p depth)) response
        (gammaSewnFourRateSamePrimeCell p depth) = 0 := by
  unfold gammaSewnFourRateComplementaryResponseDetailEnergy
  simp_rw [gammaSewnFourRateComplementaryFisher_samePrime,
    gammaSewnFourRateComplementaryResponseKernel_samePrime response p hself]
  have hzero :
      2 * gammaSewnMobiusApertureBoundaryFisherClock p +
          2 * gammaSewnMobiusApertureBoundaryFisherClock p -
        2 * (2 * gammaSewnMobiusApertureBoundaryFisherClock p) = 0 := by
    ring
  rw [hzero]
  simp

/-- On a one-prime/four-depth fibre, both the joined Gamma and actual Xi tangent geometries retain
the full positive Fisher mass in the father channel and have zero detail. -/
theorem gammaJordanXi_samePrime_pureFather
    {a : ℝ} {rate : Fin 4 → ℝ} (p : Nat.Primes) (depth : Fin 4 → ℕ)
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate
      (gammaSewnFourRateSamePrimeCell p depth) s ≠ 0) :
    gammaJordanFourRateJoinedDetailEnergy a rate
          (gammaSewnFourRateSamePrimeCell p depth) = 0 ∧
      xiTangentFourRateDetailEnergy a rate
          (gammaSewnFourRateSamePrimeCell p depth) = 0 ∧
      gammaJordanFourRateJoinedFatherEnergy a rate
          (gammaSewnFourRateSamePrimeCell p depth) =
        2 * gammaSewnMobiusApertureBoundaryFisherClock p ∧
      xiTangentFourRateFatherEnergy a rate
          (gammaSewnFourRateSamePrimeCell p depth) =
        2 * gammaSewnMobiusApertureBoundaryFisherClock p ∧
      gammaJordanXiFourRateGapTransfer a rate
          (gammaSewnFourRateSamePrimeCell p depth) = 0 := by
  have hJDetail := gammaSewnFourRateComplementaryResponseDetailEnergy_samePrime
    (a := a) (rate := rate) gammaJordanXiPrimeJoinedResponse
    p (gammaJordanXiPrimeJoinedResponse_self p) depth
  have hTDetail := gammaSewnFourRateComplementaryResponseDetailEnergy_samePrime
    (a := a) (rate := rate) gammaSewnXiShiftEndpointUnitTangentKernel
    p (gammaSewnXiShiftEndpointUnitTangentKernel_self p) depth
  have hmean := gammaSewnFourRateComplementaryFisherMean_samePrime
    p depth hpartition
  have hJsplit := gammaJordanFourRateFisherMean_eq_joinedDetail_add_father hpartition
  have hTsplit := gammaJordanFourRateFisherMean_eq_tangentDetail_add_father hpartition
  have htransfer := gammaJordanFourRateJoinedFather_eq_tangent_add_gap
    a rate (gammaSewnFourRateSamePrimeCell p depth)
  change gammaJordanFourRateJoinedDetailEnergy a rate
      (gammaSewnFourRateSamePrimeCell p depth) = 0 at hJDetail
  change xiTangentFourRateDetailEnergy a rate
      (gammaSewnFourRateSamePrimeCell p depth) = 0 at hTDetail
  refine ⟨hJDetail, hTDetail, ?_, ?_, ?_⟩ <;> linarith

/-- **Sharp no-go.**  No scalar multiple of the unpointed response-gap transfer controls the
signed Jordan/Fisher mass on all source-realizable four-rate cells.  The obstruction is already
the one-prime fibre, where the gap is zero and the mass is strictly positive. -/
theorem gammaJordanXi_no_gap_domination_on_samePrime
    {a : ℝ} {rate : Fin 4 → ℝ} (p : Nat.Primes) (depth : Fin 4 → ℕ)
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ (2 : ℕ) - a ^ (2 : ℕ) ≠ 0) (C : ℝ) :
    C * gammaJordanXiFourRateGapTransfer a rate
          (gammaSewnFourRateSamePrimeCell p depth) <
      complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate
          (gammaSewnFourRateSamePrimeCell p depth))
        (gammaSewnFourRateComplementaryFisher
          (gammaSewnFourRateSamePrimeCell p depth)) := by
  have hpartition := gammaSewnFourRateBoundaryPairPartition_pos
    (cell := gammaSewnFourRateSamePrimeCell p depth) ha hrate hboundary
  have hpure := gammaJordanXi_samePrime_pureFather p depth hpartition.ne'
  have hmean := gammaSewnFourRateComplementaryFisherMean_samePrime
    p depth hpartition.ne'
  calc
    C * gammaJordanXiFourRateGapTransfer a rate
        (gammaSewnFourRateSamePrimeCell p depth) = 0 := by
          rw [hpure.2.2.2.2]
          ring
    _ < complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate
          (gammaSewnFourRateSamePrimeCell p depth))
        (gammaSewnFourRateComplementaryFisher
          (gammaSewnFourRateSamePrimeCell p depth)) := by
          rw [hmean]
          exact mul_pos (by norm_num)
            (gammaSewnMobiusApertureBoundaryFisherClock_pos p)

end

end RHTower
