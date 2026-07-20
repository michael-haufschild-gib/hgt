import GaloisForLFunctions.RHTower.GammaSewnApertureFisherSeam
import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary

/-!
# Four-rate Schur curvature of the Gamma-sewn boundary jet

Removing the two Cauchy boundary rows from a four-rate cell leaves a two-dimensional exterior
response.  Cauchy--Binet makes the denominator of its squared Schur volume a positive partition
over the six boundary pair minors.  The Gamma-sewn two-jet then gives an exact curvature law.

After normalization, every individual midpoint-square term cancels.  The logarithmic boundary
curvature is the negative sum of two intrinsic quantities:

* the expected Fisher clock on the complementary pair; and
* the pair-sum midpoint-height dispersion of the six boundary minors.

Consequently a unique cumulant correction removes the height dispersion and leaves precisely the
complementary Fisher clock.  This is the local normalization test required by the four-rate
Euler-calibrated exterior transfer; no target response or Xi zero enters the construction.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The literal two-boundary Cauchy minor -/

/-- Determinant of the two boundary rows `+a,-a` on two Cauchy rates. -/
def twoBoundaryCauchyPairDet (a lambda mu : ℝ) : ℝ :=
  1 / (a + lambda) * (1 / (-a + mu)) -
    1 / (a + mu) * (1 / (-a + lambda))

/-- The simplified Pluecker coordinate of the two boundary rows. -/
def twoBoundaryCauchyPairPlucker (a lambda mu : ℝ) : ℝ :=
  2 * a * (lambda - mu) /
    ((lambda ^ 2 - a ^ 2) * (mu ^ 2 - a ^ 2))

/-- Exact two-boundary Cauchy determinant formula. -/
theorem twoBoundaryCauchyPairDet_eq_plucker
    {a lambda mu : ℝ}
    (hlp : a + lambda ≠ 0) (hlm : -a + lambda ≠ 0)
    (hmp : a + mu ≠ 0) (hmm : -a + mu ≠ 0) :
    twoBoundaryCauchyPairDet a lambda mu =
      twoBoundaryCauchyPairPlucker a lambda mu := by
  have hl : lambda ^ 2 - a ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero
      (by simpa [add_comm] using hlp)
      (by simpa [sub_eq_add_neg, add_comm] using hlm)
  have hm : mu ^ 2 - a ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero
      (by simpa [add_comm] using hmp)
      (by simpa [sub_eq_add_neg, add_comm] using hmm)
  unfold twoBoundaryCauchyPairDet twoBoundaryCauchyPairPlucker
  field_simp [hl, hm]
  ring

/-- Squared boundary Pluecker weight carried by a pair of source rates. -/
def twoBoundaryCauchyPairPluckerSq (a lambda mu : ℝ) : ℝ :=
  twoBoundaryCauchyPairPlucker a lambda mu ^ 2

theorem twoBoundaryCauchyPairPluckerSq_pos
    {a lambda mu : ℝ} (ha : a ≠ 0) (hlm : lambda ≠ mu)
    (hl : lambda ^ 2 - a ^ 2 ≠ 0) (hm : mu ^ 2 - a ^ 2 ≠ 0) :
    0 < twoBoundaryCauchyPairPluckerSq a lambda mu := by
  apply sq_pos_of_ne_zero
  unfold twoBoundaryCauchyPairPlucker
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) ha) (sub_ne_zero.mpr hlm)
  · exact mul_ne_zero hl hm

/-! ## The six pairs and their complementary pairs -/

/-- Left endpoint of the six unordered pairs of four rates. -/
def fourRatePairLeft : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- Right endpoint of the six unordered pairs of four rates. -/
def fourRatePairRight : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- Left endpoint of the complementary pair. -/
def fourRatePairComplementLeft : Fin 6 → Fin 4 := ![2, 1, 1, 0, 0, 0]

/-- Right endpoint of the complementary pair. -/
def fourRatePairComplementRight : Fin 6 → Fin 4 := ![3, 3, 2, 3, 2, 1]

theorem fourRatePairLeft_ne_right (s : Fin 6) :
    fourRatePairLeft s ≠ fourRatePairRight s := by
  fin_cases s <;> decide

/-- Sum of a four-rate observable on the selected pair. -/
def fourRateSelectedSum (x : Fin 4 → ℝ) (s : Fin 6) : ℝ :=
  x (fourRatePairLeft s) + x (fourRatePairRight s)

/-- Sum of a four-rate observable on the complementary pair. -/
def fourRateComplementarySum (x : Fin 4 → ℝ) (s : Fin 6) : ℝ :=
  x (fourRatePairComplementLeft s) + x (fourRatePairComplementRight s)

/-- Total of a four-rate observable. -/
def fourRateTotalSum (x : Fin 4 → ℝ) : ℝ :=
  x 0 + x 1 + x 2 + x 3

theorem fourRateSelectedSum_add_complementarySum
    (x : Fin 4 → ℝ) (s : Fin 6) :
    fourRateSelectedSum x s + fourRateComplementarySum x s =
      fourRateTotalSum x := by
  fin_cases s <;>
    simp [fourRateSelectedSum, fourRateComplementarySum,
      fourRateTotalSum, fourRatePairLeft, fourRatePairRight,
      fourRatePairComplementLeft, fourRatePairComplementRight] <;> ring

/-! ## Abstract curvature and its exact complementary decomposition -/

/-- Variance of an observable under a normalized finite weight. -/
def normalizedFiniteVariance {β : Type*} [Fintype β]
    (weight value : β → ℝ) : ℝ :=
  (∑ b, weight b * value b ^ 2) - (∑ b, weight b * value b) ^ 2

/-- Ordered pairwise dispersion under a normalized finite weight. -/
def normalizedFinitePairDispersion {β : Type*} [Fintype β]
    (weight value : β → ℝ) : ℝ :=
  ∑ b, ∑ c, weight b * weight c * (value b - value c) ^ 2

/-- Boundary logarithmic curvature forced by a four-rate Schur quotient.

The numerator contains all four rate clocks, while the boundary denominator is the normalized
partition over selected pairs. -/
def fourRateSchurBoundaryLogCurvature {β : Type*} [Fintype β]
    (weight selectedHeight selectedFisher : β → ℝ) (totalFisher : ℝ) : ℝ :=
  -2 * totalFisher + 2 * (∑ b, weight b * selectedFisher b) -
    4 * normalizedFiniteVariance weight selectedHeight

/-- Expected Fisher clock on the pair complementary to the boundary minor. -/
def complementaryFisherMean {β : Type*} [Fintype β]
    (weight complementaryFisher : β → ℝ) : ℝ :=
  ∑ b, weight b * complementaryFisher b

/-- **Complementary Fisher--dispersion law.**  Once the six boundary-minor weights are normalized,
the four-rate Schur curvature is exactly minus twice the complementary Fisher mean minus twice the
ordered pair-sum height dispersion. -/
theorem fourRateSchurBoundaryLogCurvature_eq_complementaryFisher_sub_dispersion
    {β : Type*} [Fintype β]
    (weight selectedHeight selectedFisher complementaryFisher : β → ℝ)
    (totalFisher : ℝ) (hweight : ∑ b, weight b = 1)
    (htotal : ∀ b, selectedFisher b + complementaryFisher b = totalFisher) :
    fourRateSchurBoundaryLogCurvature
        weight selectedHeight selectedFisher totalFisher =
      -2 * complementaryFisherMean weight complementaryFisher -
        2 * normalizedFinitePairDispersion weight selectedHeight := by
  have hcomp :
      complementaryFisherMean weight complementaryFisher =
        totalFisher - ∑ b, weight b * selectedFisher b := by
    rw [complementaryFisherMean]
    calc
      (∑ b, weight b * complementaryFisher b) =
          ∑ b, weight b * (totalFisher - selectedFisher b) := by
            apply Finset.sum_congr rfl
            intro b _hb
            rw [← htotal b]
            ring
      _ = totalFisher * (∑ b, weight b) -
          ∑ b, weight b * selectedFisher b := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro b _hb
            ring
      _ = totalFisher - ∑ b, weight b * selectedFisher b := by
            rw [hweight]
            ring
  have hdisp := HTGeometry.normalizedWeight_pairwiseSqGap_eq_two_mul_variance
    weight selectedHeight hweight
  rw [fourRateSchurBoundaryLogCurvature, hcomp,
    normalizedFinitePairDispersion, hdisp, normalizedFiniteVariance]
  ring

/-- The unique cumulant correction which removes the pair-sum height dispersion. -/
def fourRateSchurCumulantCorrectedFisher {β : Type*} [Fintype β]
    (weight selectedHeight selectedFisher : β → ℝ) (totalFisher : ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
      fourRateSchurBoundaryLogCurvature
        weight selectedHeight selectedFisher totalFisher -
    normalizedFinitePairDispersion weight selectedHeight

/-- The cumulant-corrected Schur curvature is exactly the complementary Fisher mean. -/
theorem fourRateSchurCumulantCorrectedFisher_eq_complementaryFisherMean
    {β : Type*} [Fintype β]
    (weight selectedHeight selectedFisher complementaryFisher : β → ℝ)
    (totalFisher : ℝ) (hweight : ∑ b, weight b = 1)
    (htotal : ∀ b, selectedFisher b + complementaryFisher b = totalFisher) :
    fourRateSchurCumulantCorrectedFisher
        weight selectedHeight selectedFisher totalFisher =
      complementaryFisherMean weight complementaryFisher := by
  rw [fourRateSchurCumulantCorrectedFisher,
    fourRateSchurBoundaryLogCurvature_eq_complementaryFisher_sub_dispersion
      weight selectedHeight selectedFisher complementaryFisher totalFisher hweight htotal]
  ring

/-- Strict negativity: positive pair weights and positive complementary Fisher clocks make every
four-rate Schur boundary cell strictly log-concave. -/
theorem fourRateSchurBoundaryLogCurvature_neg
    {β : Type*} [Fintype β] [Nonempty β]
    (weight selectedHeight selectedFisher complementaryFisher : β → ℝ)
    (totalFisher : ℝ) (hweight : ∑ b, weight b = 1)
    (htotal : ∀ b, selectedFisher b + complementaryFisher b = totalFisher)
    (hwpos : ∀ b, 0 < weight b) (hFpos : ∀ b, 0 < complementaryFisher b) :
    fourRateSchurBoundaryLogCurvature
        weight selectedHeight selectedFisher totalFisher < 0 := by
  rw [fourRateSchurBoundaryLogCurvature_eq_complementaryFisher_sub_dispersion
    weight selectedHeight selectedFisher complementaryFisher totalFisher hweight htotal]
  have hmean : 0 < complementaryFisherMean weight complementaryFisher := by
    unfold complementaryFisherMean
    exact Finset.sum_pos (fun b _hb => mul_pos (hwpos b) (hFpos b)) Finset.univ_nonempty
  have hdisp : 0 ≤ normalizedFinitePairDispersion weight selectedHeight := by
    unfold normalizedFinitePairDispersion
    exact Finset.sum_nonneg fun b _hb => Finset.sum_nonneg fun c _hc =>
      mul_nonneg (mul_nonneg (hwpos b).le (hwpos c).le) (sq_nonneg _)
  linarith

/-! ## Derivation from the source-selected formal boundary partition jets -/

/-- Zeroth jet of the Cauchy--Binet boundary-pair partition. -/
def boundaryPairPartitionJetZero {β : Type*} [Fintype β]
    (rawWeight : β → ℝ) : ℝ :=
  ∑ b, rawWeight b

/-- First jet.  Each squared two-column amplitude has logarithmic velocity
`-2 * selectedHeight`. -/
def boundaryPairPartitionJetOne {β : Type*} [Fintype β]
    (rawWeight selectedHeight : β → ℝ) : ℝ :=
  ∑ b, -2 * selectedHeight b * rawWeight b

/-- Second jet.  The source identity
`F''/F - (F'/F)^2 = -kappa` gives the coefficient
`4 * selectedHeight^2 - 2 * selectedFisher` for a squared pair amplitude. -/
def boundaryPairPartitionJetTwo {β : Type*} [Fintype β]
    (rawWeight selectedHeight selectedFisher : β → ℝ) : ℝ :=
  ∑ b, (4 * selectedHeight b ^ 2 - 2 * selectedFisher b) * rawWeight b

/-- Literal logarithmic curvature obtained from the three boundary partition jets. -/
def boundaryPairPartitionLogCurvatureFromJets {β : Type*} [Fintype β]
    (rawWeight selectedHeight selectedFisher : β → ℝ) : ℝ :=
  boundaryPairPartitionJetTwo rawWeight selectedHeight selectedFisher /
      boundaryPairPartitionJetZero rawWeight -
    (boundaryPairPartitionJetOne rawWeight selectedHeight /
      boundaryPairPartitionJetZero rawWeight) ^ 2

/-- Literal boundary logarithmic curvature of the four-rate Schur quotient.  The full four-column
numerator contributes `-2 * totalFisher`; the denominator is the boundary-pair partition. -/
def fourRateSchurBoundaryLogCurvatureFromJets {β : Type*} [Fintype β]
    (rawWeight selectedHeight selectedFisher : β → ℝ) (totalFisher : ℝ) : ℝ :=
  -2 * totalFisher -
    boundaryPairPartitionLogCurvatureFromJets
      rawWeight selectedHeight selectedFisher

private theorem sum_div_mul_eq_div_sum_mul
    {β : Type*} [Fintype β] (rawWeight value : β → ℝ) (z : ℝ) :
    (∑ b, rawWeight b / z * value b) =
      (∑ b, rawWeight b * value b) / z := by
  calc
    (∑ b, rawWeight b / z * value b) =
        ∑ b, (rawWeight b * value b) / z := by
          apply Finset.sum_congr rfl
          intro b _hb
          ring
    _ = (∑ b, rawWeight b * value b) / z := by
          rw [← Finset.sum_div]

/-- The jet computation, rather than a definition, produces the normalized-weight curvature. -/
theorem fourRateSchurBoundaryLogCurvatureFromJets_eq
    {β : Type*} [Fintype β]
    (rawWeight selectedHeight selectedFisher : β → ℝ) (totalFisher : ℝ) :
    fourRateSchurBoundaryLogCurvatureFromJets
        rawWeight selectedHeight selectedFisher totalFisher =
      fourRateSchurBoundaryLogCurvature
        (fun b => rawWeight b / boundaryPairPartitionJetZero rawWeight)
        selectedHeight selectedFisher totalFisher := by
  have hOne :
      boundaryPairPartitionJetOne rawWeight selectedHeight =
        -2 * ∑ b, rawWeight b * selectedHeight b := by
    rw [boundaryPairPartitionJetOne, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  have hTwo :
      boundaryPairPartitionJetTwo rawWeight selectedHeight selectedFisher =
        4 * (∑ b, rawWeight b * selectedHeight b ^ 2) -
          2 * (∑ b, rawWeight b * selectedFisher b) := by
    rw [boundaryPairPartitionJetTwo, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  rw [fourRateSchurBoundaryLogCurvatureFromJets,
    boundaryPairPartitionLogCurvatureFromJets,
    hOne, hTwo, boundaryPairPartitionJetZero,
    fourRateSchurBoundaryLogCurvature, normalizedFiniteVariance]
  rw [sum_div_mul_eq_div_sum_mul rawWeight selectedFisher]
  rw [sum_div_mul_eq_div_sum_mul rawWeight selectedHeight]
  rw [sum_div_mul_eq_div_sum_mul rawWeight (fun b => selectedHeight b ^ 2)]
  ring

/-! ## The actual Gamma-sewn four-rate boundary object -/

/-- Raw positive Cauchy--Binet weight of one boundary pair, including the two Gamma-sewn Rees
amplitudes. -/
def gammaSewnFourRateBoundaryPairRawWeight
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) : ℝ :=
  twoBoundaryCauchyPairPluckerSq a
      (rate (fourRatePairLeft s)) (rate (fourRatePairRight s)) *
    (gammaSewnMobiusApertureBoundaryAmplitude (cell (fourRatePairLeft s)).1 *
      gammaSewnMobiusApertureBoundaryAmplitude (cell (fourRatePairRight s)).1) ^ 2

/-- The six boundary minors normalized to a probability packet. -/
def gammaSewnFourRateBoundaryPairProbability
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) : ℝ :=
  gammaSewnFourRateBoundaryPairRawWeight a rate cell s /
    ∑ t, gammaSewnFourRateBoundaryPairRawWeight a rate cell t

/-- Selected midpoint-height sum on one boundary pair. -/
def gammaSewnFourRateSelectedHeight
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) : ℝ :=
  fourRateSelectedSum
    (fun i => gammaSewnMobiusApertureCellMidHeight (cell i).1 (cell i).2) s

/-- Complementary midpoint-height sum. -/
def gammaSewnFourRateComplementaryHeight
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) : ℝ :=
  fourRateComplementarySum
    (fun i => gammaSewnMobiusApertureCellMidHeight (cell i).1 (cell i).2) s

/-- Selected Gamma-sewn Fisher-clock sum on one boundary pair. -/
def gammaSewnFourRateSelectedFisher
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) : ℝ :=
  fourRateSelectedSum
    (fun i => gammaSewnMobiusApertureBoundaryFisherClock (cell i).1) s

/-- Complementary Gamma-sewn Fisher-clock sum. -/
def gammaSewnFourRateComplementaryFisher
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) : ℝ :=
  fourRateComplementarySum
    (fun i => gammaSewnMobiusApertureBoundaryFisherClock (cell i).1) s

/-- Total Fisher clock of the four source rates. -/
def gammaSewnFourRateTotalFisher (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  fourRateTotalSum
    (fun i => gammaSewnMobiusApertureBoundaryFisherClock (cell i).1)

theorem gammaSewnMobiusApertureBoundaryFisherClock_pos (p : Nat.Primes) :
    0 < gammaSewnMobiusApertureBoundaryFisherClock p := by
  unfold gammaSewnMobiusApertureBoundaryFisherClock
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  exact mul_pos (by norm_num) (sq_pos_of_pos (Real.log_pos hp))

theorem gammaSewnFourRateSelectedFisher_add_complementaryFisher
    (cell : Fin 4 → Nat.Primes × ℕ) (s : Fin 6) :
    gammaSewnFourRateSelectedFisher cell s +
        gammaSewnFourRateComplementaryFisher cell s =
      gammaSewnFourRateTotalFisher cell := by
  exact fourRateSelectedSum_add_complementarySum
    (fun i => gammaSewnMobiusApertureBoundaryFisherClock (cell i).1) s

/-- The individual two-jet self term cancels in logarithmic curvature, leaving exactly the
prime-only Fisher clock. -/
theorem gammaSewnBoundaryTwoJetLogCurvature_eq_neg_fisher
    (p : Nat.Primes) (e : ℕ) :
    (gammaSewnMobiusApertureCellMidHeight p e ^ 2 -
        gammaSewnMobiusApertureBoundaryFisherClock p) -
      (-gammaSewnMobiusApertureCellMidHeight p e) ^ 2 =
        -gammaSewnMobiusApertureBoundaryFisherClock p := by
  ring

theorem gammaSewnFourRateBoundaryPairRawWeight_pos
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) (s : Fin 6) :
    0 < gammaSewnFourRateBoundaryPairRawWeight a rate cell s := by
  unfold gammaSewnFourRateBoundaryPairRawWeight
  apply mul_pos
  · apply twoBoundaryCauchyPairPluckerSq_pos ha
    · exact hrate.ne (fourRatePairLeft_ne_right s)
    · exact hboundary _
    · exact hboundary _
  · apply sq_pos_of_pos
    exact mul_pos
      (gammaSewnMobiusApertureBoundaryAmplitude_pos _)
      (gammaSewnMobiusApertureBoundaryAmplitude_pos _)

theorem gammaSewnFourRateBoundaryPairPartition_pos
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) :
    0 < ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s := by
  exact Finset.sum_pos
    (fun s _hs => gammaSewnFourRateBoundaryPairRawWeight_pos ha hrate hboundary s)
    Finset.univ_nonempty

theorem sum_gammaSewnFourRateBoundaryPairProbability
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    ∑ s, gammaSewnFourRateBoundaryPairProbability a rate cell s = 1 := by
  unfold gammaSewnFourRateBoundaryPairProbability
  rw [← Finset.sum_div]
  exact div_self hpartition

theorem gammaSewnFourRateBoundaryPairProbability_pos
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) (s : Fin 6) :
    0 < gammaSewnFourRateBoundaryPairProbability a rate cell s := by
  unfold gammaSewnFourRateBoundaryPairProbability
  exact div_pos
    (gammaSewnFourRateBoundaryPairRawWeight_pos ha hrate hboundary s)
    (gammaSewnFourRateBoundaryPairPartition_pos ha hrate hboundary)

/-- Boundary logarithmic curvature of the source-selected four-rate Gamma-sewn Schur jet.  Its
identification with derivatives of the analytic normalized feature uses the separate boundary-jet
extension theorem. -/
def gammaSewnFourRateSchurBoundaryLogCurvature
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  fourRateSchurBoundaryLogCurvatureFromJets
    (gammaSewnFourRateBoundaryPairRawWeight a rate cell)
    (gammaSewnFourRateSelectedHeight cell)
    (gammaSewnFourRateSelectedFisher cell)
    (gammaSewnFourRateTotalFisher cell)

/-- **Source-specific four-rate curvature law.**  The literal Cauchy boundary weights split the
Schur curvature into complementary Gamma Fisher mass and midpoint-pair dispersion. -/
theorem gammaSewnFourRateSchurBoundaryLogCurvature_eq
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    gammaSewnFourRateSchurBoundaryLogCurvature a rate cell =
      -2 * complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) -
      2 * normalizedFinitePairDispersion
        (gammaSewnFourRateBoundaryPairProbability a rate cell)
        (gammaSewnFourRateSelectedHeight cell) := by
  rw [gammaSewnFourRateSchurBoundaryLogCurvature,
    fourRateSchurBoundaryLogCurvatureFromJets_eq]
  change fourRateSchurBoundaryLogCurvature
      (gammaSewnFourRateBoundaryPairProbability a rate cell)
      (gammaSewnFourRateSelectedHeight cell)
      (gammaSewnFourRateSelectedFisher cell)
      (gammaSewnFourRateTotalFisher cell) = _
  apply fourRateSchurBoundaryLogCurvature_eq_complementaryFisher_sub_dispersion
  · exact sum_gammaSewnFourRateBoundaryPairProbability hpartition
  · exact gammaSewnFourRateSelectedFisher_add_complementaryFisher cell

/-- The four-rate Schur source jet is strictly log-concave at the Rees boundary. -/
theorem gammaSewnFourRateSchurBoundaryLogCurvature_neg
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (ha : a ≠ 0) (hrate : Function.Injective rate)
    (hboundary : ∀ i, rate i ^ 2 - a ^ 2 ≠ 0) :
    gammaSewnFourRateSchurBoundaryLogCurvature a rate cell < 0 := by
  rw [gammaSewnFourRateSchurBoundaryLogCurvature,
    fourRateSchurBoundaryLogCurvatureFromJets_eq]
  change fourRateSchurBoundaryLogCurvature
      (gammaSewnFourRateBoundaryPairProbability a rate cell)
      (gammaSewnFourRateSelectedHeight cell)
      (gammaSewnFourRateSelectedFisher cell)
      (gammaSewnFourRateTotalFisher cell) < 0
  apply fourRateSchurBoundaryLogCurvature_neg
    (gammaSewnFourRateBoundaryPairProbability a rate cell)
    (gammaSewnFourRateSelectedHeight cell)
    (gammaSewnFourRateSelectedFisher cell)
    (gammaSewnFourRateComplementaryFisher cell)
    (gammaSewnFourRateTotalFisher cell)
  · exact sum_gammaSewnFourRateBoundaryPairProbability
      (gammaSewnFourRateBoundaryPairPartition_pos ha hrate hboundary).ne'
  · exact gammaSewnFourRateSelectedFisher_add_complementaryFisher cell
  · exact gammaSewnFourRateBoundaryPairProbability_pos ha hrate hboundary
  · intro s
    unfold gammaSewnFourRateComplementaryFisher fourRateComplementarySum
    exact add_pos
      (gammaSewnMobiusApertureBoundaryFisherClock_pos _)
      (gammaSewnMobiusApertureBoundaryFisherClock_pos _)

/-- Cumulant-corrected boundary Fisher channel of the actual four-rate Schur cell. -/
def gammaSewnFourRateSchurCorrectedFisher
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) : ℝ :=
  fourRateSchurCumulantCorrectedFisher
    (gammaSewnFourRateBoundaryPairProbability a rate cell)
    (gammaSewnFourRateSelectedHeight cell)
    (gammaSewnFourRateSelectedFisher cell)
    (gammaSewnFourRateTotalFisher cell)

/-- The forced correction isolates exactly the complementary prime-only Fisher clock. -/
theorem gammaSewnFourRateSchurCorrectedFisher_eq
    {a : ℝ} {rate : Fin 4 → ℝ} {cell : Fin 4 → Nat.Primes × ℕ}
    (hpartition : ∑ s, gammaSewnFourRateBoundaryPairRawWeight a rate cell s ≠ 0) :
    gammaSewnFourRateSchurCorrectedFisher a rate cell =
      complementaryFisherMean
        (gammaSewnFourRateBoundaryPairProbability a rate cell)
        (gammaSewnFourRateComplementaryFisher cell) := by
  unfold gammaSewnFourRateSchurCorrectedFisher
  apply fourRateSchurCumulantCorrectedFisher_eq_complementaryFisherMean
  · exact sum_gammaSewnFourRateBoundaryPairProbability hpartition
  · exact gammaSewnFourRateSelectedFisher_add_complementaryFisher cell

end

end RHTower
