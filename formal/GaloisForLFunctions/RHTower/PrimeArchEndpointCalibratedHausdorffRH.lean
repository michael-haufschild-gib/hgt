import GaloisForLFunctions.RHTower.PrimeArchHausdorffBernsteinKMSRH
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

open scoped BigOperators Polynomial
open Polynomial Filter Topology

namespace RHTower
noncomputable section
open HTGeometry

/-- Complementary Hausdorff differences calibrated to a support radius `R`. -/
def scaledHausdorffMomentDifference (R : ℝ) (m : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => m k
  | r + 1 => R * scaledHausdorffMomentDifference R m k r -
      scaledHausdorffMomentDifference R m (k + 1) r

/-- Complete positivity of the Hausdorff differences calibrated to radius `R`. -/
def ScaledHausdorffMomentDifferencesNonnegative (R : ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ k r : ℕ, 0 ≤ scaledHausdorffMomentDifference R m k r

/-- Normalize a moment sequence by the support radius. -/
def radiusNormalizedMoment (R : ℝ) (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  m n / R ^ n

/-- Calibrated differences become ordinary unit-interval differences after radius normalization. -/
theorem hausdorffMomentDifference_radiusNormalizedMoment
    {R : ℝ} (hR : 0 < R) (m : ℕ → ℝ) (k r : ℕ) :
    hausdorffMomentDifference (radiusNormalizedMoment R m) k r =
      scaledHausdorffMomentDifference R m k r / R ^ (k + r) := by
  induction r generalizing k with
  | zero => simp [hausdorffMomentDifference, scaledHausdorffMomentDifference,
      radiusNormalizedMoment]
  | succ r ih =>
      rw [hausdorffMomentDifference, scaledHausdorffMomentDifference,
        ih k, ih (k + 1)]
      have hR0 : R ≠ 0 := hR.ne'
      field_simp [hR0]
      ring

/-- Calibrated difference positivity implies ordinary Hausdorff positivity of the normalized
sequence. -/
theorem hausdorffMomentDifferencesNonnegative_radiusNormalizedMoment
    {R : ℝ} (hR : 0 < R) {m : ℕ → ℝ}
    (h : ScaledHausdorffMomentDifferencesNonnegative R m) :
    HausdorffMomentDifferencesNonnegative (radiusNormalizedMoment R m) := by
  intro k r
  rw [hausdorffMomentDifference_radiusNormalizedMoment hR]
  exact div_nonneg (h k r) (pow_nonneg hR.le _)

/-- Rescale a finite positive-atomic moment sequence by multiplying its nodes by `R`. -/
theorem finitePositiveAtomicMomentSequence_radiusRescale
    {R : ℝ} (hR : 0 ≤ R) {m : ℕ → ℝ}
    (h : FinitePositiveAtomicMomentSequence m) :
    FinitePositiveAtomicMomentSequence (fun n => R ^ n * m n) := by
  obtain ⟨d, mass, node, hmass, hnode, rfl⟩ := h
  refine ⟨d, mass, fun i => R * node i, hmass,
    fun i => mul_nonneg hR (hnode i), ?_⟩
  funext n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  ring

/-- The normalized Hausdorff--Bernstein systems rescale to finite positive-atomic systems
converging to the original radius-`R` moment sequence. -/
theorem finitePositiveAtomicLocalMomentClosure_of_scaledHausdorffMomentDifferencesNonnegative
    {R : ℝ} (hR : 0 < R) {m : ℕ → ℝ}
    (h : ScaledHausdorffMomentDifferencesNonnegative R m) :
    FinitePositiveAtomicLocalMomentClosure m := by
  let s := radiusNormalizedMoment R m
  let b : ℕ → ℕ → ℝ := fun N n => R ^ n * hausdorffBernsteinAtomicMoment s N n
  have hs : HausdorffMomentDifferencesNonnegative s :=
    hausdorffMomentDifferencesNonnegative_radiusNormalizedMoment hR h
  have hb : ∀ N, FinitePositiveAtomicMomentSequence (b N) := by
    intro N
    exact finitePositiveAtomicMomentSequence_radiusRescale hR.le
      (finitePositiveAtomicMomentSequence_hausdorffBernsteinAtomicMoment
        (hausdorffBernsteinNonnegative_of_momentDifferencesNonnegative hs) N)
  have htarget : (fun n => R ^ n * s n) = m := by
    funext n
    dsimp only [s, radiusNormalizedMoment]
    field_simp [hR.ne']
  apply finitePositiveAtomicLocalMomentClosure_of_tendsto hb
  rw [← htarget]
  apply tendsto_pi_nhds.mpr
  intro n
  exact (tendsto_hausdorffBernsteinAtomicMoment_coordinate s n).const_mul (R ^ n)

/-- Any positive-radius calibrated Hausdorff certificate for the normalized prime--Gamma moments
implies RH. -/
theorem riemannHypothesis_of_scaledPrimeArchHausdorffMomentDifferencesNonnegative
    {R : ℝ} (hR : 0 < R)
    (h : ScaledHausdorffMomentDifferencesNonnegative R normalizedPrimeArchMoment) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_primeArchFinitePositiveAtomicLocalMomentClosure
    (finitePositiveAtomicLocalMomentClosure_of_scaledHausdorffMomentDifferencesNonnegative hR h)

/-- The endpoint source itself determines the natural reciprocal-square support radius. -/
def primeArchEndpointHausdorffRadius : ℝ :=
  xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature)

theorem primeArchEndpointHausdorffRadius_pos : 0 < primeArchEndpointHausdorffRadius := by
  exact div_pos xiEndpointCompletedCurvature_pos
    (sub_pos.mpr xiEndpointCompletedCurvature_lt_one)

theorem primeArchEndpointHausdorffRadius_lt_one :
    primeArchEndpointHausdorffRadius < 1 := by
  rw [primeArchEndpointHausdorffRadius, div_lt_one
    (sub_pos.mpr xiEndpointCompletedCurvature_lt_one)]
  nlinarith [xiEndpointCompletedCurvature_lt_one_half]

/-- The endpoint height law puts every Xi thermal node below the source-calibrated radius. -/
theorem xiThermalNode_le_primeArchEndpointHausdorffRadius (q : XiZeroCopy) :
    xiThermalNode q ≤ primeArchEndpointHausdorffRadius := by
  let C := xiEndpointCompletedCurvature
  have hC : 0 < C := xiEndpointCompletedCurvature_pos
  have hC1 : 0 < 1 - C := sub_pos.mpr xiEndpointCompletedCurvature_lt_one
  have hheight := xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
  change 1 / C - 1 ≤ (q.1 : ℂ).im ^ (2 : ℕ) at hheight
  have hspec : (1 - C) / C ≤ ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    rw [norm_xiSpectralPoint, Complex.sq_norm, Complex.normSq_apply]
    norm_num
    have heq : (1 - C) / C = 1 / C - 1 := by field_simp
    rw [heq]
    nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  have hspecpos : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
    sq_pos_of_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))
  have hnorm : ‖xiZeroCopyReciprocalSquare q‖ ≤ C / (1 - C) := by
    rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, inv_pow]
    have hbasepos : 0 < (1 - C) / C := div_pos hC1 hC
    have hradius : C / (1 - C) = ((1 - C) / C)⁻¹ := by
      field_simp [hC.ne', hC1.ne']
    rw [hradius]
    exact (inv_le_inv₀ hspecpos hbasepos).2 hspec
  calc
    xiThermalNode q ≤ |xiThermalNode q| := le_abs_self _
    _ ≤ ‖xiZeroCopyReciprocalSquare q‖ :=
      Complex.abs_re_le_norm (xiZeroCopyReciprocalSquare q)
    _ ≤ C / (1 - C) := hnorm
    _ = primeArchEndpointHausdorffRadius := rfl

/-- Calibrated difference of a finite Xi thermal truncation. -/
theorem scaledHausdorffMomentDifference_xiThermalTruncation
    (R : ℝ) (N k r : ℕ) :
    scaledHausdorffMomentDifference R (xiThermalTruncation N) k r =
      ∑ j ∈ Finset.range N,
        xiThermalNode (xiThermalEnumeration j) ^ (k + 1) *
          (R - xiThermalNode (xiThermalEnumeration j)) ^ r := by
  induction r generalizing k with
  | zero =>
      simp only [scaledHausdorffMomentDifference, pow_zero, mul_one,
        xiThermalTruncation]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      exact mul_comm _ _
  | succ r ih =>
      rw [scaledHausdorffMomentDifference, ih k, ih (k + 1),
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring

/-- A radius upper bound on every thermal node makes each finite Xi truncation completely
Hausdorff-positive at that radius. -/
theorem scaledHausdorffMomentDifferencesNonnegative_xiThermalTruncation_of_node_le
    (R : ℝ) (hnode : ∀ q : XiZeroCopy, xiThermalNode q ≤ R) (N : ℕ) :
    ScaledHausdorffMomentDifferencesNonnegative R (xiThermalTruncation N) := by
  intro k r
  rw [scaledHausdorffMomentDifference_xiThermalTruncation]
  exact Finset.sum_nonneg fun j hj => mul_nonneg
    (pow_nonneg (xiThermalNode_pos _).le _)
    (pow_nonneg (sub_nonneg.mpr (hnode _)) _)

/-- Each finite Xi truncation is completely positive at the endpoint-calibrated radius. -/
theorem scaledHausdorffMomentDifferencesNonnegative_xiThermalTruncation (N : ℕ) :
    ScaledHausdorffMomentDifferencesNonnegative primeArchEndpointHausdorffRadius
      (xiThermalTruncation N) :=
  scaledHausdorffMomentDifferencesNonnegative_xiThermalTruncation_of_node_le
    primeArchEndpointHausdorffRadius
    xiThermalNode_le_primeArchEndpointHausdorffRadius N

/-- Calibrated differences are continuous under pointwise convergence. -/
theorem tendsto_scaledHausdorffMomentDifference_of_tendsto
    (R : ℝ) {m : ℕ → ℕ → ℝ} {target : ℕ → ℝ}
    (h : Tendsto m atTop (nhds target)) (k r : ℕ) :
    Tendsto (fun N => scaledHausdorffMomentDifference R (m N) k r) atTop
      (nhds (scaledHausdorffMomentDifference R target k r)) := by
  induction r generalizing k with
  | zero =>
      simpa only [scaledHausdorffMomentDifference] using (tendsto_pi_nhds.mp h) k
  | succ r ih =>
      simpa only [scaledHausdorffMomentDifference] using
        ((ih k).const_mul R).sub (ih (k + 1))


/-- Under RH, any radius dominating all thermal nodes gives complete calibrated source
finite-difference positivity. -/
theorem scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis_of_node_le
    (R : ℝ) (hnode : ∀ q : XiZeroCopy, xiThermalNode q ≤ R)
    (hRH : RiemannHypothesis) :
    ScaledHausdorffMomentDifferencesNonnegative R normalizedPrimeArchMoment := by
  intro k r
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_scaledHausdorffMomentDifference_of_tendsto R
      (tendsto_xiThermalTruncation_of_rh hRH) k r)
    (Eventually.of_forall fun N =>
      scaledHausdorffMomentDifferencesNonnegative_xiThermalTruncation_of_node_le
        R hnode N k r)

/-- At every positive radius containing the reciprocal-square thermal nodes, calibrated source
Hausdorff positivity is exactly RH. -/
theorem scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis_of_node_le
    {R : ℝ} (hR : 0 < R) (hnode : ∀ q : XiZeroCopy, xiThermalNode q ≤ R) :
    ScaledHausdorffMomentDifferencesNonnegative R normalizedPrimeArchMoment ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_scaledPrimeArchHausdorffMomentDifferencesNonnegative hR,
    scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis_of_node_le
      R hnode⟩

/-- RH supplies complete positivity at the exact endpoint-calibrated support radius. -/
theorem scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ScaledHausdorffMomentDifferencesNonnegative primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment :=
  scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis_of_node_le
    primeArchEndpointHausdorffRadius
    xiThermalNode_le_primeArchEndpointHausdorffRadius hRH

/-- **Endpoint-calibrated Hausdorff value law for RH.** -/
theorem scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis :
    ScaledHausdorffMomentDifferencesNonnegative primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment ↔
      RiemannHypothesis :=
  scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis_of_node_le
    primeArchEndpointHausdorffRadius_pos
    xiThermalNode_le_primeArchEndpointHausdorffRadius

/-- The exact source-calibrated radius is smaller than the rational endpoint radius `2/41`. -/
theorem primeArchEndpointHausdorffRadius_lt_two_over_fortyOne :
    primeArchEndpointHausdorffRadius < 2 / 41 := by
  rw [primeArchEndpointHausdorffRadius,
    div_lt_iff₀ (sub_pos.mpr xiEndpointCompletedCurvature_lt_one)]
  nlinarith [xiEndpointCompletedCurvature_lt_two_over_fortyThree]

/-- The exact prime--polar abscissa endpoint is equivalent to positivity of the source-calibrated
Hausdorff differences. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_scaledPrimeArchHausdorffMomentDifferencesNonnegative
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      ScaledHausdorffMomentDifferencesNonnegative primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans
    scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis.symm

end
end RHTower
