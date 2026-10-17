import GaloisForLFunctions.HTGeometry.FiniteRealAtomicMeasure
import GaloisForLFunctions.RHTower.XiBernsteinIndexAsymptotic
import GaloisForLFunctions.RHTower.XiBernsteinOccupationWeights
import Mathlib.Topology.Algebra.Indicator

/-!
# Weak limits of the actual Bernstein index measures

The actual source index measures converge weakly to the finite positive maximal-divisor
measure. Every measurable window avoiding its atomic boundary has the exact mass limit.
-/

open Filter Topology MeasureTheory
open scoped BigOperators Real unitInterval
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The index measure formed directly from the actual PA source coefficients. -/
def primeArchEndpointBernsteinIndexMeasure (B : ℝ) (n : ℕ) : FiniteMeasure I :=
  finiteRealAtomicMeasure Finset.univ (fun k : Fin (n + 1) => bernstein.z k)
    (fun k => Real.sqrt n / (B ^ 2) ^ n * ‖primeArchEndpointBernsteinPacket n k‖ ^ 2)

/-- The finite positive divisor measure exposed by the maximal packet. -/
def xiEndpointBernsteinOccupationMeasure (D : Finset XiZeroCopy) : FiniteMeasure I :=
  finiteRealAtomicMeasure (xiEndpointCoordinateSet D) bernsteinAffineOccupation
    (fun u => ‖xiEndpointCoordinateWeight D u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u)

theorem integral_primeArchEndpointBernsteinIndexMeasure (B : ℝ) (n : ℕ) (g : I → ℝ) :
    (∫ p, g p ∂(primeArchEndpointBernsteinIndexMeasure B n : Measure I)) =
      Real.sqrt n / (B ^ 2) ^ n * primeArchEndpointBernsteinIndexEnergy g n := by
  rw [primeArchEndpointBernsteinIndexMeasure, integral_finiteRealAtomicMeasure
    _ _ _ (by intro k hk; positivity), primeArchEndpointBernsteinIndexEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem integral_xiEndpointBernsteinOccupationMeasure
    (D : Finset XiZeroCopy) (hpos : ∀ u ∈ xiEndpointCoordinateSet D,
      0 ≤ bernsteinAffineRowHalfOrderConstant u) (g : I → ℝ) :
    (∫ p, g p ∂(xiEndpointBernsteinOccupationMeasure D : Measure I)) =
      ∑ u ∈ xiEndpointCoordinateSet D, ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
        bernsteinAffineRowHalfOrderConstant u * g (bernsteinAffineOccupation u) := by
  exact integral_finiteRealAtomicMeasure _ _ _
    (fun u hu => mul_nonneg (sq_nonneg _) (hpos u hu)) g

theorem xiEndpointBernsteinOccupationMeasure_singleton
    (D : Finset XiZeroCopy) (hpos : ∀ u ∈ xiEndpointCoordinateSet D,
      0 ≤ bernsteinAffineRowHalfOrderConstant u) (p : I) :
    (xiEndpointBernsteinOccupationMeasure D : Measure I).real {p} =
      xiEndpointOccupationAtomWeight D p := by
  rw [xiEndpointBernsteinOccupationMeasure, real_finiteRealAtomicMeasure_apply
    _ _ _ (fun u hu => mul_nonneg (sq_nonneg _) (hpos u hu)) (measurableSet_singleton p)]
  rfl

private theorem halfOrderConstant_nonneg_of_maximalPacket
    (D : Finset XiZeroCopy) {B : ℝ} (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) :
    ∀ u ∈ xiEndpointCoordinateSet D, 0 ≤ bernsteinAffineRowHalfOrderConstant u := by
  intro u hu
  obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
  have him : u.im ≠ 0 := by
    rw [← hqu]
    exact (xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q
      (by rw [hD q hq]; exact hB)).2
  exact (bernsteinAffineRowHalfOrderConstant_pos
    (fun heq => him (by rw [heq]; rfl)) (fun heq => him (by rw [heq]; rfl))).le

/-- Weak convergence of the actual source index measures in Mathlib's finite-measure topology. -/
theorem tendsto_primeArchEndpointBernsteinIndexMeasure_of_maximalPacket
    (D : Finset XiZeroCopy) {B beta : ℝ} (hB : 1 < B)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (htail : ∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) :
    Tendsto (primeArchEndpointBernsteinIndexMeasure B) atTop
      (nhds (xiEndpointBernsteinOccupationMeasure D)) := by
  have hpos := halfOrderConstant_nonneg_of_maximalPacket D hB hD
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro g
  simp only [integral_primeArchEndpointBernsteinIndexMeasure,
    integral_xiEndpointBernsteinOccupationMeasure D hpos]
  exact tendsto_primeArchEndpointBernsteinIndexEnergy_of_maximalPacket D hB hbeta0 hbeta
    hD htail (norm_nonneg g) (fun p => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm p)
    (fun u hu => g.continuous.continuousAt)

/-- Any measurable index window whose boundary misses the limiting occupation points has the
corresponding exact mass limit, including interval windows. -/
theorem tendsto_primeArchEndpointBernsteinIndexMeasure_window
    (D : Finset XiZeroCopy) {B beta : ℝ} (hB : 1 < B)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (htail : ∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta)
    {S : Set I} (hS : MeasurableSet S)
    (hboundary : ∀ u ∈ xiEndpointCoordinateSet D, bernsteinAffineOccupation u ∉ frontier S) :
    Tendsto (fun n => (primeArchEndpointBernsteinIndexMeasure B n : Measure I).real S) atTop
      (nhds ((xiEndpointBernsteinOccupationMeasure D : Measure I).real S)) := by
  classical
  have h := tendsto_primeArchEndpointBernsteinIndexEnergy_of_maximalPacket D hB hbeta0 hbeta
    hD htail (g := S.indicator (1 : I → ℝ)) (M := 1) (by norm_num)
    (by intro p; by_cases hp : p ∈ S <;> simp [hp])
    (fun u hu => continuousOn_const.continuousAt_indicator (hboundary u hu))
  convert h using 1
  · ext n
    rw [← integral_indicator_one hS, integral_primeArchEndpointBernsteinIndexMeasure]
  · rw [← integral_indicator_one hS, integral_xiEndpointBernsteinOccupationMeasure
      D (halfOrderConstant_nonneg_of_maximalPacket D hB hD)]

end
end RHTower
