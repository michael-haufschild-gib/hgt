import GaloisForLFunctions.RHTower.SteinhausEulerSpatialEnvelope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# One exceptional event for all selected Steinhaus Euler fields

BAG C20.10. A geometric aggregate of the proved spatial envelopes is measurable
and has a cutoff-independent finite expectation. It dominates the actual Euler
field simultaneously at every selected cutoff and every point of the unit vertical
segment. Markov bounds the single exceptional event. No variance clock, tilted
barrier identification, or recurrence premise is assumed here.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

/-- The spatial expectation constant, independent of the cutoff sequence. -/
def steinhausEulerGlobalEnvelopeConstant : ℝ :=
  128 * steinhausEulerSpatialMomentConstant / Real.pi

/-- A geometric aggregate controls the spatial field at all selected cutoffs. -/
def steinhausEulerGlobalEnvelope (u : ℕ → ℕ) (ω : Omega) : ℝ≥0∞ :=
  ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1) *
    (ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2))⁻¹ *
      steinhausEulerSpatialEnvelope (u j) ω

theorem steinhausEulerGlobalEnvelopeConstant_pos : 0 < steinhausEulerGlobalEnvelopeConstant := by
  unfold steinhausEulerGlobalEnvelopeConstant
  have := steinhausEulerSpatialMomentConstant_pos
  positivity

theorem measurable_steinhausEulerGlobalEnvelope (u : ℕ → ℕ) :
    Measurable (steinhausEulerGlobalEnvelope u) := by
  apply Measurable.tsum
  intro j
  exact (measurable_steinhausEulerSpatialEnvelope (u j)).const_mul _

private theorem spatial_partition_sq_pos (N : ℕ) :
    0 < steinhausEulerPartition (Nat.primesBelow N) (1 / 2) ^ 2 := by
  have := one_le_steinhausEulerPartition_half N
  positivity

/-- All scales share one finite expectation bound. -/
theorem lintegral_steinhausEulerGlobalEnvelope_le (u : ℕ → ℕ) (hu : ∀ j, 3 ≤ u j) :
    (∫⁻ ω, steinhausEulerGlobalEnvelope u ω ∂steinhausMeasure) ≤
      ENNReal.ofReal steinhausEulerGlobalEnvelopeConstant := by
  have hC := steinhausEulerGlobalEnvelopeConstant_pos
  unfold steinhausEulerGlobalEnvelope
  rw [lintegral_tsum (fun j =>
    ((measurable_steinhausEulerSpatialEnvelope (u j)).const_mul _).aemeasurable)]
  simp_rw [lintegral_const_mul _ (measurable_steinhausEulerSpatialEnvelope _)]
  calc
    _ ≤ ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1) *
        (ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2))⁻¹ *
          ENNReal.ofReal (steinhausEulerGlobalEnvelopeConstant *
            steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2) :=
      ENNReal.tsum_le_tsum fun j => mul_le_mul_right
        (lintegral_steinhausEulerSpatialEnvelope_le (hu j)) _
    _ = ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1) *
        ENNReal.ofReal steinhausEulerGlobalEnvelopeConstant := by
      apply tsum_congr
      intro j
      have hM0 := ENNReal.ofReal_ne_zero_iff.mpr (spatial_partition_sq_pos (u j))
      rw [ENNReal.ofReal_mul hC.le]
      calc
        _ = (2⁻¹ : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal steinhausEulerGlobalEnvelopeConstant *
            ((ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2))⁻¹ *
              ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2)) := by ac_rfl
        _ = _ := by rw [ENNReal.inv_mul_cancel hM0 ENNReal.ofReal_ne_top, mul_one]
    _ = _ := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_add_one]
      norm_num
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

private theorem globalEnvelope_term_le (u : ℕ → ℕ) (ω : Omega) (j : ℕ) :
    steinhausEulerSpatialEnvelope (u j) ω ≤
      ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2) *
        (2 : ℝ≥0∞) ^ (j + 1) * steinhausEulerGlobalEnvelope u ω := by
  have hM0 := ENNReal.ofReal_ne_zero_iff.mpr (spatial_partition_sq_pos (u j))
  have ht0 : (2 : ℝ≥0∞) ^ (j + 1) ≠ 0 := by simp
  have htT : (2 : ℝ≥0∞) ^ (j + 1) ≠ ∞ := by simp
  have hterm : (2⁻¹ : ℝ≥0∞) ^ (j + 1) *
      (ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2))⁻¹ *
        steinhausEulerSpatialEnvelope (u j) ω ≤ steinhausEulerGlobalEnvelope u ω :=
    ENNReal.le_tsum j
  calc
    _ = ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2) *
        (2 : ℝ≥0∞) ^ (j + 1) *
        ((2⁻¹ : ℝ≥0∞) ^ (j + 1) *
          (ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2))⁻¹ *
            steinhausEulerSpatialEnvelope (u j) ω) := by
      rw [← ENNReal.inv_pow]
      have heq : ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2) *
          (2 : ℝ≥0∞) ^ (j + 1) *
          (((2 : ℝ≥0∞) ^ (j + 1))⁻¹ *
            (ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2))⁻¹ *
              steinhausEulerSpatialEnvelope (u j) ω) =
          (ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2) *
            (ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2))⁻¹) *
          ((2 : ℝ≥0∞) ^ (j + 1) * ((2 : ℝ≥0∞) ^ (j + 1))⁻¹) *
            steinhausEulerSpatialEnvelope (u j) ω := by ac_rfl
      rw [heq, ENNReal.mul_inv_cancel hM0 ENNReal.ofReal_ne_top,
        ENNReal.mul_inv_cancel ht0 htT, one_mul, one_mul]
    _ ≤ _ := mul_le_mul_right hterm _

/-- One random variable dominates every selected field on the whole unit segment. -/
theorem norm_sq_le_steinhausEulerGlobalEnvelope (u : ℕ → ℕ) (hu : ∀ j, 3 ≤ u j)
    (ω : Omega) (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ENNReal.ofReal (‖steinhausFiniteEulerProduct (Nat.primesBelow (u j))
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ω‖ ^ 2) ≤
      ENNReal.ofReal (steinhausEulerPartition (Nat.primesBelow (u j)) (1 / 2) ^ 2) *
        (2 : ℝ≥0∞) ^ (j + 1) * steinhausEulerGlobalEnvelope u ω :=
  (norm_sq_le_steinhausEulerSpatialEnvelope (hu j) ω ht).trans (globalEnvelope_term_le u ω j)

/-- A uniform Markov bound for the single exceptional event. -/
theorem measure_steinhausEulerGlobalEnvelope_ge_le (u : ℕ → ℕ) (hu : ∀ j, 3 ≤ u j)
    {R : ℝ} (hR : 0 < R) :
    steinhausMeasure {ω | ENNReal.ofReal R ≤ steinhausEulerGlobalEnvelope u ω} ≤
      ENNReal.ofReal (steinhausEulerGlobalEnvelopeConstant / R) := by
  calc
    _ ≤ (∫⁻ ω, steinhausEulerGlobalEnvelope u ω ∂steinhausMeasure) / ENNReal.ofReal R :=
      meas_ge_le_lintegral_div (measurable_steinhausEulerGlobalEnvelope u).aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr hR) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal steinhausEulerGlobalEnvelopeConstant / ENNReal.ofReal R :=
      ENNReal.div_le_div_right (lintegral_steinhausEulerGlobalEnvelope_le u hu) _
    _ = _ := (ENNReal.ofReal_div_of_pos hR).symm

end RHTower
