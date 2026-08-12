import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesReflectedCompactCarrier

/-!
# Squared reciprocal-gap Markov candidate for Route P

P-G70 produces a symmetric reciprocal-gap carrier.  The completed seam germ uses the square of
the centered coordinate, so the source-facing endpoint measure is its square pushforward: mass
`2 b_s/g_s` at `g_s⁻²`.  This file constructs that measure directly, proves compact positivity and
finiteness, identifies every moment, and proves the exact reflected-response law

`R_s^ref(z) = -z K_{ν_s}(z²)`.

At `s=1/2`, equality of this explicit source Markov germ with `completedSeamMomentGerm` is isolated
as the sole remaining all-degree identification gate; that equality implies RH through the
existing compact Markov capstone.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

noncomputable section
namespace RHTower

def gammaSewnMobiusApertureStokesSquaredWeight (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  2 * gammaSewnMobiusApertureStokesReflectedWeight s pk

def gammaSewnMobiusApertureStokesSquaredReciprocalGapNode
    (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusApertureStokesReciprocalGapNode s pk ^ 2

theorem gammaSewnMobiusApertureStokesSquaredWeight_pos
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusApertureStokesSquaredWeight s pk := by
  exact mul_pos (by norm_num) (gammaSewnMobiusApertureStokesReflectedWeight_pos hs pk)

theorem gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusApertureStokesSquaredReciprocalGapNode s pk := by
  exact sq_pos_of_pos (gammaSewnMobiusApertureStokesReciprocalGapNode_pos hs pk)

theorem gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesSquaredReciprocalGapNode s pk ≤
      ((Real.log 2)⁻¹) ^ 2 := by
  have hx0 := gammaSewnMobiusApertureStokesReciprocalGapNode_pos hs pk
  have hx := gammaSewnMobiusApertureStokesReciprocalGapNode_le hs hs1 pk
  have hB : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  rw [gammaSewnMobiusApertureStokesSquaredReciprocalGapNode]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hx0.le hB.le)]

theorem summable_gammaSewnMobiusApertureStokesSquaredWeight
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Summable (gammaSewnMobiusApertureStokesSquaredWeight s) := by
  have h := summable_gammaSewnMobiusApertureStokesDualFeatureCoefficient_div_gap hs hs1
  change Summable (fun pk : Nat.Primes × ℕ =>
    2 * (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk /
      gammaSewnMobiusApertureStokesGap s pk))
  exact h.mul_left 2

/-- Positive square-pushforward carrier: mass `2 b_s/g_s` at `g_s⁻²`. -/
def gammaSewnMobiusApertureStokesSquaredCompactCarrier (s : ℝ) : Measure ℝ :=
  Measure.sum fun pk : Nat.Primes × ℕ =>
    ENNReal.ofReal (gammaSewnMobiusApertureStokesSquaredWeight s pk) •
      Measure.dirac (gammaSewnMobiusApertureStokesSquaredReciprocalGapNode s pk)

theorem integrable_one_gammaSewnMobiusApertureStokesSquaredCompactCarrier
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Integrable (fun _ : ℝ => (1 : ℝ))
      (gammaSewnMobiusApertureStokesSquaredCompactCarrier s) := by
  rw [gammaSewnMobiusApertureStokesSquaredCompactCarrier]
  apply integrable_sum_dirac (fun pk => by simp [ENNReal.ofReal_ne_top])
  apply (summable_gammaSewnMobiusApertureStokesSquaredWeight hs hs1).congr
  intro pk
  rw [ENNReal.toReal_ofReal
    (gammaSewnMobiusApertureStokesSquaredWeight_pos hs pk).le]
  simp

theorem gammaSewnMobiusApertureStokesSquaredCompactCarrier_finite
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    IsFiniteMeasure (gammaSewnMobiusApertureStokesSquaredCompactCarrier s) := by
  exact (integrable_const_iff_isFiniteMeasure one_ne_zero).mp
    (integrable_one_gammaSewnMobiusApertureStokesSquaredCompactCarrier hs hs1)

theorem ae_gammaSewnMobiusApertureStokesSquaredCompactCarrier_mem_compact
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ y : ℝ ∂gammaSewnMobiusApertureStokesSquaredCompactCarrier s,
      0 ≤ y ∧ |y| ≤ ((Real.log 2)⁻¹) ^ 2 := by
  rw [gammaSewnMobiusApertureStokesSquaredCompactCarrier, Measure.ae_sum_iff]
  intro pk
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff
    (measurableSet_Ici.inter
      (measurableSet_le measurable_id.abs measurable_const))).2
    ⟨(gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos hs pk).le,
      by
        change |gammaSewnMobiusApertureStokesSquaredReciprocalGapNode s pk| ≤
          ((Real.log 2)⁻¹) ^ 2
        rw [abs_of_pos
          (gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos hs pk)]
        exact gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le hs hs1 pk⟩

theorem integrable_pow_gammaSewnMobiusApertureStokesSquaredCompactCarrier
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n)
      (gammaSewnMobiusApertureStokesSquaredCompactCarrier s) := by
  letI : IsFiniteMeasure (gammaSewnMobiusApertureStokesSquaredCompactCarrier s) :=
    gammaSewnMobiusApertureStokesSquaredCompactCarrier_finite hs hs1
  refine Integrable.of_bound (continuous_id.pow n).aestronglyMeasurable
    ((((Real.log 2)⁻¹) ^ 2) ^ n) ?_
  filter_upwards [ae_gammaSewnMobiusApertureStokesSquaredCompactCarrier_mem_compact hs hs1]
    with y hy
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg y) hy.2 n

/-- Exact all-degree moments of the explicit squared Stokes carrier. -/
theorem integral_pow_gammaSewnMobiusApertureStokesSquaredCompactCarrier_eq_tsum
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∫ y : ℝ, y ^ n ∂gammaSewnMobiusApertureStokesSquaredCompactCarrier s =
      ∑' pk : Nat.Primes × ℕ,
        gammaSewnMobiusApertureStokesSquaredWeight s pk *
          gammaSewnMobiusApertureStokesSquaredReciprocalGapNode s pk ^ n := by
  rw [gammaSewnMobiusApertureStokesSquaredCompactCarrier,
    integral_sum_dirac (fun pk => by simp [ENNReal.ofReal_ne_top])]
  apply tsum_congr
  intro pk
  rw [ENNReal.toReal_ofReal
    (gammaSewnMobiusApertureStokesSquaredWeight_pos hs pk).le]
  simp only [smul_eq_mul]

/-- Moment formula in physical Stokes variables: `2 sum b_s/g_s^(2n+1)`. -/
theorem integral_pow_gammaSewnMobiusApertureStokesSquaredCompactCarrier_eq_physical
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∫ y : ℝ, y ^ n ∂gammaSewnMobiusApertureStokesSquaredCompactCarrier s =
      2 * ∑' pk : Nat.Primes × ℕ,
        gammaSewnMobiusApertureStokesReflectedWeight s pk *
          gammaSewnMobiusApertureStokesReciprocalGapNode s pk ^ (2 * n) := by
  rw [integral_pow_gammaSewnMobiusApertureStokesSquaredCompactCarrier_eq_tsum hs]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro pk
  rw [gammaSewnMobiusApertureStokesSquaredWeight,
    gammaSewnMobiusApertureStokesSquaredReciprocalGapNode]
  ring_nf

/-- Same moment formula with reflected variables eliminated: `2 sum b_s/g_s^(2n+1)`. -/
theorem integral_pow_gammaSewnMobiusApertureStokesSquaredCompactCarrier_eq_euler
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∫ y : ℝ, y ^ n ∂gammaSewnMobiusApertureStokesSquaredCompactCarrier s =
      2 * ∑' pk : Nat.Primes × ℕ,
        gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk /
          gammaSewnMobiusApertureStokesGap s pk ^ (2 * n + 1) := by
  rw [integral_pow_gammaSewnMobiusApertureStokesSquaredCompactCarrier_eq_physical hs]
  congr 1
  apply tsum_congr
  intro pk
  rw [gammaSewnMobiusApertureStokesReflectedWeight,
    gammaSewnMobiusApertureStokesReciprocalGapNode]
  simp only [div_eq_mul_inv, inv_pow]
  rw [pow_succ]
  ring

private theorem summable_gammaSewnMobiusApertureStokesSquaredMarkovSeries
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {u : ℂ} (hu : ‖u‖ < 1 / (2 * (((Real.log 2)⁻¹) ^ 2))) :
    Summable (fun pk : Nat.Primes × ℕ =>
      (gammaSewnMobiusApertureStokesSquaredWeight s pk : ℂ) *
        (1 - (gammaSewnMobiusApertureStokesSquaredReciprocalGapNode s pk : ℂ) * u)⁻¹) := by
  have hB : 0 < ((Real.log 2)⁻¹) ^ 2 :=
    sq_pos_of_pos (inv_pos.mpr (Real.log_pos (by norm_num)))
  apply Summable.of_norm_bounded
    ((summable_gammaSewnMobiusApertureStokesSquaredWeight hs hs1).mul_left 2)
  intro pk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gammaSewnMobiusApertureStokesSquaredWeight_pos hs pk).le]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (norm_inv_one_sub_real_mul_le_two hB
      (by
        rw [abs_of_pos
          (gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos hs pk)]
        exact gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_le hs hs1 pk)
      hu)
    (gammaSewnMobiusApertureStokesSquaredWeight_pos hs pk).le

theorem gammaSewnMobiusApertureStokesSquaredCompactCarrier_markov_eq_tsum
    {s : ℝ} (hs : 0 < s) (u : ℂ) :
    compactMarkovTransform (gammaSewnMobiusApertureStokesSquaredCompactCarrier s) u =
      ∑' pk : Nat.Primes × ℕ,
        (gammaSewnMobiusApertureStokesSquaredWeight s pk : ℂ) *
          (1 - (gammaSewnMobiusApertureStokesSquaredReciprocalGapNode s pk : ℂ) * u)⁻¹ := by
  rw [compactMarkovTransform, compactMarkovKernelMoment,
    gammaSewnMobiusApertureStokesSquaredCompactCarrier]
  rw [integral_sum_dirac (fun pk => by simp [ENNReal.ofReal_ne_top])]
  rw [tsum_congr (fun pk => by
    rw [ENNReal.toReal_ofReal
      (gammaSewnMobiusApertureStokesSquaredWeight_pos hs pk).le])]
  simp only [pow_zero, one_mul, Nat.zero_add, pow_one]
  rfl

/-- Exact square-coordinate response law forced by Kummer reflection. -/
theorem gammaSewnMobiusApertureStokesReflectedResponse_eq_squaredCompactMarkov
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hzIm : 0 < z.im)
    (hzSq : ‖z ^ 2‖ < 1 / (2 * (((Real.log 2)⁻¹) ^ 2))) :
    gammaSewnMobiusApertureStokesReflectedResponse s z =
      -z * compactMarkovTransform
        (gammaSewnMobiusApertureStokesSquaredCompactCarrier s) (z ^ 2) := by
  rw [gammaSewnMobiusApertureStokesReflectedResponse,
    gammaSewnMobiusApertureStokesSquaredCompactCarrier_markov_eq_tsum hs (z ^ 2)]
  have hseries :=
    summable_gammaSewnMobiusApertureStokesSquaredMarkovSeries hs hs1 hzSq
  rw [← hseries.tsum_mul_left]
  apply tsum_congr
  intro pk
  rw [gammaSewnMobiusApertureStokesReflectedAtom_eq_compactMarkov hs hzIm,
    gammaSewnMobiusApertureStokesSquaredWeight,
    gammaSewnMobiusApertureStokesSquaredReciprocalGapNode]
  push_cast
  ring

/-- Critical aperture candidate singled out by the completed seam. -/
def gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier : Measure ℝ :=
  gammaSewnMobiusApertureStokesSquaredCompactCarrier (1 / 2)

/-- The exact remaining Route-P coefficient identification. -/
def GammaSewnMobiusApertureStokesCriticalMomentIdentification : Prop :=
  completedSeamMomentGerm =ᶠ[nhds 0]
    compactMarkovTransform gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier

/-- Closing the critical all-degree source identity closes RH through the existing capstone. -/
theorem riemannHypothesis_of_gammaSewnMobiusApertureStokesCriticalMomentIdentification
    (h : GammaSewnMobiusApertureStokesCriticalMomentIdentification) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_primeArchCompactMarkovGermRepresentation
  refine ⟨gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier,
    ((Real.log 2)⁻¹) ^ 2, ?_, ?_, ?_, h⟩
  · exact gammaSewnMobiusApertureStokesSquaredCompactCarrier_finite
      (by norm_num) (by norm_num)
  · exact sq_pos_of_pos (inv_pos.mpr (Real.log_pos (by norm_num)))
  · exact ae_gammaSewnMobiusApertureStokesSquaredCompactCarrier_mem_compact
      (by norm_num) (by norm_num)

end RHTower
