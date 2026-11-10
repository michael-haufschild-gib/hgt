import GaloisForLFunctions.TransThresholdPairCorrelation.PeriodicSincMajorant
import GaloisForLFunctions.TransThresholdPairCorrelation.PositivityCannotReachTheThreeQuarterThreshold
import GaloisForLFunctions.HTGeometry.TorusFejerDisplacement
import GaloisForLFunctions.RHTower.Sieve.FejerCorrelation

/-!
# Positive pair densities with excess mass above frequency one

A periodic majorant of `sinc²`, completed to mean one by a Fejér kernel,
produces nonnegative Fourier coefficients. Replacing its atoms by narrow
triangles preserves positivity of the pair density and exact agreement
with the diagonal form factor on `[0,1]`.
-/

open Real Finset MeasureTheory Set FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem fejer_cosine_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ 1 + 2 * ∑ k ∈ range N,
      (1 - ((k : ℝ) + 1) / ((N : ℝ) + 1)) * cos (((k : ℝ) + 1) * x) := by
  have hN : 0 < (N : ℝ) + 1 := by positivity
  have hd : ‖dirichletSum N x‖ ^ 2 =
      2 * (∑ k ∈ range (N+1), (((N+1 : ℕ) : ℝ) - (k : ℝ)) * cos ((k : ℝ)*x)) -
        ((N+1 : ℕ) : ℝ) * cos ((0 : ℝ)*x) := by
    rw [norm_dirichletSum_sq]
    convert! RHTower.Sieve.sum_dist_double (fun k => cos ((k : ℝ)*x)) (N+1) using 1
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rcases le_total i j with hij | hji
    · rw [max_eq_right hij, min_eq_left hij, Nat.cast_sub hij]
      have harg : ((i : ℝ)-(j : ℝ))*x = -(((j : ℝ)-(i : ℝ))*x) := by ring
      rw [harg, cos_neg]
    · rw [max_eq_left hji, min_eq_right hji, Nat.cast_sub hji]
    all_goals simp only [Nat.cast_zero]
  have hw : (∑ k ∈ range (N+1), (((N+1 : ℕ) : ℝ) - (k : ℝ)) * cos ((k : ℝ)*x)) =
      ((N : ℝ)+1) + ((N : ℝ)+1) * ∑ k ∈ range N,
        (1 - ((k : ℝ)+1)/((N : ℝ)+1)) * cos (((k : ℝ)+1)*x) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, sub_zero, zero_mul, cos_zero, mul_one]
    rw [mul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    field_simp
  rw [hw] at hd
  simp only [zero_mul, cos_zero, mul_one, Nat.cast_add, Nat.cast_one] at hd
  have he : ‖dirichletSum N x‖ ^ 2 = ((N : ℝ)+1) *
      (1 + 2 * ∑ k ∈ range N,
        (1 - ((k : ℝ)+1)/((N : ℝ)+1)) * cos (((k : ℝ)+1)*x)) := by
    rw [hd]
    ring
  have hp := sq_nonneg ‖dirichletSum N x‖
  rw [he] at hp
  exact (mul_nonneg_iff_of_pos_left hN).mp hp

/-- Half-width of the triangular spikes. -/
def seventySpikeWidth : ℝ := 1 / 10000

/-- The first spike starts at frequency one. -/
def seventySpikeCenter : ℝ := 10001 / 10000

/-- The constant coefficient available for a nonnegative Fejér kernel. -/
def seventySpikeReserve : ℝ := 1 - seventySpikeCenter ^ 2 * (3273 / 4096)

private def majorantCorrection (k : ℕ) : ℝ :=
  (if k = 0 then 991/9216 else 0) - (if k = 1 then 49/6144 else 0) +
    (if k = 2 then 1/1024 else 0) - (if k = 3 then 5/73728 else 0)

/-- Mass of the spike at the `(k+1)`-st positive frequency. -/
def seventySpikeCoeff (k : ℕ) : ℝ :=
  seventySpikeCenter ^ 2 * majorantCorrection k +
    seventySpikeReserve * (1 - ((k : ℝ) + 1) / 101)

theorem seventySpikeReserve_pos : 0 < seventySpikeReserve := by
  norm_num [seventySpikeReserve, seventySpikeCenter]

theorem seventySpikeCoeff_nonneg {k : ℕ} (hk : k < 100) : 0 ≤ seventySpikeCoeff k := by
  by_cases h0 : k = 0
  · subst k; norm_num [seventySpikeCoeff, majorantCorrection, seventySpikeReserve, seventySpikeCenter]
  by_cases h1 : k = 1
  · subst k; norm_num [seventySpikeCoeff, majorantCorrection, seventySpikeReserve, seventySpikeCenter]
  by_cases h2 : k = 2
  · subst k; norm_num [seventySpikeCoeff, majorantCorrection, seventySpikeReserve, seventySpikeCenter]
  by_cases h3 : k = 3
  · subst k; norm_num [seventySpikeCoeff, majorantCorrection, seventySpikeReserve, seventySpikeCenter]
  have hk' : (k : ℝ) < 100 := by exact_mod_cast hk
  have hc : majorantCorrection k = 0 := by simp only [majorantCorrection, if_neg h0,
    if_neg h1, if_neg h2, if_neg h3, sub_self, add_zero]
  rw [seventySpikeCoeff, hc, mul_zero, zero_add]
  exact mul_nonneg seventySpikeReserve_pos.le (by linarith)

theorem seventySpikeCoeff_zero_gt : 61/200 < seventySpikeCoeff 0 := by
  norm_num [seventySpikeCoeff, majorantCorrection, seventySpikeReserve, seventySpikeCenter]

private theorem sum_majorantCorrection (x : ℝ) :
    (∑ k ∈ Finset.range 100, majorantCorrection k * cos (2*((k : ℝ)+1)*x)) =
      991/9216*cos (2*x) - 49/6144*cos (4*x) + 1/1024*cos (6*x) - 5/73728*cos (8*x) := by
  simp only [majorantCorrection, sub_mul, add_mul, ite_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp
  ring

/-- A continuous form factor with one hundred narrow symmetric spike pairs. -/
def seventyFormFactor (α : ℝ) : ℝ :=
  min |α| 1 + ∑ k ∈ Finset.range 100, (seventySpikeCoeff k / seventySpikeWidth) *
    (triangleFn seventySpikeWidth (α - ((k : ℝ)+1)*seventySpikeCenter) +
      triangleFn seventySpikeWidth (α + ((k : ℝ)+1)*seventySpikeCenter))

/-- The off-diagonal pair density of the finite spike model. -/
def seventyPairDensity (ξ : ℝ) : ℝ :=
  1 - sinc (π*ξ)^2 + 2 *
    (∑ k ∈ Finset.range 100, seventySpikeCoeff k *
      cos (2*π*(((k : ℝ)+1)*seventySpikeCenter)*ξ)) * sinc (π*seventySpikeWidth*ξ)^2


private theorem seventyEnvelope_identity (x : ℝ) :
    seventySpikeCenter^2 * periodicSincMajorant x + seventySpikeReserve *
      (1 + 2 * ∑ k ∈ range 100, (1 - ((k : ℝ)+1)/101) * cos (2*((k : ℝ)+1)*x)) =
        1 + 2 * ∑ k ∈ range 100, seventySpikeCoeff k * cos (2*((k : ℝ)+1)*x) := by
  have he : (∑ k ∈ range 100, seventySpikeCoeff k * cos (2*((k : ℝ)+1)*x)) =
      seventySpikeCenter^2 * (∑ k ∈ range 100, majorantCorrection k * cos (2*((k : ℝ)+1)*x)) +
        seventySpikeReserve * (∑ k ∈ range 100, (1 - ((k : ℝ)+1)/101) * cos (2*((k : ℝ)+1)*x)) := by
    simp only [seventySpikeCoeff, add_mul, mul_assoc, sum_add_distrib, mul_sum]
  rw [he, sum_majorantCorrection, periodicSincMajorant_fourier]
  unfold seventySpikeReserve
  ring

/-- The Fourier polynomial of the spike masses dominates the squared sinc function. -/
theorem sinc_sq_le_seventyEnvelope (x : ℝ) :
    sinc x^2 ≤ 1 + 2 * ∑ k ∈ range 100,
      seventySpikeCoeff k * cos (2*((k : ℝ)+1)*(seventySpikeCenter*x)) := by
  have hK : 0 ≤ 1 + 2 * ∑ k ∈ range 100,
      (1 - ((k : ℝ)+1)/101) * cos (2*((k : ℝ)+1)*(seventySpikeCenter*x)) := by
    have h := fejer_cosine_nonneg 100 (2*(seventySpikeCenter*x))
    simp only [Nat.cast_ofNat, show (100 : ℝ)+1 = 101 by norm_num] at h
    have hs : (∑ k ∈ range 100, (1 - ((k : ℝ)+1)/101) *
        cos (((k : ℝ)+1)*(2*(seventySpikeCenter*x)))) =
        ∑ k ∈ range 100, (1 - ((k : ℝ)+1)/101) *
          cos (2*((k : ℝ)+1)*(seventySpikeCenter*x)) := by
      refine sum_congr rfl fun k _ => ?_
      rw [show ((k : ℝ)+1)*(2*(seventySpikeCenter*x)) =
        2*((k : ℝ)+1)*(seventySpikeCenter*x) by ring]
    rwa [hs] at h
  have hmajor := sinc_sq_le_scaled_periodicMajorant
    (b := seventySpikeCenter) (by norm_num [seventySpikeCenter]) x
  have hpositive := mul_nonneg seventySpikeReserve_pos.le hK
  linarith only [hmajor, hpositive, seventyEnvelope_identity (seventySpikeCenter*x)]

/-- Smoothing the Fourier atoms by equal triangles preserves the positive pair density. -/
theorem seventyPairDensity_nonneg (ξ : ℝ) : 0 ≤ seventyPairDensity ξ := by
  have h := sinc_sq_le_seventyEnvelope (π*ξ)
  have hs : (∑ k ∈ range 100, seventySpikeCoeff k *
      cos (2*((k : ℝ)+1)*(seventySpikeCenter*(π*ξ)))) =
      ∑ k ∈ range 100, seventySpikeCoeff k *
        cos (2*π*(((k : ℝ)+1)*seventySpikeCenter)*ξ) := by
    refine sum_congr rfl fun k _ => ?_
    rw [show 2*((k : ℝ)+1)*(seventySpikeCenter*(π*ξ)) =
      2*π*(((k : ℝ)+1)*seventySpikeCenter)*ξ by ring]
  rw [hs] at h
  have hb : 0 ≤ 1 - sinc (π*ξ)^2 :=
    sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one _))
  have hq : 0 ≤ 1 - sinc (π*seventySpikeWidth*ξ)^2 :=
    sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one _))
  have hp := mul_nonneg hq hb
  have hp' := mul_nonneg (sq_nonneg (sinc (π*seventySpikeWidth*ξ))) (sub_nonneg.mpr h)
  unfold seventyPairDensity
  nlinarith only [hp, hp']


private theorem seventySpikeWidth_pos : 0 < seventySpikeWidth := by
  norm_num [seventySpikeWidth]

theorem continuous_seventyFormFactor : Continuous seventyFormFactor := by
  have hΛ := continuous_triangleFn seventySpikeWidth
  unfold seventyFormFactor
  fun_prop

theorem seventyFormFactor_nonneg (α : ℝ) : 0 ≤ seventyFormFactor α := by
  unfold seventyFormFactor
  refine add_nonneg (le_min (abs_nonneg α) zero_le_one) (sum_nonneg fun k hk => ?_)
  exact mul_nonneg (div_nonneg (seventySpikeCoeff_nonneg (mem_range.mp hk)) seventySpikeWidth_pos.le)
    (add_nonneg (triangleFn_nonneg _ _) (triangleFn_nonneg _ _))

theorem seventyFormFactor_ge_one {α : ℝ} (hα : 1 ≤ |α|) : 1 ≤ seventyFormFactor α := by
  unfold seventyFormFactor
  rw [min_eq_right hα]
  have hs : 0 ≤ ∑ k ∈ range 100, (seventySpikeCoeff k / seventySpikeWidth) *
      (triangleFn seventySpikeWidth (α - ((k : ℝ)+1)*seventySpikeCenter) +
        triangleFn seventySpikeWidth (α + ((k : ℝ)+1)*seventySpikeCenter)) := by
    apply sum_nonneg
    intro k hk
    exact mul_nonneg (div_nonneg (seventySpikeCoeff_nonneg (mem_range.mp hk)) seventySpikeWidth_pos.le)
      (add_nonneg (triangleFn_nonneg _ _) (triangleFn_nonneg _ _))
  linarith only [hs]

theorem seventyFormFactor_even (α : ℝ) : seventyFormFactor (-α) = seventyFormFactor α := by
  have heven (w u : ℝ) : triangleFn w (-u) = triangleFn w u := by
    unfold triangleFn
    rw [abs_neg]
  unfold seventyFormFactor
  rw [abs_neg]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [show -α - ((k : ℝ)+1)*seventySpikeCenter = -(α + ((k : ℝ)+1)*seventySpikeCenter) by ring,
    show -α + ((k : ℝ)+1)*seventySpikeCenter = -(α - ((k : ℝ)+1)*seventySpikeCenter) by ring,
    heven, heven, add_comm]

theorem seventyFormFactor_of_mem_Icc {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    seventyFormFactor α = α := by
  have hb (k : ℕ) : 1 + seventySpikeWidth ≤ ((k : ℝ)+1)*seventySpikeCenter := by
    unfold seventySpikeWidth seventySpikeCenter
    nlinarith only [Nat.cast_nonneg (α := ℝ) k]
  have hz : ∑ k ∈ range 100, (seventySpikeCoeff k / seventySpikeWidth) *
      (triangleFn seventySpikeWidth (α - ((k : ℝ)+1)*seventySpikeCenter) +
        triangleFn seventySpikeWidth (α + ((k : ℝ)+1)*seventySpikeCenter)) = 0 := by
    refine sum_eq_zero fun k _ => ?_
    have hm : triangleFn seventySpikeWidth (α - ((k : ℝ)+1)*seventySpikeCenter) = 0 := by
      apply triangleFn_eq_zero seventySpikeWidth_pos
      rw [abs_of_neg (by linarith only [hb k, hα.2, seventySpikeWidth_pos])]
      linarith only [hb k, hα.2]
    have hp : triangleFn seventySpikeWidth (α + ((k : ℝ)+1)*seventySpikeCenter) = 0 := by
      apply triangleFn_eq_zero seventySpikeWidth_pos
      rw [abs_of_pos (by linarith only [hb k, hα.1, seventySpikeWidth_pos])]
      linarith only [hb k, hα.1]
    rw [hm, hp, add_zero, mul_zero]
  unfold seventyFormFactor
  rw [hz, add_zero, abs_of_nonneg hα.1, min_eq_left hα.2]

end GaloisForLFunctions.TransThresholdPairCorrelation
