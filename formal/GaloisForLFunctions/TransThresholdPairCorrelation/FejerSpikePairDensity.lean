import GaloisForLFunctions.TransThresholdPairCorrelation.PeriodicSincMajorant
import GaloisForLFunctions.TransThresholdPairCorrelation.PositivityCannotReachTheThreeQuarterThreshold
import GaloisForLFunctions.HTGeometry.TorusFejerDisplacement
import GaloisForLFunctions.RHTower.Sieve.FejerCorrelation

/-!
# Positive pair densities with excess mass above frequency one

A periodic majorant of `sinc²`, completed to mean one by a Fejér kernel,
produces nonnegative Fourier coefficients. Replacing its atoms by narrow
triangles preserves positivity of the pair density and exact agreement
with the diagonal form factor on `[0,1]`. Its weighted integral exceeds `7/45`,
excluding a seventy-percent certificate at bandwidth `4/3`.
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
  norm_num

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

private theorem integral_first_seventyTriangle :
    ∫ α in (1 : ℝ)..4/3, triangleFn seventySpikeWidth (α-seventySpikeCenter) =
      seventySpikeWidth := by
  have hc := continuous_triangleFn seventySpikeWidth
  rw [intervalIntegral.integral_comp_sub_right (triangleFn seventySpikeWidth) seventySpikeCenter,
    show (1 : ℝ)-seventySpikeCenter = -seventySpikeWidth by
      norm_num [seventySpikeCenter, seventySpikeWidth]]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := seventySpikeWidth)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hcore : ∫ u in -seventySpikeWidth..seventySpikeWidth, triangleFn seventySpikeWidth u =
      seventySpikeWidth := by
    have h := integral_triangleFn seventySpikeWidth_pos
    rw [intervalIntegral.integral_ofReal] at h
    exact_mod_cast h
  have htail : ∫ u in seventySpikeWidth..4/3-seventySpikeCenter,
      triangleFn seventySpikeWidth u = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_]
    · simp
    rw [Set.uIcc_of_le (by norm_num [seventySpikeWidth, seventySpikeCenter])] at hu
    exact triangleFn_eq_zero seventySpikeWidth_pos
      (by rw [abs_of_pos (lt_of_lt_of_le seventySpikeWidth_pos hu.1)]; exact hu.1)
  rw [hcore, htail, add_zero]

private theorem seventyFormFactor_ge_first {α : ℝ} (hα : 1 ≤ α) :
    1 + (seventySpikeCoeff 0/seventySpikeWidth) *
      triangleFn seventySpikeWidth (α-seventySpikeCenter) ≤ seventyFormFactor α := by
  have hn (k : ℕ) (hk : k ∈ range 100) : 0 ≤ (seventySpikeCoeff k/seventySpikeWidth) *
      (triangleFn seventySpikeWidth (α-((k : ℝ)+1)*seventySpikeCenter) +
        triangleFn seventySpikeWidth (α+((k : ℝ)+1)*seventySpikeCenter)) :=
    mul_nonneg (div_nonneg (seventySpikeCoeff_nonneg (mem_range.mp hk)) seventySpikeWidth_pos.le)
      (add_nonneg (triangleFn_nonneg _ _) (triangleFn_nonneg _ _))
  have hs := single_le_sum hn (by norm_num : 0 ∈ range 100)
  have ha := div_nonneg (seventySpikeCoeff_nonneg (by norm_num : 0 < 100)) seventySpikeWidth_pos.le
  have hp := mul_nonneg ha (triangleFn_nonneg seventySpikeWidth (α+seventySpikeCenter))
  simp only [Nat.cast_zero, zero_add, one_mul] at hs
  unfold seventyFormFactor
  rw [abs_of_pos (by linarith only [hα]), min_eq_right hα]
  nlinarith only [hs, hp]

/-- The first spike alone exceeds the seventy-percent weighted-integral threshold. -/
theorem transThresholdIntegral_seventyFormFactor_gt :
    7/45 < transThresholdIntegral seventyFormFactor (4/3) := by
  have hΛc : Continuous fun α : ℝ => triangleFn seventySpikeWidth (α-seventySpikeCenter) :=
    (continuous_triangleFn _).comp (continuous_id.sub continuous_const)
  have hbase : ∫ α in (1 : ℝ)..4/3, (4/3-α) = 1/18 := by
    have h := transThresholdIntegral_four_thirds_one
    unfold transThresholdIntegral at h
    simpa only [mul_one] using h
  have ha := div_nonneg (seventySpikeCoeff_nonneg (by norm_num : 0 < 100)) seventySpikeWidth_pos.le
  have hpt (α : ℝ) (hα : α ∈ Icc (1 : ℝ) (4/3)) :
      (4/3-α) + ((4/3-seventySpikeCenter-seventySpikeWidth) *
        (seventySpikeCoeff 0/seventySpikeWidth)) * triangleFn seventySpikeWidth (α-seventySpikeCenter) ≤
          (4/3-α) * seventyFormFactor α := by
    have hw := mul_le_mul_of_nonneg_left (seventyFormFactor_ge_first hα.1)
      (by linarith only [hα.2] : 0 ≤ 4/3-α)
    by_cases hnear : α ≤ seventySpikeCenter+seventySpikeWidth
    · have hp := mul_nonneg (sub_nonneg.mpr hnear)
        (mul_nonneg ha (triangleFn_nonneg seventySpikeWidth (α-seventySpikeCenter)))
      nlinarith only [hw, hp]
    · have hz : triangleFn seventySpikeWidth (α-seventySpikeCenter) = 0 := by
        apply triangleFn_eq_zero seventySpikeWidth_pos
        rw [abs_of_pos (by linarith only [hnear, seventySpikeWidth_pos])]
        linarith only [hnear]
      rw [hz] at hw ⊢
      simpa only [mul_zero, add_zero, mul_one] using hw
  have hlhs : IntervalIntegrable (fun α : ℝ => (4/3-α) +
      ((4/3-seventySpikeCenter-seventySpikeWidth)*(seventySpikeCoeff 0/seventySpikeWidth)) *
        triangleFn seventySpikeWidth (α-seventySpikeCenter)) volume 1 (4/3) :=
    ((continuous_const.sub continuous_id).add (hΛc.const_mul _)).intervalIntegrable _ _
  have hrhs : IntervalIntegrable (fun α : ℝ => (4/3-α)*seventyFormFactor α) volume 1 (4/3) :=
    ((continuous_const.sub continuous_id).mul continuous_seventyFormFactor).intervalIntegrable _ _
  have hint := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 4/3) hlhs hrhs hpt
  have hlin : IntervalIntegrable (fun α : ℝ => (4/3 : ℝ)-α) volume 1 (4/3) :=
    (by fun_prop : Continuous fun α : ℝ => (4/3 : ℝ)-α).intervalIntegrable _ _
  have hsp : IntervalIntegrable (fun α : ℝ =>
      ((4/3-seventySpikeCenter-seventySpikeWidth)*(seventySpikeCoeff 0/seventySpikeWidth)) *
        triangleFn seventySpikeWidth (α-seventySpikeCenter)) volume 1 (4/3) :=
    (hΛc.const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hlin hsp, intervalIntegral.integral_const_mul,
    hbase, integral_first_seventyTriangle] at hint
  have hm : ((4/3-seventySpikeCenter-seventySpikeWidth)*(seventySpikeCoeff 0/seventySpikeWidth)) *
      seventySpikeWidth = (4/3-seventySpikeCenter-seventySpikeWidth)*seventySpikeCoeff 0 := by
    field_simp [ne_of_gt seventySpikeWidth_pos]
  rw [hm] at hint
  have hL : 0 < (4/3 : ℝ)-seventySpikeCenter-seventySpikeWidth := by
    norm_num [seventySpikeCenter, seventySpikeWidth]
  have hmass := mul_lt_mul_of_pos_left seventySpikeCoeff_zero_gt hL
  have htarget : (7/45 : ℝ) < 1/18 + (4/3-seventySpikeCenter-seventySpikeWidth)*(61/200) := by
    norm_num [seventySpikeCenter, seventySpikeWidth]
  unfold transThresholdIntegral
  linarith only [hint, hmass, htarget]

/-- Positivity's seventy-percent Frobenius ceiling fails at bandwidth `4/3`. -/
theorem frobeniusFormFactor_seventyFormFactor_gt :
    13/10 < frobeniusFormFactor seventyFormFactor (4/3) := by
  rw [frobeniusFormFactor_four_thirds continuous_seventyFormFactor
    (fun _ hα => seventyFormFactor_of_mem_Icc hα)]
  linarith only [transThresholdIntegral_seventyFormFactor_gt]

private theorem seventyFormFactor_sub_one (α : ℝ) :
    seventyFormFactor α - 1 = -triangleFn 1 (α-0) +
      ∑ k ∈ Finset.range 100, (seventySpikeCoeff k/seventySpikeWidth) *
        (triangleFn seventySpikeWidth (α-((k : ℝ)+1)*seventySpikeCenter) +
          triangleFn seventySpikeWidth (α-(-(((k : ℝ)+1)*seventySpikeCenter)))) := by
  have hm : min |α| 1 - 1 = -triangleFn 1 α := by
    unfold triangleFn
    rcases le_total |α| 1 with h | h
    · rw [min_eq_left h, div_one, max_eq_left (by linarith only [h])]; ring
    · rw [min_eq_right h, div_one, max_eq_right (by linarith only [h])]; ring
  unfold seventyFormFactor
  simp only [sub_zero, sub_neg_eq_add]
  linarith only [hm]

private theorem integral_cexp_mul_triangle_pair {w : ℝ} (hw : 0 < w) (b ξ : ℝ) :
    ∫ α : ℝ, Complex.exp (↑(-2*π*α*ξ)*Complex.I) *
      ((triangleFn w (α-b) + triangleFn w (α-(-b)) : ℝ) : ℂ) =
        ((2*w*cos (2*π*b*ξ)*sinc (π*w*ξ)^2 : ℝ) : ℂ) := by
  have hB := integrable_cexp_mul_triangleFn_sub hw b ξ
  have hC := integrable_cexp_mul_triangleFn_sub hw (-b) ξ
  have he : (fun α : ℝ => Complex.exp (↑(-2*π*α*ξ)*Complex.I) *
      ((triangleFn w (α-b) + triangleFn w (α-(-b)) : ℝ) : ℂ)) =
      fun α : ℝ => Complex.exp (↑(-2*π*α*ξ)*Complex.I) * (triangleFn w (α-b) : ℂ) +
        Complex.exp (↑(-2*π*α*ξ)*Complex.I) * (triangleFn w (α-(-b)) : ℂ) := by
    funext α
    push_cast
    ring
  rw [he, integral_add hB hC, integral_cexp_mul_triangleFn_sub hw,
    integral_cexp_mul_triangleFn_sub hw]
  have hcos : Complex.exp (↑(-2*π*b*ξ)*Complex.I) +
      Complex.exp (↑(-2*π*(-b)*ξ)*Complex.I) = ((2*cos (2*π*b*ξ) : ℝ) : ℂ) := by
    rw [show (-2*π*b*ξ : ℝ) = -(2*π*b*ξ) by ring,
      show (-2*π*(-b)*ξ : ℝ) = 2*π*b*ξ by ring,
      Complex.ofReal_neg, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  rw [← add_mul, hcos]
  push_cast
  ring

/-- The finite spike perturbation is integrable. -/
theorem integrable_seventyFormFactor_sub_one : Integrable (fun α => seventyFormFactor α-1) := by
  rw [show (fun α => seventyFormFactor α-1) = fun α => -triangleFn 1 (α-0) +
      ∑ k ∈ Finset.range 100, (seventySpikeCoeff k/seventySpikeWidth) *
        (triangleFn seventySpikeWidth (α-((k : ℝ)+1)*seventySpikeCenter) +
          triangleFn seventySpikeWidth (α-(-(((k : ℝ)+1)*seventySpikeCenter)))) from
    funext seventyFormFactor_sub_one]
  apply (integrable_triangleFn_sub one_pos 0).neg.add
  apply integrable_finsetSum
  intro k _
  exact ((integrable_triangleFn_sub seventySpikeWidth_pos _).add
    (integrable_triangleFn_sub seventySpikeWidth_pos _)).const_mul _

private def seventyFourierTerm (ξ : ℝ) (k : ℕ) (α : ℝ) : ℂ :=
  ((seventySpikeCoeff k/seventySpikeWidth : ℝ) : ℂ) *
    (Complex.exp (↑(-2*π*α*ξ)*Complex.I) *
      ((triangleFn seventySpikeWidth (α-((k : ℝ)+1)*seventySpikeCenter) +
        triangleFn seventySpikeWidth (α-(-(((k : ℝ)+1)*seventySpikeCenter))) : ℝ) : ℂ))

private theorem integrable_seventyFourierTerm (ξ : ℝ) (k : ℕ) :
    Integrable (seventyFourierTerm ξ k) := by
  have hA := integrable_cexp_mul_triangleFn_sub seventySpikeWidth_pos
    (((k : ℝ)+1)*seventySpikeCenter) ξ
  have hB := integrable_cexp_mul_triangleFn_sub seventySpikeWidth_pos
    (-(((k : ℝ)+1)*seventySpikeCenter)) ξ
  dsimp only [seventyFourierTerm]
  simpa only [Pi.add_apply, Complex.ofReal_add, mul_add] using
    (hA.add hB).const_mul ((seventySpikeCoeff k/seventySpikeWidth : ℝ) : ℂ)

private theorem integral_seventyFourierTerm (ξ : ℝ) (k : ℕ) :
    ∫ α : ℝ, seventyFourierTerm ξ k α =
      ((2*seventySpikeCoeff k*cos (2*π*(((k : ℝ)+1)*seventySpikeCenter)*ξ) *
        sinc (π*seventySpikeWidth*ξ)^2 : ℝ) : ℂ) := by
  dsimp only [seventyFourierTerm]
  rw [integral_const_mul, integral_cexp_mul_triangle_pair seventySpikeWidth_pos,
    ← Complex.ofReal_mul]
  congr 1
  field_simp [ne_of_gt seventySpikeWidth_pos]
  ring

/-- Exact Fourier duality between the form factor and its nonnegative pair density. -/
theorem fourier_seventyFormFactor_sub_one (ξ : ℝ) :
    𝓕 (fun α => ((seventyFormFactor α-1 : ℝ) : ℂ)) ξ = ((seventyPairDensity ξ-1 : ℝ) : ℂ) := by
  have hA := integrable_cexp_mul_triangleFn_sub one_pos 0 ξ
  have hterms (k : ℕ) (_ : k ∈ Finset.range 100) := integrable_seventyFourierTerm ξ k
  have hneg : Integrable (fun α : ℝ =>
      -(Complex.exp (↑(-2*π*α*ξ)*Complex.I) * (triangleFn 1 (α-0) : ℂ))) := hA.neg
  have hsum : Integrable (fun α : ℝ =>
      ∑ k ∈ Finset.range 100, seventyFourierTerm ξ k α) := integrable_finsetSum _ hterms
  rw [fourier_real_eq_integral_exp_smul]
  refine (integral_congr_ae (g := fun α : ℝ =>
      -(Complex.exp (↑(-2*π*α*ξ)*Complex.I) * (triangleFn 1 (α-0) : ℂ)) +
        ∑ k ∈ Finset.range 100, seventyFourierTerm ξ k α)
    (Filter.Eventually.of_forall fun α => ?_)).trans ?_
  · simp only [smul_eq_mul]
    rw [seventyFormFactor_sub_one]
    push_cast
    rw [mul_add, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold seventyFourierTerm
    push_cast
    ring
  rw [integral_add hneg hsum, integral_neg,
    integral_finsetSum _ hterms, integral_cexp_mul_triangleFn_sub one_pos]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, mul_one]
  rw [Finset.sum_congr rfl fun k _ => integral_seventyFourierTerm ξ k]
  have hs : (∑ k ∈ Finset.range 100,
      ((2*seventySpikeCoeff k*cos (2*π*(((k : ℝ)+1)*seventySpikeCenter)*ξ) *
        sinc (π*seventySpikeWidth*ξ)^2 : ℝ) : ℂ)) =
      ((2*(∑ k ∈ Finset.range 100, seventySpikeCoeff k*
        cos (2*π*(((k : ℝ)+1)*seventySpikeCenter)*ξ)) * sinc (π*seventySpikeWidth*ξ)^2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hs]
  unfold seventyPairDensity
  push_cast
  ring

/-- At bandwidth `4/3`, sub-threshold agreement and positivity of both the form factor
and its pair density do not certify seventy percent. The witness also dominates the
constant form factor beyond frequency one and has an integrable perturbation. -/
theorem positivity_does_not_reach_seventy_percent_at_four_thirds :
    ∃ F : ℝ → ℝ, Continuous F ∧ (∀ α, F (-α) = F α) ∧ (∀ α, 0 ≤ F α) ∧
      (∀ α ∈ Set.Icc (0 : ℝ) 1, F α = α) ∧ (∀ α, 1 ≤ |α| → 1 ≤ F α) ∧
      Integrable (fun α => F α-1) ∧
      (∀ ξ : ℝ, ∃ p : ℝ, 0 ≤ p ∧ 𝓕 (fun α => ((F α-1 : ℝ) : ℂ)) ξ = ((p-1 : ℝ) : ℂ)) ∧
      7/45 < transThresholdIntegral F (4/3) ∧ 13/10 < frobeniusFormFactor F (4/3) := by
  exact ⟨seventyFormFactor, continuous_seventyFormFactor, seventyFormFactor_even,
    seventyFormFactor_nonneg, fun _ hα => seventyFormFactor_of_mem_Icc hα,
    fun _ hα => seventyFormFactor_ge_one hα, integrable_seventyFormFactor_sub_one,
    fun ξ => ⟨seventyPairDensity ξ, seventyPairDensity_nonneg ξ, fourier_seventyFormFactor_sub_one ξ⟩,
    transThresholdIntegral_seventyFormFactor_gt, frobeniusFormFactor_seventyFormFactor_gt⟩

end GaloisForLFunctions.TransThresholdPairCorrelation
