import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
# Mean-square transfer and dyadic-to-prefix passage

Uniform approximation on each dyadic window transfers its mean square. A
continuous primitive then recovers the mean on the whole initial interval.
-/

open Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

def dyadicSquareMean (f : ℝ → ℂ) (T : ℝ) : ℝ :=
  (∫ t in T..2 * T, ‖f t‖ ^ 2) / T

theorem abs_norm_sq_sub_le {x y : ℂ} {e : ℝ} (he : 0 ≤ e) (hxy : ‖x - y‖ ≤ e) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ e * (‖y‖ ^ 2 + 1 + e) := by
  have hd : |‖x‖ - ‖y‖| ≤ e := (abs_norm_sub_norm_le x y).trans hxy
  have hs : ‖x‖ + ‖y‖ ≤ 2 * ‖y‖ + e := by linarith [(abs_le.mp hd).2]
  calc
    |‖x‖ ^ 2 - ‖y‖ ^ 2| = |‖x‖ - ‖y‖| * (‖x‖ + ‖y‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring
    _ ≤ e * (2 * ‖y‖ + e) := mul_le_mul hd hs (by positivity) he
    _ ≤ e * (‖y‖ ^ 2 + 1 + e) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖y‖ - 1)]) he

theorem abs_dyadicSquareMean_sub_le {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {T e : ℝ} (hT : 0 < T) (he : 0 ≤ e)
    (hclose : ∀ t ∈ Icc T (2 * T), ‖f t - g t‖ ≤ e) :
    |dyadicSquareMean f T - dyadicSquareMean g T| ≤
      e * (dyadicSquareMean g T + 1 + e) := by
  have hab : T ≤ 2 * T := by linarith
  have hf₂ : Continuous (fun t => ‖f t‖ ^ 2) := hf.norm.pow 2
  have hg₂ : Continuous (fun t => ‖g t‖ ^ 2) := hg.norm.pow 2
  have hbound := intervalIntegral.integral_mono_on (μ := volume) hab
    ((hf₂.sub hg₂).abs.intervalIntegrable T (2 * T))
    (((continuous_const.mul hg₂).add continuous_const).intervalIntegrable T (2 * T))
    (fun t ht => (abs_norm_sq_sub_le he (hclose t ht)).trans_eq
      (show e * (‖g t‖ ^ 2 + 1 + e) = e * ‖g t‖ ^ 2 + e * (1 + e) by ring))
  have h := (intervalIntegral.abs_integral_le_integral_abs
    (f := fun t => ‖f t‖ ^ 2 - ‖g t‖ ^ 2) hab).trans hbound
  change |∫ t in T..2 * T, ‖f t‖ ^ 2 - ‖g t‖ ^ 2| ≤
    ∫ t in T..2 * T, e * ‖g t‖ ^ 2 + e * (1 + e) at h
  have hgi : IntervalIntegrable (fun t => e * ‖g t‖ ^ 2) volume T (2 * T) :=
    (continuous_const.mul hg₂).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hf₂.intervalIntegrable _ _) (hg₂.intervalIntegrable _ _),
    intervalIntegral.integral_add hgi (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h
  have hd := div_le_div_of_nonneg_right h hT.le
  unfold dyadicSquareMean
  rw [← sub_div, abs_div, abs_of_pos hT]
  apply hd.trans_eq
  simp only [smul_eq_mul]
  field_simp
  ring

theorem tendsto_dyadicSquareMean_of_uniform_error {f : ℝ → ℂ} {g : ℝ → ℝ → ℂ}
    (hf : Continuous f) (hg : ∀ T, Continuous (g T)) {e : ℝ → ℝ} {c : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (he0 : ∀ᶠ T in atTop, 0 ≤ e T)
    (hclose : ∀ᶠ T in atTop, ∀ t ∈ Icc T (2 * T), ‖f t - g T t‖ ≤ e T)
    (hmean : Tendsto (fun T => dyadicSquareMean (g T) T) atTop (𝓝 c)) :
    Tendsto (dyadicSquareMean f) atTop (𝓝 c) := by
  have hbound : Tendsto (fun T => e T * (dyadicSquareMean (g T) T + 1 + e T))
      atTop (𝓝 0) := by
    simpa using he.mul ((hmean.add_const 1).add he)
  have herr : Tendsto (fun T => dyadicSquareMean f T - dyadicSquareMean (g T) T)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hbound
    filter_upwards [eventually_ge_atTop (1 : ℝ), he0, hclose] with T hT heT hcT
    simpa only [Real.norm_eq_abs] using
      abs_dyadicSquareMean_sub_le hf (hg T) (by linarith) heT hcT
  simpa using herr.add hmean

theorem tendsto_div_zero_of_dyadicDifference {F : ℝ → ℝ} (hF : Continuous F)
    (hstep : Tendsto (fun T => (F (2 * T) - F T) / T) atTop (𝓝 0)) :
    Tendsto (fun T => F T / T) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := (Metric.tendsto_nhds.mp hstep) (ε / 2) (by positivity)
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp hsmall
  let V := max V₀ 1
  have hV0 : V₀ ≤ V := le_max_left _ _
  have hV1 : 1 ≤ V := le_max_right _ _
  have hV : 0 < V := by linarith
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  have hrec (u : ℝ) (hu : u ∈ Icc V (2 * V)) (n : ℕ) :
      |F ((2 : ℝ) ^ n * u)| ≤ C + (ε / 2) * ((2 : ℝ) ^ n * u) := by
    have hu0 : 0 < u := hV.trans_le hu.1
    induction n with
    | zero =>
      simpa only [pow_zero, one_mul] using
        (show |F u| ≤ C from by simpa only [Real.norm_eq_abs] using hC u hu).trans
          (le_add_of_nonneg_right (by positivity))
    | succ n ih =>
      have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hpu : 0 < (2 : ℝ) ^ n * u := mul_pos (by positivity) (hV.trans_le hu.1)
      have hbase : V₀ ≤ (2 : ℝ) ^ n * u := by nlinarith [hu.1]
      have hs := hV₀ _ hbase
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpu] at hs
      have hs' := (div_lt_iff₀ hpu).mp hs
      have htri := norm_add_le (F (2 * ((2 : ℝ) ^ n * u)) - F ((2 : ℝ) ^ n * u))
        (F ((2 : ℝ) ^ n * u))
      simp only [sub_add_cancel, Real.norm_eq_abs] at htri
      rw [pow_succ]
      rw [show (2 : ℝ) ^ n * 2 * u = 2 * ((2 : ℝ) ^ n * u) by ring]
      linarith
  have hc : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_ge_atTop V,
    hc.eventually_lt_const (show 0 < ε / 2 by positivity)] with T hT hcT
  have hTpos : 0 < T := hV.trans_le hT
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near
    (show 1 ≤ T / V by exact (le_div_iff₀ hV).mpr (by simpa using hT))
    (show (1 : ℝ) < 2 by norm_num)
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  have hu : T / (2 : ℝ) ^ n ∈ Icc V (2 * V) := by
    constructor
    · apply (le_div_iff₀ hp).mpr
      have := (le_div_iff₀ hV).mp hlo
      nlinarith
    · apply (div_le_iff₀ hp).mpr
      have := (div_lt_iff₀ hV).mp hhi
      rw [pow_succ] at this
      nlinarith
  have h := hrec (T / (2 : ℝ) ^ n) hu n
  rw [mul_div_cancel₀ _ hp.ne'] at h
  have hd := div_le_div_of_nonneg_right h hTpos.le
  rw [add_div, mul_div_cancel_right₀ _ hTpos.ne'] at hd
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hTpos]
  linarith

theorem tendsto_div_of_dyadicDifference {F : ℝ → ℝ} (hF : Continuous F) {c : ℝ}
    (hstep : Tendsto (fun T => (F (2 * T) - F T) / T) atTop (𝓝 c)) :
    Tendsto (fun T => F T / T) atTop (𝓝 c) := by
  have hzero : Tendsto (fun T => ((F (2 * T) - c * (2 * T)) - (F T - c * T)) / T)
      atTop (𝓝 0) := by
    have h' : Tendsto (fun T => (F (2 * T) - F T) / T - c) atTop (𝓝 0) := by
      simpa using hstep.sub_const c
    apply h'.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : T ≠ 0 := by linarith
    field_simp
    ring
  have h := (tendsto_div_zero_of_dyadicDifference
    (hF.sub (continuous_const.mul continuous_id)) hzero).add_const c
  simp only [zero_add] at h
  change Tendsto (fun T => (F T - c * T) / T + c) atTop (𝓝 c) at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : T ≠ 0 := by linarith
  field_simp
  ring

theorem tendsto_prefixSquareMean_of_dyadic {f : ℝ → ℂ} (hf : Continuous f) {c : ℝ}
    (hmean : Tendsto (dyadicSquareMean f) atTop (𝓝 c)) :
    Tendsto (fun T => (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) / T) atTop (𝓝 c) := by
  apply tendsto_div_of_dyadicDifference
    (intervalIntegral.continuous_primitive
      (fun a b => (hf.norm.pow 2).intervalIntegrable a b) 0)
  convert hmean using 1
  ext T
  dsimp only [dyadicSquareMean]
  rw [intervalIntegral.integral_interval_sub_left
    ((hf.norm.pow 2).intervalIntegrable 0 (2 * T))
    ((hf.norm.pow 2).intervalIntegrable 0 T)]
  rfl

end RHTower
