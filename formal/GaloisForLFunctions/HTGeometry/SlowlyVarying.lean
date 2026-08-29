import GaloisForLFunctions.HTGeometry.SlowShiftUniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Slowly varying functions and Karamata's uniform convergence theorem

`L` is slowly varying when `L(cx)/L(x) → 1` for every fixed `c > 0`.  The exponential change of
variable `h(t) = log L(e^t)` turns this into the additive statement of `SlowShiftUniform`, so the
convergence is automatically *uniform* for `c` in a compact subinterval of `(0,∞)`.

This is the regular-variation input of the prime Karamata law: the slowly varying factor of the
weight disappears after normalisation precisely because the ratio `L(vX)/L(X)` tends to `1`
uniformly on compact `v`-sets.
-/

open MeasureTheory Filter Topology Set

namespace HTGeometry

/-- A positive, measurable, slowly varying function. -/
structure IsSlowlyVarying (L : ℝ → ℝ) : Prop where
  meas : Measurable L
  pos : ∀ x : ℝ, 0 < x → 0 < L x
  ratio : ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1)

/-- The additive avatar of a slowly varying function. -/
noncomputable def slowLog (L : ℝ → ℝ) (t : ℝ) : ℝ := Real.log (L (Real.exp t))

theorem isSlowShift_slowLog {L : ℝ → ℝ} (hL : IsSlowlyVarying L) : IsSlowShift (slowLog L) := by
  constructor
  · exact Real.measurable_log.comp (hL.meas.comp Real.measurable_exp)
  · intro u
    have hc : (0 : ℝ) < Real.exp u := Real.exp_pos u
    have hratio := hL.ratio (Real.exp u) hc
    have hexp : Tendsto Real.exp atTop atTop := Real.tendsto_exp_atTop
    have hcomp := hratio.comp hexp
    have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hcomp
    rw [Real.log_one] at hlog
    refine Tendsto.congr' ?_ hlog
    filter_upwards with t
    have hp : 0 < L (Real.exp t) := hL.pos _ (Real.exp_pos t)
    have hq : 0 < L (Real.exp u * Real.exp t) := hL.pos _ (by positivity)
    have hcomm : Real.exp (t + u) = Real.exp u * Real.exp t := by
      rw [Real.exp_add, mul_comm]
    rw [Function.comp_apply, Function.comp_apply, slowLog, slowLog, hcomm,
      ← Real.log_div hq.ne' hp.ne']

/-- **Karamata's uniform convergence theorem for slowly varying functions**, logarithmic form. -/
theorem isSlowlyVarying_uniform_log {L : ℝ → ℝ} (hL : IsSlowlyVarying L) (U : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x in atTop, ∀ c ∈ Icc (Real.exp (-U)) (Real.exp U),
      |Real.log (L (c * x) / L x)| ≤ ε := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (isSlowShift_uniform (isSlowShift_slowLog hL) U hε)
  filter_upwards [eventually_gt_atTop (max (Real.exp T₀) 0)] with x hx
  intro c hc
  have hx0 : 0 < x := lt_of_le_of_lt (le_max_right _ _) hx
  have hxT : Real.exp T₀ < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hT : T₀ ≤ Real.log x := by
    rw [← Real.log_exp T₀]
    exact (Real.log_le_log (Real.exp_pos _) hxT.le)
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos _) hc.1
  set u : ℝ := Real.log c with hu
  have hmem : u ∈ Icc (-U) U := by
    constructor
    · rw [hu, ← Real.log_exp (-U)]
      exact Real.log_le_log (Real.exp_pos _) hc.1
    · rw [hu, ← Real.log_exp U]
      exact Real.log_le_log hc0 hc.2
  have hval := hT₀ (Real.log x) hT u hmem
  have hexpx : Real.exp (Real.log x) = x := Real.exp_log hx0
  have hexpc : Real.exp u = c := Real.exp_log hc0
  have hsum : Real.exp (Real.log x + u) = c * x := by
    rw [Real.exp_add, hexpx, hexpc, mul_comm]
  have hp : 0 < L x := hL.pos _ hx0
  have hq : 0 < L (c * x) := hL.pos _ (by positivity)
  rw [slowLog, slowLog, hsum, hexpx, ← Real.log_div hq.ne' hp.ne'] at hval
  exact hval


/-- **Karamata's uniform convergence theorem**, ratio form: `L(cx)/L(x) → 1` uniformly for `c` in
a compact subinterval of `(0,∞)`. -/
theorem isSlowlyVarying_uniform {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {a b : ℝ} (ha : 0 < a)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, ∀ c ∈ Icc a b, |L (c * x) / L x - 1| ≤ ε := by
  set U : ℝ := max |Real.log a| |Real.log b| with hU
  set δ : ℝ := Real.log (1 + ε) with hδdef
  have hδ : 0 < δ := Real.log_pos (by linarith)
  have hsub : Icc a b ⊆ Icc (Real.exp (-U)) (Real.exp U) := by
    intro c hc
    have hc0 : 0 < c := lt_of_lt_of_le ha hc.1
    constructor
    · have h1 : -U ≤ Real.log a := by
        have := neg_abs_le (Real.log a)
        have h2 : |Real.log a| ≤ U := le_max_left _ _
        linarith
      calc Real.exp (-U) ≤ Real.exp (Real.log a) := Real.exp_le_exp.2 h1
        _ = a := Real.exp_log ha
        _ ≤ c := hc.1
    · rcases le_or_gt b 0 with hb | hb0
      · exact absurd (le_trans hc.1 hc.2) (by linarith)
      · have h1 : Real.log b ≤ U := le_trans (le_abs_self _) (le_max_right _ _)
        calc c ≤ b := hc.2
          _ = Real.exp (Real.log b) := (Real.exp_log hb0).symm
          _ ≤ Real.exp U := Real.exp_le_exp.2 h1
  filter_upwards [isSlowlyVarying_uniform_log hL U hδ, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro c hc
  have hc0 : 0 < c := lt_of_lt_of_le ha hc.1
  have hp : 0 < L x := hL.pos _ hx0
  have hq : 0 < L (c * x) := hL.pos _ (by positivity)
  set r : ℝ := L (c * x) / L x with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hlog := hx c (hsub hc)
  rw [← hr] at hlog
  rw [abs_le] at hlog
  have hup : r ≤ 1 + ε := by
    have h1 : Real.log r ≤ δ := hlog.2
    have := Real.exp_le_exp.2 h1
    rw [Real.exp_log hr0, hδdef, Real.exp_log (by linarith : (0:ℝ) < 1 + ε)] at this
    exact this
  have hlow : 1 / (1 + ε) ≤ r := by
    have h1 : -δ ≤ Real.log r := hlog.1
    have := Real.exp_le_exp.2 h1
    rw [Real.exp_log hr0, hδdef, Real.exp_neg, Real.exp_log (by linarith : (0:ℝ) < 1 + ε)] at this
    rw [one_div]
    exact this
  have hlow' : 1 - ε ≤ r := by
    have hpos : (0 : ℝ) < 1 + ε := by linarith
    have : (1 - ε) ≤ 1 / (1 + ε) := by
      rw [le_div_iff₀ hpos]
      nlinarith [sq_nonneg ε]
    linarith
  rw [abs_le]
  constructor <;> linarith


/-- **Potter's bound.**  Above a threshold the ratio of a slowly varying function at two points is
controlled by an arbitrarily small power of their quotient. -/
theorem isSlowlyVarying_potter {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x y : ℝ, X₀ ≤ x → x ≤ y →
      L y / L x ≤ Real.exp (2 * δ) * (y / x) ^ δ
        ∧ Real.exp (-(2 * δ)) * (x / y) ^ δ ≤ L y / L x := by
  obtain ⟨T₀, hT₀⟩ := isSlowShift_potter (isSlowShift_slowLog hL) hδ
  refine ⟨max (Real.exp T₀) 1, le_max_right _ _, fun x y hx hxy => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hx0 hxy
  have hxT : Real.exp T₀ ≤ x := le_trans (le_max_left _ _) hx
  have hlogx : T₀ ≤ Real.log x := by
    rw [← Real.log_exp T₀]
    exact Real.log_le_log (Real.exp_pos _) hxT
  have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hbound := hT₀ (Real.log x) (Real.log y) hlogx hlogxy
  have hLx : 0 < L x := hL.pos _ hx0
  have hLy : 0 < L y := hL.pos _ hy0
  have hslx : slowLog L (Real.log x) = Real.log (L x) := by
    rw [slowLog, Real.exp_log hx0]
  have hsly : slowLog L (Real.log y) = Real.log (L y) := by
    rw [slowLog, Real.exp_log hy0]
  rw [hslx, hsly, ← Real.log_div hLy.ne' hLx.ne'] at hbound
  have hdiv : 0 < L y / L x := by positivity
  have hratio : 0 < y / x := by positivity
  have hlogdiv : Real.log y - Real.log x = Real.log (y / x) :=
    (Real.log_div hy0.ne' hx0.ne').symm
  rw [hlogdiv] at hbound
  rw [abs_le] at hbound
  have hrpow : (y / x) ^ δ = Real.exp (δ * Real.log (y / x)) := by
    rw [Real.rpow_def_of_pos hratio, mul_comm]
  have hrpow' : (x / y) ^ δ = Real.exp (-(δ * Real.log (y / x))) := by
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < x / y)]
    congr 1
    have hlg : Real.log (x / y) = -Real.log (y / x) := by
      rw [Real.log_div hx0.ne' hy0.ne', Real.log_div hy0.ne' hx0.ne']
      ring
    rw [hlg]
    ring
  constructor
  · have hup : Real.log (L y / L x) ≤ δ * Real.log (y / x) + 2 * δ := by
      nlinarith [hbound.2]
    have := Real.exp_le_exp.2 hup
    rw [Real.exp_log hdiv, Real.exp_add] at this
    rw [hrpow]
    calc L y / L x ≤ Real.exp (δ * Real.log (y / x)) * Real.exp (2 * δ) := this
      _ = Real.exp (2 * δ) * Real.exp (δ * Real.log (y / x)) := by ring
  · have hlow : -(δ * Real.log (y / x)) - 2 * δ ≤ Real.log (L y / L x) := by
      nlinarith [hbound.1]
    have := Real.exp_le_exp.2 hlow
    rw [Real.exp_log hdiv, Real.exp_sub] at this
    rw [hrpow']
    calc Real.exp (-(2 * δ)) * Real.exp (-(δ * Real.log (y / x)))
        = Real.exp (-(δ * Real.log (y / x))) / Real.exp (2 * δ) := by
          rw [Real.exp_neg, div_eq_mul_inv]
          ring
      _ ≤ L y / L x := this

end HTGeometry
