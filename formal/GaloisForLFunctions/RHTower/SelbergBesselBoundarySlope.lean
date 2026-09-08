import GaloisForLFunctions.HTGeometry.BesselArgumentDerivative
import GaloisForLFunctions.HTGeometry.BesselOrderPositiveComparison
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual critical Bessel boundary slope

For the source-defined Schlaefli integrals, `q(s)=s*K_1(s)/K_0(s)` obeys
`q'(s)=(q(s)^2-s^2)/s` and is strictly increasing on the positive ray.
Its logarithmic reparameterization has range exactly the positive ray: a
hypothetical positive lower bound contradicts the Riccati equation on a
sufficiently long interval toward negative logarithmic height. No small-argument
asymptotic or numerical estimate is assumed.

There is a unique transition with `q(s)=1/2`, at an argument strictly between
zero and one half. The actual critical profile `exp(t/2)*K_0(exp(a+t))` solves
the critical nonzero-mode ODE. Its outgoing height slope has exactly this sign
transition. Relating this mode to every Maass Fourier coefficient and gluing its
boundary response to the compact core remain separate obligations.
-/

open Filter Set Topology
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.RHTower.SelbergBesselSlope
noncomputable section

/-- Real part of the existing actual modified Bessel integral. -/
def K (j s : ℝ) : ℝ := (modifiedBesselKOrder s (j : ℂ)).re

/-- On positive arguments this is the original positive real Schlaefli integral. -/
theorem K_eq_real {s : ℝ} (hs : 0 < s) (j : ℝ) :
    K j s = realModifiedBesselKOrder s j := by
  simp only [K, modifiedBesselKOrder_ofReal hs, Complex.ofReal_re]

/-- Strict positivity supplied by the source integral. -/
theorem K_pos {s : ℝ} (hs : 0 < s) (j : ℝ) : 0 < K j s :=
  modifiedBesselKOrder_real_pos hs j

/-- Strict comparison of the original order-zero and order-one integrals. -/
theorem K_zero_lt_one {s : ℝ} (hs : 0 < s) : K 0 s < K 1 s := by
  rw [K_eq_real hs, K_eq_real hs]
  exact realModifiedBesselKOrder_zero_lt_one hs

/-- The actual order-zero argument derivative. -/
theorem K_zero_hasDerivAt {s : ℝ} (hs : 0 < s) : HasDerivAt (K 0) (-K 1 s) s := by
  have hc := _root_.RHTower.d4BM_hasDerivAt_modifiedBesselKOrder_argument hs (0 : ℂ)
  simp only [zero_add, zero_sub, modifiedBesselKOrder_neg] at hc
  have he (b : ℂ) : -(1 / 2 : ℂ) * (b + b) = -b := by ring
  simp only [he] at hc
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hc
  convert hr using 1 <;> try rfl

/-- The actual order-one derivative, using the source recurrence. -/
theorem K_one_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (K 1) (-(K 0 s + K 1 s / s)) s := by
  have hc := _root_.RHTower.d4BM_hasDerivAt_modifiedBesselKOrder_argument hs (1 : ℂ)
  have hrec := modifiedBesselKOrder_add_one hs (1 : ℂ)
  rw [hrec] at hc
  simp only [sub_self, mul_one] at hc
  have he (b c : ℂ) : -(1 / 2 : ℂ) * (b + (2 / (s : ℂ)) * c + b) = -(b + c / s) := by ring
  simp only [he] at hc
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hc
  convert hr using 1 <;> try rfl
  simp only [Complex.reCLM_apply, Complex.neg_re, Complex.add_re,
    Complex.div_ofReal_re, K, Complex.ofReal_zero, Complex.ofReal_one]

/-- Dimensionless logarithmic slope of the order-zero carrier. -/
def slope (s : ℝ) : ℝ := s * K 1 s / K 0 s

/-- The Bessel slope strictly exceeds its positive argument. -/
theorem argument_lt_slope {s : ℝ} (hs : 0 < s) : s < slope s := by
  apply (lt_div_iff₀ (K_pos hs 0)).mpr
  exact mul_lt_mul_of_pos_left (K_zero_lt_one hs) hs

/-- Exact Riccati derivative of the source-defined Bessel ratio. -/
theorem slope_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt slope ((slope s ^ 2 - s ^ 2) / s) s := by
  have hk0 := (K_pos hs 0).ne'
  convert (((hasDerivAt_id s).mul (K_one_hasDerivAt hs)).div (K_zero_hasDerivAt hs) hk0) using 1 <;> try rfl
  dsimp only [slope, id_eq, Pi.mul_apply]
  field_simp
  ring

/-- The source order comparison forces a strictly positive derivative. -/
theorem slope_deriv_pos {s : ℝ} (hs : 0 < s) : 0 < deriv slope s := by
  rw [(slope_hasDerivAt hs).deriv]
  apply div_pos _ hs
  nlinarith [argument_lt_slope hs]

/-- Strict increase throughout the positive ray. -/
theorem slope_strictMonoOn : StrictMonoOn slope (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro s hs
    exact (slope_hasDerivAt hs).continuousAt.continuousWithinAt
  · intro s hs
    exact slope_deriv_pos (interior_subset hs)

/-- The dimensionless slope in logarithmic argument. -/
def logSlope (t : ℝ) : ℝ := slope (Real.exp t)

/-- Positivity at every logarithmic argument. -/
theorem logSlope_pos (t : ℝ) : 0 < logSlope t :=
  (Real.exp_pos t).trans (argument_lt_slope (Real.exp_pos t))

/-- The Riccati equation without a singular denominator. -/
theorem logSlope_hasDerivAt (t : ℝ) :
    HasDerivAt logSlope (logSlope t ^ 2 - Real.exp t ^ 2) t := by
  have hh := (slope_hasDerivAt (Real.exp_pos t)).comp t (Real.hasDerivAt_exp t)
  convert hh using 1 <;> try rfl
  dsimp only [logSlope]
  field_simp

/-- Strict increase in logarithmic argument. -/
theorem logSlope_strictMono : StrictMono logSlope := by
  intro s t hst
  exact slope_strictMonoOn (Real.exp_pos s) (Real.exp_pos t) (Real.exp_lt_exp.mpr hst)

/-- C¹ regularity needed for the later flux integral. -/
theorem logSlope_contDiff : ContDiff ℝ 1 logSlope := by
  apply contDiff_one_iff_deriv.mpr
  have hc : Continuous logSlope :=
    continuous_iff_continuousAt.mpr (fun t => (logSlope_hasDerivAt t).continuousAt)
  refine ⟨fun t => (logSlope_hasDerivAt t).differentiableAt, ?_⟩
  have he : deriv logSlope = fun t => logSlope t ^ 2 - Real.exp t ^ 2 :=
    funext (fun t => (logSlope_hasDerivAt t).deriv)
  rw [he]
  exact (hc.pow 2).sub (Real.continuous_exp.pow 2)

/-- There is no positive lower bound: the Riccati law rules it out on a long left interval. -/
theorem exists_logSlope_lt {d : ℝ} (hd : 0 < d) : ∃ t, logSlope t < d := by
  by_contra hn
  push Not at hn
  let T := Real.log (d / 2)
  let c := d ^ 2 / 2
  have hc : 0 < c := div_pos (sq_pos_of_pos hd) (by linarith)
  have hT : Real.exp T = d / 2 := Real.exp_log (by positivity)
  let F := fun t => logSlope t - c * t
  have hF : ∀ t, HasDerivAt F (logSlope t ^ 2 - Real.exp t ^ 2 - c) t := by
    intro t
    convert (logSlope_hasDerivAt t).sub ((hasDerivAt_id t).const_mul c) using 1 <;> try rfl
    simp only [mul_one]
  have hm : MonotoneOn F (Iic T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic T)
    · intro t _
      exact (hF t).continuousAt.continuousWithinAt
    · intro t _
      exact (hF t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hF t).deriv]
      have htT : t ∈ Iic T := interior_subset ht
      have he : Real.exp t ≤ d / 2 := by rw [← hT]; exact Real.exp_le_exp.mpr htT
      dsimp only [c]
      nlinarith [hn t, Real.exp_pos t]
  let t := T - (logSlope T + 1) / c
  have ht : t ≤ T := sub_le_self _ (div_nonneg (by linarith [logSlope_pos T]) hc.le)
  have hm' := hm ht (le_refl T) ht
  have hcdiv : c * ((logSlope T + 1) / c) = logSlope T + 1 := by field_simp
  dsimp only [F, t] at hm'
  nlinarith [logSlope_pos t]

/-- Every positive target slope is attained exactly once. -/
theorem existsUnique_logSlope (d : ℝ) (hd : 0 < d) : ∃! t, logSlope t = d := by
  obtain ⟨a, ha⟩ := exists_logSlope_lt hd
  let b := Real.log d
  have hb : d < logSlope b := by
    simpa only [logSlope, b, Real.exp_log hd] using argument_lt_slope hd
  have hab : a ≤ b := by
    by_contra hn
    have hh := logSlope_strictMono (lt_of_not_ge hn)
    linarith
  have hcont : Continuous logSlope :=
    continuous_iff_continuousAt.mpr (fun t => (logSlope_hasDerivAt t).continuousAt)
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨ha.le, hb.le⟩
  refine ⟨t, ht, ?_⟩
  intro u hu
  exact logSlope_strictMono.injective (hu.trans ht.symm)

/-- Exact range, proved from the actual differential equation and positivity. -/
theorem range_logSlope : Set.range logSlope = Ioi 0 := by
  ext d
  constructor
  · rintro ⟨t, rfl⟩
    exact logSlope_pos t
  · intro hd
    obtain ⟨t, ht, _⟩ := existsUnique_logSlope d hd
    exact ⟨t, ht⟩

/-- The unique logarithmic argument with dimensionless slope one half. -/
def transition : ℝ := Classical.choose (existsUnique_logSlope (1 / 2) (by linarith))

/-- The selected transition satisfies its defining equality. -/
theorem transition_eq : logSlope transition = 1 / 2 :=
  (Classical.choose_spec (existsUnique_logSlope (1 / 2) (by linarith))).1

/-- Exact classification below the transition. -/
theorem logSlope_lt_half_iff (t : ℝ) : logSlope t < 1 / 2 ↔ t < transition := by
  rw [← transition_eq]
  exact logSlope_strictMono.lt_iff_lt

/-- The transition improves the elementary sufficient cutoff strictly. -/
theorem transition_lt_log_half : transition < Real.log (1 / 2) := by
  apply logSlope_strictMono.lt_iff_lt.mp
  rw [transition_eq]
  simpa only [logSlope, Real.exp_log (by linarith : (0 : ℝ) < 1 / 2)] using
    argument_lt_slope (by linarith : (0 : ℝ) < 1 / 2)

/-- The transition argument lies strictly between zero and one half. -/
theorem transition_argument_bounds : 0 < Real.exp transition ∧ Real.exp transition < 1 / 2 := by
  refine ⟨Real.exp_pos _, ?_⟩
  simpa only [Real.exp_log (by linarith : (0 : ℝ) < 1 / 2)] using
    Real.exp_lt_exp.mpr transition_lt_log_half

/-- Actual critical nonzero-mode profile at frequency `exp(a)`, in logarithmic height. -/
def logMode (a t : ℝ) : ℝ := Real.exp (t / 2) * K 0 (Real.exp (a + t))

/-- The actual critical profile has no zeros. -/
theorem logMode_pos (a t : ℝ) : 0 < logMode a t :=
  mul_pos (Real.exp_pos _) (K_pos (Real.exp_pos _) 0)

/-- Its actual first derivative is the profile times the logarithmic slope. -/
theorem logMode_hasDerivAt (a t : ℝ) :
    HasDerivAt (logMode a) ((1 / 2 - logSlope (a + t)) * logMode a t) t := by
  have he := ((hasDerivAt_id t).div_const 2).exp
  have hk := (K_zero_hasDerivAt (Real.exp_pos (a + t))).comp t
    (((hasDerivAt_id t).const_add a).exp)
  convert he.mul hk using 1 <;> try rfl
  simp only [logMode, logSlope, slope, id_eq, Function.comp_apply]
  have hK := (K_pos (Real.exp_pos (a + t)) 0).ne'
  field_simp
  ring

/-- Its actual second derivative. -/
theorem logMode_second_hasDerivAt (a t : ℝ) :
    HasDerivAt (deriv (logMode a))
      ((1 / 4 - logSlope (a + t) + Real.exp (a + t) ^ 2) * logMode a t) t := by
  have hfun : deriv (logMode a) = fun s => (1 / 2 - logSlope (a + s)) * logMode a s :=
    funext (fun s => (logMode_hasDerivAt a s).deriv)
  rw [hfun]
  have hq := (logSlope_hasDerivAt (a + t)).comp t ((hasDerivAt_id t).const_add a)
  convert (hq.const_sub (1 / 2)).mul (logMode_hasDerivAt a t) using 1 <;> try rfl
  simp only [mul_one, Function.comp_apply]
  ring

/-- The original profile solves the critical logarithmic-height mode equation. -/
theorem logMode_critical_equation (a t : ℝ) :
    deriv (deriv (logMode a)) t - deriv (logMode a) t =
      (Real.exp (a + t) ^ 2 - 1 / 4) * logMode a t := by
  rw [(logMode_second_hasDerivAt a t).deriv, (logMode_hasDerivAt a t).deriv]
  ring

/-- Negative logarithmic derivative converted from log height to physical height. -/
def outgoing (a t : ℝ) : ℝ := -deriv (logMode a) t / (Real.exp t * logMode a t)

/-- Exact outgoing boundary coefficient. -/
theorem outgoing_eq (a t : ℝ) :
    outgoing a t = (logSlope (a + t) - 1 / 2) / Real.exp t := by
  rw [outgoing, (logMode_hasDerivAt a t).deriv]
  have hM := (logMode_pos a t).ne'
  field_simp
  ring

/-- The outgoing coefficient is negative exactly below the transition. -/
theorem outgoing_neg_iff (a t : ℝ) : outgoing a t < 0 ↔ a + t < transition := by
  rw [outgoing_eq, div_lt_iff₀ (Real.exp_pos t), zero_mul, sub_neg, logSlope_lt_half_iff]

/-- Its only zero is the transition. -/
theorem outgoing_zero_iff (a t : ℝ) : outgoing a t = 0 ↔ a + t = transition := by
  rw [outgoing_eq, div_eq_zero_iff, or_iff_left (Real.exp_ne_zero t), sub_eq_zero, ← transition_eq]
  exact logSlope_strictMono.injective.eq_iff

/-- It is positive exactly above the transition. -/
theorem outgoing_pos_iff (a t : ℝ) : 0 < outgoing a t ↔ transition < a + t := by
  rw [outgoing_eq, lt_div_iff₀ (Real.exp_pos t), zero_mul, sub_pos, ← transition_eq]
  exact logSlope_strictMono.lt_iff_lt

/-- At every positive frequency the actual boundary coefficient takes both signs. -/
theorem outgoing_has_both_signs (a : ℝ) :
    outgoing a (transition - a - 1) < 0 ∧ 0 < outgoing a (transition - a + 1) := by
  rw [outgoing_neg_iff, outgoing_pos_iff]
  constructor <;> linarith

end
end GaloisForLFunctions.RHTower.SelbergBesselSlope
