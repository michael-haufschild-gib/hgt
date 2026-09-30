import GaloisForLFunctions.RHTower.ThetaMovingShellBoundaryLayer
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# First-order errors in the literal moving-shell coordinate

The phase and amplitude have exact first-order limits with global polynomial
bounds. These are inputs to the critical-ray correction, not a sign theorem.
-/

open Real Complex Set Filter Topology

namespace RHTower
noncomputable section

def thetaMovingShellGammaRoot (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (Real.log (1 + u / thetaMovingShellScale n) / 4)

theorem thetaMovingShellGammaPhase_firstOrder_bound (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ thetaMovingShellScale n * (u/2 - thetaMovingShellGammaPhase n u) ∧
    thetaMovingShellScale n * (u/2 - thetaMovingShellGammaPhase n u) ≤ u^2/4 := by
  let a := thetaMovingShellScale n
  let z := u/a
  have ha : 0 < a := thetaMovingShellScale_pos n
  have hz : 0 ≤ z := div_nonneg hu ha.le
  have hrat : z-z^2/2 ≤ 2*z/(z+2) := by
    apply (le_div_iff₀ (by positivity : 0 < z+2)).mpr
    nlinarith [mul_nonneg (sq_nonneg z) hz]
  have hlower := hrat.trans (Real.le_log_one_add_of_nonneg hz)
  have hm := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ a^2/2)
  have hleft : a^2/2*(z-z^2/2) = a*u/2-u^2/4 := by
    dsimp [z]
    field_simp [ha.ne']
    ring
  have hright : a^2/2*Real.log (1+z) = a*thetaMovingShellGammaPhase n u := by
    dsimp [a, z, thetaMovingShellGammaPhase]
    ring
  rw [hleft, hright] at hm
  constructor
  · exact mul_nonneg ha.le (sub_nonneg.mpr (thetaMovingShellGammaPhase_le n hu))
  · change a*(u/2-thetaMovingShellGammaPhase n u) ≤ u^2/4
    nlinarith

theorem tendsto_thetaMovingShellGammaPhase_firstOrder {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => thetaMovingShellScale n *
      (thetaMovingShellGammaPhase n u-u/2)) atTop (𝓝 (-u^2/4)) := by
  have herror : Tendsto (fun n => thetaMovingShellScale n *
      (thetaMovingShellGammaPhase n u-u/2)+u^2/4) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      (tendsto_const_nhds.div_atTop tendsto_thetaMovingShellScale :
        Tendsto (fun n => u^3/thetaMovingShellScale n) atTop (𝓝 0))
    filter_upwards [tendsto_thetaMovingShellScale.eventually (eventually_gt_atTop (2*u))]
      with n hn
    let a := thetaMovingShellScale n
    let z := u/a
    have ha : 0 < a := thetaMovingShellScale_pos n
    have hz : 0 ≤ z := div_nonneg hu ha.le
    have hzhalf : z < 1/2 := by
      apply (div_lt_iff₀ ha).mpr
      change 2*u < a at hn
      linarith
    have ht := Real.abs_log_sub_add_sum_range_le
      (x := -z) (by rw [abs_neg, abs_of_nonneg hz]; linarith) 2
    norm_num [Finset.sum_range_succ, abs_neg, abs_of_nonneg hz] at ht
    have heq : a*(thetaMovingShellGammaPhase n u-u/2)+u^2/4 =
        a^2/2*(-z+z^2/2+Real.log (1+z)) := by
      dsimp [a, z, thetaMovingShellGammaPhase]
      field_simp [(thetaMovingShellScale_pos n).ne']
      ring
    have hden : 0 < 1-z := by linarith
    have htail : z^3/(1-z) ≤ 2*z^3 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [pow_nonneg hz 3]
    change |a*(thetaMovingShellGammaPhase n u-u/2)+u^2/4| ≤ u^3/a
    rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a^2/2)]
    calc
      a^2/2*|-z+z^2/2+Real.log (1+z)| ≤ a^2/2*(z^3/(1-z)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ a^2/2*(2*z^3) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = u^3/a := by dsimp [z]; field_simp [ha.ne']
  convert herror.sub_const (u^2/4) using 1
  · funext n
    ring
  · ring

theorem tendsto_thetaMovingShellGammaRoot (u : ℝ) :
    Tendsto (fun n => thetaMovingShellGammaRoot n u) atTop (𝓝 1) := by
  have hz : Tendsto (fun n => u/thetaMovingShellScale n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_thetaMovingShellScale
  have hb : Tendsto (fun n => 1+u/thetaMovingShellScale n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hz
  simpa [thetaMovingShellGammaRoot, Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp
    ((hb.log one_ne_zero).div_const 4)

theorem one_le_thetaMovingShellGammaRoot (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ thetaMovingShellGammaRoot n u := by
  apply Real.one_le_exp
  exact div_nonneg (Real.log_nonneg
    (le_add_of_nonneg_right (div_nonneg hu (thetaMovingShellScale_pos n).le)))
    (by positivity)

theorem thetaMovingShellGammaRoot_pow_four (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    thetaMovingShellGammaRoot n u ^ 4 = 1+u/thetaMovingShellScale n := by
  unfold thetaMovingShellGammaRoot
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (4 : ℝ)*(Real.log (1+u/thetaMovingShellScale n)/4) =
      Real.log (1+u/thetaMovingShellScale n) := by ring
  rw [he, Real.exp_log (by
    have hz := div_nonneg hu (thetaMovingShellScale_pos n).le
    linarith : 0 < 1+u/thetaMovingShellScale n)]

theorem thetaMovingShellGammaRoot_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    thetaMovingShellGammaRoot n u ≤ 1+u := by
  have ha := thetaMovingShellScale_pos n
  have hz := div_nonneg hu ha.le
  have hlog := Real.log_nonneg (le_add_of_nonneg_right hz)
  calc
    thetaMovingShellGammaRoot n u ≤ Real.exp (Real.log (1+u/thetaMovingShellScale n)) :=
      Real.exp_le_exp.mpr (by change Real.log (1+u/thetaMovingShellScale n)/4 ≤ _; linarith)
    _ = 1+u/thetaMovingShellScale n := Real.exp_log (by positivity)
    _ ≤ 1+u := by linarith [div_le_self hu (one_le_thetaMovingShellScale n)]

theorem thetaMovingShellGammaRoot_firstOrder_eq (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    thetaMovingShellScale n*(thetaMovingShellGammaRoot n u-1) =
      u/(thetaMovingShellGammaRoot n u^3+thetaMovingShellGammaRoot n u^2+
        thetaMovingShellGammaRoot n u+1) := by
  let r := thetaMovingShellGammaRoot n u
  have ha := thetaMovingShellScale_pos n
  have hr : 1 ≤ r := one_le_thetaMovingShellGammaRoot n hu
  have hd : 0 < r^3+r^2+r+1 := by positivity
  have hf : (r-1)*(r^3+r^2+r+1) = u/thetaMovingShellScale n := by
    linear_combination thetaMovingShellGammaRoot_pow_four n hu
  apply (eq_div_iff hd.ne').mpr
  change (thetaMovingShellScale n*(r-1))*(r^3+r^2+r+1) = u
  rw [mul_assoc, hf, mul_div_cancel₀ _ ha.ne']

theorem thetaMovingShellGammaRoot_firstOrder_bound (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ thetaMovingShellScale n*(thetaMovingShellGammaRoot n u-1) ∧
    thetaMovingShellScale n*(thetaMovingShellGammaRoot n u-1) ≤ u/4 := by
  have hr := one_le_thetaMovingShellGammaRoot n hu
  have hr2 : 1 ≤ thetaMovingShellGammaRoot n u^2 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hr 2
  have hr3 : 1 ≤ thetaMovingShellGammaRoot n u^3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hr 3
  constructor
  · exact mul_nonneg (thetaMovingShellScale_pos n).le (sub_nonneg.mpr hr)
  · rw [thetaMovingShellGammaRoot_firstOrder_eq n hu]
    exact div_le_div_of_nonneg_left hu (by positivity) (by linarith)

theorem tendsto_thetaMovingShellGammaRoot_firstOrder {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => thetaMovingShellScale n*(thetaMovingShellGammaRoot n u-1))
      atTop (𝓝 (u/4)) := by
  have hr := tendsto_thetaMovingShellGammaRoot u
  have hd : Tendsto (fun n => thetaMovingShellGammaRoot n u^3+
      thetaMovingShellGammaRoot n u^2+thetaMovingShellGammaRoot n u+1)
      atTop (𝓝 4) := by
    convert (((hr.pow 3).add (hr.pow 2)).add hr).add_const 1 using 1
    norm_num
  have heq : (fun n => thetaMovingShellScale n*(thetaMovingShellGammaRoot n u-1)) =
      (fun n => u/(thetaMovingShellGammaRoot n u^3+
        thetaMovingShellGammaRoot n u^2+thetaMovingShellGammaRoot n u+1)) :=
    funext fun n => thetaMovingShellGammaRoot_firstOrder_eq n hu
  rw [heq]
  exact tendsto_const_nhds.div hd (by norm_num)

theorem thetaMovingShellGammaAmplitude_firstOrder_eq (n : ℕ) (u : ℝ) :
    thetaMovingShellScale n*(thetaMovingShellGammaAmplitude n u-
      2*Real.pi^2*Real.exp (-Real.pi*u)) =
      Real.pi*Real.exp (-Real.pi*u)*
        (2*Real.pi*(thetaMovingShellScale n*(thetaMovingShellGammaRoot n u-1))+
          thetaMovingShellGammaRoot n u*(2*Real.pi*u-3)) := by
  unfold thetaMovingShellGammaAmplitude thetaMovingShellGammaRoot
  field_simp [(thetaMovingShellScale_pos n).ne']
  ring

theorem tendsto_thetaMovingShellGammaAmplitude_firstOrder {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => thetaMovingShellScale n*(thetaMovingShellGammaAmplitude n u-
      2*Real.pi^2*Real.exp (-Real.pi*u))) atTop
      (𝓝 (Real.pi*((5*Real.pi/2)*u-3)*Real.exp (-Real.pi*u))) := by
  have hr := tendsto_thetaMovingShellGammaRoot u
  have hd := tendsto_thetaMovingShellGammaRoot_firstOrder hu
  have hlim := ((hd.const_mul (2*Real.pi)).add (hr.mul_const (2*Real.pi*u-3))).const_mul
    (Real.pi*Real.exp (-Real.pi*u))
  convert hlim using 1
  · funext n
    exact thetaMovingShellGammaAmplitude_firstOrder_eq n u
  · ring

theorem abs_thetaMovingShellGammaAmplitude_firstOrder_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |thetaMovingShellScale n*(thetaMovingShellGammaAmplitude n u-
      2*Real.pi^2*Real.exp (-Real.pi*u))| ≤
        Real.pi*(3*Real.pi+3)*(1+u)^2*Real.exp (-Real.pi*u) := by
  let r := thetaMovingShellGammaRoot n u
  let d := thetaMovingShellScale n*(r-1)
  have hr0 : 0 ≤ r := (zero_le_one.trans (one_le_thetaMovingShellGammaRoot n hu))
  have hr : r ≤ 1+u := thetaMovingShellGammaRoot_le n hu
  have hd : 0 ≤ d ∧ d ≤ u/4 := thetaMovingShellGammaRoot_firstOrder_bound n hu
  have hd0 := hd.1
  have hsmall : |r*(2*Real.pi*u-3)| ≤ r*(2*Real.pi*u+3) := by
    rw [abs_mul, abs_of_nonneg hr0]
    calc
      r*|2*Real.pi*u-3| ≤ r*(|2*Real.pi*u|+|3|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hr0
      _ = r*(2*Real.pi*u+3) := by rw [abs_of_nonneg (by positivity)]; norm_num
  have hfirst : 2*Real.pi*d ≤ Real.pi*(1+u)^2 := by
    have hm := mul_le_mul_of_nonneg_left hd.2 (by positivity : 0 ≤ 2*Real.pi)
    have hu2 : u/2 ≤ (1+u)^2 := by nlinarith [sq_nonneg u]
    have hs := mul_le_mul_of_nonneg_left hu2 Real.pi_pos.le
    nlinarith
  have hsecond : r*(2*Real.pi*u+3) ≤ (2*Real.pi+3)*(1+u)^2 := by
    have hm := mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ 2*Real.pi*u+3)
    have hp : 2*Real.pi*u+3 ≤ (2*Real.pi+3)*(1+u) := by nlinarith [Real.pi_pos]
    have hs := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1+u)
    nlinarith
  have hsum : |2*Real.pi*d+r*(2*Real.pi*u-3)| ≤ (3*Real.pi+3)*(1+u)^2 := by
    calc
      |2*Real.pi*d+r*(2*Real.pi*u-3)| ≤ |2*Real.pi*d|+|r*(2*Real.pi*u-3)| :=
        abs_add_le _ _
      _ ≤ 2*Real.pi*d+r*(2*Real.pi*u+3) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi*d)]
        linarith [hsmall]
      _ ≤ (3*Real.pi+3)*(1+u)^2 := by nlinarith
  rw [thetaMovingShellGammaAmplitude_firstOrder_eq, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ Real.pi*Real.exp (-Real.pi*u))]
  have hs := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ Real.pi*Real.exp (-Real.pi*u))
  convert hs using 1 <;> first | rfl | ring

theorem tendsto_thetaMovingShellCriticalPhase_firstOrder (s : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => thetaMovingShellScale n *
      ((2*Real.pi+s/thetaMovingShellScale n)*thetaMovingShellGammaPhase n u-Real.pi*u))
      atTop (𝓝 (-Real.pi*u^2/2+s*u/2)) := by
  have hq := tendsto_thetaMovingShellGammaPhase u
  have hd := tendsto_thetaMovingShellGammaPhase_firstOrder hu
  convert (hd.const_mul (2*Real.pi)).add (hq.const_mul s) using 1
  · funext n
    field_simp [(thetaMovingShellScale_pos n).ne']
    ring
  · ring

theorem abs_thetaMovingShellCriticalPhase_firstOrder_le (n : ℕ) (s : ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    |thetaMovingShellScale n *
      ((2*Real.pi+s/thetaMovingShellScale n)*thetaMovingShellGammaPhase n u-Real.pi*u)| ≤
      Real.pi*u^2/2+|s| * u/2 := by
  let q := thetaMovingShellGammaPhase n u
  let d := thetaMovingShellScale n*(u/2-q)
  have hq0 : 0 ≤ q := thetaMovingShellGammaPhase_nonneg n hu
  have hq : q ≤ u/2 := thetaMovingShellGammaPhase_le n hu
  have hd : 0 ≤ d ∧ d ≤ u^2/4 := thetaMovingShellGammaPhase_firstOrder_bound n hu
  have hd0 := hd.1
  have heq : thetaMovingShellScale n *
      ((2*Real.pi+s/thetaMovingShellScale n)*q-Real.pi*u) = -2*Real.pi*d+s*q := by
    dsimp [d]
    field_simp [(thetaMovingShellScale_pos n).ne']
    ring
  rw [heq]
  calc
    |-2*Real.pi*d+s*q| ≤ |-2*Real.pi*d|+|s*q| := abs_add_le _ _
    _ = 2*Real.pi*d+|s| * q := by
      rw [show -2*Real.pi*d = -(2*Real.pi*d) by ring, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi*d), abs_mul, abs_of_nonneg hq0]
    _ ≤ Real.pi*u^2/2+|s| * u/2 := by
      have hm := mul_le_mul_of_nonneg_left hd.2 (by positivity : 0 ≤ 2*Real.pi)
      have hs := mul_le_mul_of_nonneg_left hq (abs_nonneg s)
      nlinarith

end
end RHTower
