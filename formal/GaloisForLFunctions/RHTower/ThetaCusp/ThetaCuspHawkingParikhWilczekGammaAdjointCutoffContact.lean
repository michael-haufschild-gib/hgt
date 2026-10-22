import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaReversibleDensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Literal reciprocal-cutoff adjoint contact

The two displacement cutoffs have a retained contact tending to `2 * log x`.
An admitted exponential remainder has norm bounded by the cutoff interval
length. This closes the literal limit, not an operator adjoint or a domain
identification. No stationarity or Xi occurrence is asserted.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

def pwGammaAdjointCutoffLower (x delta : ℝ) : ℝ := delta/(x*(x-delta))
def pwGammaAdjointCutoffContact (x delta : ℝ) : ℝ :=
  ∫ h in pwGammaAdjointCutoffLower x delta..delta, Real.exp (-h)/h

theorem pwGammaExponentialRemainder_norm_le {h : ℝ} (hh : 0<h) :
    ‖(Real.exp (-h)-1)/h‖ ≤ 1 := by
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh.le)
  rw [Real.norm_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr he) hh.le),
    ← neg_div, neg_sub]
  apply (div_le_iff₀ hh).mpr
  have ht := Real.add_one_le_exp (-h)
  linarith

theorem pwGammaExponentialContact_error_bound {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ‖(∫ h in a..b, Real.exp (-h)/h)-Real.log (b/a)‖ ≤ |b-a| := by
  have hi : ContinuousOn (fun h : ℝ => h) (uIcc a b) := continuousOn_id
  have hn : ∀ h ∈ uIcc a b, h≠0 := by
    intro h hh
    exact ne_of_gt ((lt_min ha hb).trans_le hh.1)
  have hf : IntervalIntegrable (fun h : ℝ => Real.exp (-h)/h) volume a b :=
    (hi.neg.rexp.div hi hn).intervalIntegrable
  have hg : IntervalIntegrable (fun h : ℝ => 1/h) volume a b :=
    (continuousOn_const.div hi hn).intervalIntegrable
  rw [← integral_one_div_of_pos ha hb, ← intervalIntegral.integral_sub hf hg]
  simp_rw [← sub_div]
  have ht := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun h : ℝ => (Real.exp (-h)-1)/h) (C := 1) (a := a) (b := b) (by
      intro h hh
      exact pwGammaExponentialRemainder_norm_le ((lt_min ha hb).trans hh.1))
  simpa only [one_mul] using ht

theorem pwGammaAdjointCutoffLower_pos {x delta : ℝ} (hx : 0<x)
    (hd : 0<delta) (hdx : delta<x) : 0 < pwGammaAdjointCutoffLower x delta :=
  div_pos hd (mul_pos hx (sub_pos.mpr hdx))

theorem pwGammaAdjointCutoffLower_displacement {x delta : ℝ}
    (hx : x≠0) (hdx : x-delta≠0) :
    (x-delta)⁻¹-x⁻¹ = pwGammaAdjointCutoffLower x delta := by
  unfold pwGammaAdjointCutoffLower
  field_simp
  ring

theorem pwGammaAdjointCutoffLower_tendsto {x : ℝ} (hx : 0<x) :
    Tendsto (pwGammaAdjointCutoffLower x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hd : Tendsto (fun d : ℝ => d) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht := hd.div (tendsto_const_nhds.mul (tendsto_const_nhds.sub hd))
    (by positivity : x*(x-0)≠0)
  change Tendsto (fun d : ℝ => d/(x*(x-d))) (𝓝[>] (0:ℝ)) (𝓝 0)
  simpa only [Pi.div_def, zero_div] using ht

theorem pwGammaAdjointCutoffContact_error_bound {x delta : ℝ} (hx : 0<x)
    (hd : 0<delta) (hdx : delta<x) :
    ‖pwGammaAdjointCutoffContact x delta-Real.log (x*(x-delta))‖ ≤
      |delta-pwGammaAdjointCutoffLower x delta| := by
  have hr : delta/pwGammaAdjointCutoffLower x delta = x*(x-delta) := by
    unfold pwGammaAdjointCutoffLower
    field_simp
  have ht := pwGammaExponentialContact_error_bound (pwGammaAdjointCutoffLower_pos hx hd hdx) hd
  rw [hr] at ht
  exact ht

theorem pwGammaAdjointCutoffContact_tendsto {x : ℝ} (hx : 0<x) :
    Tendsto (pwGammaAdjointCutoffContact x) (𝓝[>] (0:ℝ)) (𝓝 (2*Real.log x)) := by
  have hd : Tendsto (fun d : ℝ => d) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ha := pwGammaAdjointCutoffLower_tendsto hx
  have hlength : Tendsto (fun d => |d-pwGammaAdjointCutoffLower x d|)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [sub_zero, abs_zero] using (hd.sub ha).abs
  have herr : Tendsto (fun d => pwGammaAdjointCutoffContact x d-Real.log (x*(x-d)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun d => norm_nonneg _) ?_ hlength
    filter_upwards [self_mem_nhdsWithin, hd.eventually_lt_const hx] with d hd0 hdx
    exact pwGammaAdjointCutoffContact_error_bound hx hd0 hdx
  have hp : Tendsto (fun d : ℝ => x*(x-d)) (𝓝[>] (0:ℝ)) (𝓝 (x*x)) := by
    simpa only [sub_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.sub hd)
  have hl := (Real.continuousAt_log (mul_ne_zero hx.ne' hx.ne')).tendsto.comp hp
  rw [Real.log_mul hx.ne' hx.ne', ← two_mul] at hl
  have ht := herr.add hl
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using ht

end
end RHTower
