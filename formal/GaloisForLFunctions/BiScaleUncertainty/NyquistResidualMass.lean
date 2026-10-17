import GaloisForLFunctions.BiScaleUncertainty.ExplicitNyquistPolarAndChebyshevFactorialProducer
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Summable mass of the explicit Nyquist polar residual

Zero-based cell `k` is `[log(k+1), log(k+2)]`. Its actual residual integral
has a telescoping radical majorant, giving an unconditional bound on every tail.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistResidualNode (k : ℕ) : ℝ := Real.log ((k + 1 : ℕ) : ℝ)

def nyquistResidualDensity (k : ℕ) (x : ℝ) : ℝ :=
  Real.cosh (x / 2) - nyquistPolarConstant (k + 1)

def nyquistResidualMass (k : ℕ) : ℝ :=
  ∫ x in nyquistResidualNode k..nyquistResidualNode (k + 1), nyquistResidualDensity k x

def nyquistResidualTailScale (N : ℕ) : ℝ := 1 / Real.sqrt ((N + 1 : ℕ) : ℝ)

theorem nyquistResidualNode_zero : nyquistResidualNode 0 = 0 := by
  simp [nyquistResidualNode]

theorem strictMono_nyquistResidualNode : StrictMono nyquistResidualNode := by
  intro i j hij
  apply Real.log_lt_log (by positivity : (0 : ℝ) < (i + 1 : ℕ))
  exact_mod_cast (show i + 1 < j + 1 by omega)

theorem tendsto_nyquistResidualNode : Tendsto nyquistResidualNode atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop
  simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
    Real.tendsto_log_atTop.comp hn

theorem continuous_nyquistResidualDensity (k : ℕ) : Continuous (nyquistResidualDensity k) :=
  (Real.continuous_cosh.comp (continuous_id.div_const 2)).sub continuous_const

theorem nyquistResidualDensity_bounds (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (nyquistResidualNode k) (nyquistResidualNode (k + 1))) :
    0 ≤ nyquistResidualDensity k x ∧
      nyquistResidualDensity k x ≤ 1 / (4 * Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
  apply nyquist_cell_cosh_sub_polarConstant_bounds (by omega : 1 ≤ k + 1)
  simpa only [nyquistResidualNode, Nat.cast_add, Nat.cast_one] using hx

theorem nyquistResidualMass_nonneg (k : ℕ) : 0 ≤ nyquistResidualMass k := by
  apply intervalIntegral.integral_nonneg
    (strictMono_nyquistResidualNode.monotone (by omega : k ≤ k + 1))
  intro x hx
  exact (nyquistResidualDensity_bounds k hx).1

theorem nyquistResidualMass_le (k : ℕ) :
    nyquistResidualMass k ≤
      1 / (4 * ((k + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
  have hab := strictMono_nyquistResidualNode.monotone (show k ≤ k + 1 by omega)
  have hi : IntervalIntegrable (nyquistResidualDensity k) volume
      (nyquistResidualNode k) (nyquistResidualNode (k + 1)) :=
    (continuous_nyquistResidualDensity k).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
    (fun x hx => (nyquistResidualDensity_bounds k hx).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  have hlen : nyquistResidualNode (k + 1) - nyquistResidualNode k ≤
      1 / ((k + 1 : ℕ) : ℝ) := by
    simpa only [nyquistResidualNode, ChebyshevGauge.cellLength, Nat.cast_add, Nat.cast_one] using
      ChebyshevGauge.cellLength_le (by omega : 1 ≤ k + 1)
  calc
    nyquistResidualMass k ≤
        (nyquistResidualNode (k + 1) - nyquistResidualNode k) *
          (1 / (4 * Real.sqrt ((k + 1 : ℕ) : ℝ))) := h
    _ ≤ (1 / ((k + 1 : ℕ) : ℝ)) * (1 / (4 * Real.sqrt ((k + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = _ := by ring

/-- A scalar telescoping majorant valid throughout the positive real range. -/
theorem inverse_sqrt_step_majorant {x : ℝ} (hx : 1 ≤ x) :
    1 / (4 * x * Real.sqrt x) ≤ 1 / Real.sqrt x - 1 / Real.sqrt (x + 1) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x + 1)
  have hx0 : 0 < x := by linarith only [hx]
  have ha : 0 < a := Real.sqrt_pos.mpr hx0
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith only [hx])
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx0.le
  have hb2 : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith only [hx])
  have hb_le : b ≤ 2 * a := by nlinarith only [ha, hb, ha2, hb2, hx]
  have hab : a * b ≤ 2 * x := by
    have hh := mul_le_mul_of_nonneg_left hb_le ha.le
    nlinarith only [hh, ha2]
  have hprod : b * (b + a) ≤ 4 * x := by nlinarith only [hb2, hab, hx]
  have hden : a * b * (b + a) ≤ 4 * x * a := by
    have hh := mul_le_mul_of_nonneg_left hprod ha.le
    nlinarith only [hh]
  change 1 / (4 * x * a) ≤ 1 / a - 1 / b
  calc
    _ ≤ 1 / (a * b * (b + a)) := one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by
      field_simp [ha.ne', hb.ne', (add_pos hb ha).ne']
      nlinarith only [ha2, hb2]

theorem nyquistResidualTailScale_nonneg (N : ℕ) : 0 ≤ nyquistResidualTailScale N := by
  unfold nyquistResidualTailScale
  positivity

theorem nyquistResidualMass_le_scale_sub (k : ℕ) :
    nyquistResidualMass k ≤ nyquistResidualTailScale k - nyquistResidualTailScale (k + 1) := by
  apply (nyquistResidualMass_le k).trans
  simpa only [nyquistResidualTailScale, Nat.cast_add, Nat.cast_one] using
    inverse_sqrt_step_majorant (show (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ k + 1 by omega))

theorem sum_nyquistResidualMass_le_scale_sub (N M : ℕ) :
    (∑ k ∈ Finset.range M, nyquistResidualMass (N + k)) ≤
      nyquistResidualTailScale N - nyquistResidualTailScale (N + M) := by
  calc
    _ ≤ ∑ k ∈ Finset.range M,
        (nyquistResidualTailScale (N + k) - nyquistResidualTailScale (N + k + 1)) :=
      Finset.sum_le_sum (fun k _ => nyquistResidualMass_le_scale_sub (N + k))
    _ = _ := by
      simpa only [Nat.add_assoc, Nat.add_zero] using
        Finset.sum_range_sub' (fun k => nyquistResidualTailScale (N + k)) M

theorem sum_nyquistResidualMass_le_scale (N M : ℕ) :
    (∑ k ∈ Finset.range M, nyquistResidualMass (N + k)) ≤ nyquistResidualTailScale N :=
  (sum_nyquistResidualMass_le_scale_sub N M).trans
    (sub_le_self _ (nyquistResidualTailScale_nonneg (N + M)))

theorem summable_nyquistResidualMass (N : ℕ) : Summable (fun k => nyquistResidualMass (N + k)) :=
  summable_of_sum_range_le (fun k => nyquistResidualMass_nonneg (N + k))
    (sum_nyquistResidualMass_le_scale N)

def nyquistResidualTailMass (N : ℕ) : ℝ := ∑' k, nyquistResidualMass (N + k)

theorem nyquistResidualTailMass_nonneg (N : ℕ) : 0 ≤ nyquistResidualTailMass N :=
  tsum_nonneg (fun k => nyquistResidualMass_nonneg (N + k))

theorem nyquistResidualTailMass_le_scale (N : ℕ) :
    nyquistResidualTailMass N ≤ nyquistResidualTailScale N :=
  (summable_nyquistResidualMass N).tsum_le_of_sum_range_le (sum_nyquistResidualMass_le_scale N)

theorem tendsto_nyquistResidualTailScale : Tendsto nyquistResidualTailScale atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp
    (Real.tendsto_sqrt_atTop.comp hn)
  change Tendsto (fun n : ℕ => 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_one, one_div, Function.comp_def] using hh

theorem tendsto_nyquistResidualTailMass : Tendsto nyquistResidualTailMass atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp tendsto_nyquistResidualTailScale).2 ε hε] with N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (nyquistResidualTailMass_nonneg N)]
  exact (nyquistResidualTailMass_le_scale N).trans_lt hN

end
end GaloisForLFunctions.BiScaleUncertainty
