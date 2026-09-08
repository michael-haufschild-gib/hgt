import GaloisForLFunctions.RHTower.ZetaFisherVariance
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# An analytic lower bound for the zeta logarithmic moment at 3/2

The complete positive logarithmic series dominates its decreasing integral
tail from two. An exact antiderivative and its vanishing boundary term give
a strict rational lower bound without truncating the source series.
-/

noncomputable section
open Filter Set Topology MeasureTheory
namespace RHTower

private def logMomentTail (x : ℝ) : ℝ := Real.log x*x^(-(3/2:ℝ))
private def logMomentPrimitive (x : ℝ) : ℝ := -(2*Real.log x+4)*x^(-(1/2:ℝ))

private lemma rpow_raise_one {x : ℝ} (hx : 0<x) (r : ℝ) :
    x^(r+1)=x^r*x := by rw [Real.rpow_add hx,Real.rpow_one]

private lemma tail_deriv {x : ℝ} (hx : 0<x) :
    HasDerivAt logMomentTail ((1-(3/2)*Real.log x)*x^(-(5/2:ℝ))) x := by
  have h := (Real.hasDerivAt_log hx.ne').mul
    (Real.hasDerivAt_rpow_const (p := -(3/2:ℝ)) (Or.inl hx.ne'))
  convert! h using 1
  norm_num
  have hp : x^(-(3/2:ℝ))=x^(-(5/2:ℝ))*x := by
    convert rpow_raise_one hx (-(5/2)) using 1; norm_num
  rw [hp]
  field_simp
  ring

private lemma primitive_deriv {x : ℝ} (hx : 0<x) :
    HasDerivAt logMomentPrimitive (logMomentTail x) x := by
  have h := (((Real.hasDerivAt_log hx.ne').const_mul 2).add_const 4).neg.mul
    (Real.hasDerivAt_rpow_const (p := -(1/2:ℝ)) (Or.inl hx.ne'))
  convert! h using 1
  norm_num
  have hp : x^(-(1/2:ℝ))=x^(-(3/2:ℝ))*x := by
    convert rpow_raise_one hx (-(3/2)) using 1; norm_num
  rw [hp]
  dsimp [logMomentTail]
  field_simp
  ring

private lemma primitive_tendsto : Tendsto logMomentPrimitive atTop (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => Real.log x*x^(-(1/2:ℝ))) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [Real.rpow_neg hx.le,div_eq_mul_inv]
  have hp := tendsto_rpow_neg_atTop (y := 1/2) (by norm_num)
  convert ((hl.const_mul 2).add (hp.const_mul 4)).neg using 1
  · ext x
    dsimp [logMomentPrimitive]
    ring
  · norm_num

private lemma tail_nonneg {x : ℝ} (hx : 1≤x) : 0≤logMomentTail x := by
  exact mul_nonneg (Real.log_nonneg hx) (Real.rpow_nonneg (by linarith) _)

private lemma tail_antitone : AntitoneOn logMomentTail (Ici (2:ℝ)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 2)
    (fun x hx => (tail_deriv (by linarith [show (2:ℝ)≤x from hx])).continuousAt.continuousWithinAt)
    (fun x hx => (tail_deriv (by simp only [interior_Ici,mem_Ioi] at hx; linarith)).hasDerivWithinAt)
  intro x hx
  have hx2 : 2<x := by simpa only [interior_Ici,mem_Ioi] using hx
  have hl : (2/3:ℝ) < Real.log x := by
    have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hx2.le
    linarith [Real.log_two_gt_d9]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)

/-- The full positive logarithmic Dirichlet series at 3/2 exceeds a strict
rational bound, by a monotone integral comparison of its infinite tail. -/
theorem eulerLogMass_three_halves_gt : (64/17:ℝ)<eulerLogMass (3/2) := by
  have hs : Summable (fun n : ℕ => logMomentTail n) := by
    simpa only [logMomentTail,pow_one] using
      summable_log_natCast_pow_mul_rpow_neg 1 (σ := 3/2) (by norm_num)
  have hi : (∫ x in Ioi (2:ℝ),logMomentTail x) = (2*Real.log 2+4)/Real.sqrt 2 := by
    have h := integral_Ioi_of_hasDerivAt_of_nonneg'
      (fun x (hx : x∈Ici (2:ℝ)) => primitive_deriv (by linarith [show (2:ℝ)≤x from hx]))
      (fun x hx => tail_nonneg (by linarith [show (2:ℝ)<x from hx])) primitive_tendsto
    rw [h]
    dsimp [logMomentPrimitive]
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.sqrt_eq_rpow]
    ring
  have hbound := tail_antitone.integral_le_tsum_comp_add 2 hs
    (fun x hx => tail_nonneg (by linarith [show (2:ℝ)<x by exact_mod_cast hx]))
  norm_num only [Nat.cast_ofNat] at hbound
  rw [hi] at hbound
  have he : (∑'n : ℕ,logMomentTail (n+2:ℕ))=eulerLogMass (3/2) := by
    have ht := hs.sum_add_tsum_nat_add 2
    norm_num [logMomentTail,Finset.sum_range_succ] at ht
    simp only [logMomentTail,Nat.cast_add,Nat.cast_ofNat]
    rw [ht]
    simpa only [logMomentTail,pow_one,eulerLogPowMass_one] using
      tsum_log_natCast_pow_eq_eulerLogPowMass (k := 1) (σ := 3/2) (by norm_num) (by norm_num)
  rw [he] at hbound
  apply lt_of_lt_of_le _ hbound
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp : (0:ℝ)<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hu : Real.sqrt 2 < 17/12 := by nlinarith
  apply (lt_div_iff₀ hp).mpr
  have hl : (2/3:ℝ)<Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith

end RHTower
