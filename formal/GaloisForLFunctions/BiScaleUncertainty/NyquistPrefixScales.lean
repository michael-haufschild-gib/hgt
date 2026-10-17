import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightCellAsymptotic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Explicit telescoping scales for critical and supercritical prefixes -/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistPowerIncrement (r : ℝ) (k : ℕ) : ℝ :=
  ((k + 2 : ℕ) : ℝ) ^ r - ((k + 1 : ℕ) : ℝ) ^ r

theorem nyquistPowerIncrement_pos {r : ℝ} (hr : 0 < r) (k : ℕ) :
    0 < nyquistPowerIncrement r k := by
  apply sub_pos.mpr
  apply Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ (k + 1 : ℕ)) _ hr
  exact_mod_cast (show k + 1 < k + 2 by omega)

theorem tendsto_nyquistPowerIncrement_normalized (r : ℝ) :
    Tendsto (fun k => nyquistPowerIncrement r k /
      ((k + 1 : ℕ) : ℝ) ^ (r - 1)) atTop (𝓝 r) := by
  have hn : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hd := (Real.hasDerivAt_rpow_const (p := r)
    (Or.inl one_ne_zero : (1 : ℝ) ≠ 0 ∨ 1 ≤ r)).tendsto_slope_zero_right
  have ht := hd.comp (tendsto_inv_atTop_nhdsGT_zero.comp hn)
  simp only [Function.comp_def, smul_eq_mul, inv_inv, Real.one_rpow, mul_one] at ht
  apply ht.congr'
  filter_upwards with k
  have hnpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hnexp := (Real.rpow_pos_of_pos hnpos r).ne'
  have he : ((k + 2 : ℕ) : ℝ) =
      ((k + 1 : ℕ) : ℝ) * (1 + ((k + 1 : ℕ) : ℝ)⁻¹) := by
    field_simp
    push_cast
    ring
  unfold nyquistPowerIncrement
  rw [he, Real.mul_rpow hnpos.le (by positivity), Real.rpow_sub hnpos, Real.rpow_one]
  field_simp

theorem sum_nyquistPowerIncrement (r : ℝ) (N M : ℕ) :
    (∑ k ∈ Finset.range M, nyquistPowerIncrement r (N + k)) =
      ((N + M + 1 : ℕ) : ℝ) ^ r - ((N + 1 : ℕ) : ℝ) ^ r := by
  simpa only [nyquistPowerIncrement, Nat.add_assoc, Nat.zero_add, Nat.add_zero,
    Nat.reduceAdd] using Finset.sum_range_sub (fun k => ((N + k + 1 : ℕ) : ℝ) ^ r) M

theorem sum_nyquistWeightCellWidth (N M : ℕ) :
    (∑ k ∈ Finset.range M, nyquistWeightCellWidth (N + k)) =
      nyquistResidualNode (N + M) - nyquistResidualNode N := by
  simpa only [nyquistWeightCellWidth, Nat.add_assoc, Nat.add_zero] using
    Finset.sum_range_sub (fun k => nyquistResidualNode (N + k)) M

theorem tendsto_sum_nyquistPowerIncrement {r : ℝ} (hr : 0 < r) (N : ℕ) :
    Tendsto (fun M => ∑ k ∈ Finset.range M, nyquistPowerIncrement r (N + k))
      atTop atTop := by
  have hn : Tendsto (fun M : ℕ => ((N + M + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.add_comm N, Nat.add_assoc, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat (N + 1))
  simpa only [sum_nyquistPowerIncrement, sub_eq_add_neg, Function.comp_def] using
    tendsto_atTop_add_const_right atTop (-((N + 1 : ℕ) : ℝ) ^ r)
      ((tendsto_rpow_atTop hr).comp hn)

theorem tendsto_sum_nyquistWeightCellWidth (N : ℕ) :
    Tendsto (fun M => ∑ k ∈ Finset.range M, nyquistWeightCellWidth (N + k))
      atTop atTop := by
  have hn : Tendsto (fun M => nyquistResidualNode (N + M)) atTop atTop := by
    simpa only [Nat.add_comm N, Function.comp_def] using
      tendsto_nyquistResidualNode.comp (tendsto_add_atTop_nat N)
  simpa only [sum_nyquistWeightCellWidth, sub_eq_add_neg] using
    tendsto_atTop_add_const_right atTop (-nyquistResidualNode N) hn

theorem tendsto_nyquist_shifted_ratio (N : ℕ) :
    Tendsto (fun M : ℕ => ((N + M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
  have ht : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ) / ((N + M + 1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    convert (tendsto_natCast_div_add_atTop (N : ℝ)).comp (tendsto_add_atTop_nat 1) using 1
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
    ext M
    ring
  have hi := (tendsto_const_nhds (x := (1 : ℝ))).div ht one_ne_zero
  change Tendsto (fun M : ℕ => 1 / (((M + 1 : ℕ) : ℝ) / ((N + M + 1 : ℕ) : ℝ)))
    atTop (𝓝 ((1 : ℝ) / 1)) at hi
  simpa only [one_div_div, div_one] using hi

theorem tendsto_sum_nyquistPowerIncrement_normalized {r : ℝ} (hr : 0 < r) (N : ℕ) :
    Tendsto (fun M => (∑ k ∈ Finset.range M, nyquistPowerIncrement r (N + k)) /
      ((M + 1 : ℕ) : ℝ) ^ r) atTop (𝓝 1) := by
  have hn : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hp := (tendsto_rpow_atTop hr).comp hn
  have hs := (tendsto_nyquist_shifted_ratio N).rpow_const
    (Or.inl one_ne_zero : (1 : ℝ) ≠ 0 ∨ 0 ≤ r)
  have hq : Tendsto (fun M : ℕ => ((N + M + 1 : ℕ) : ℝ) ^ r /
      ((M + 1 : ℕ) : ℝ) ^ r) atTop (𝓝 1) := by
    simpa only [Real.one_rpow, Real.div_rpow (by positivity : (0 : ℝ) ≤ (N + _ + 1 : ℕ))
      (by positivity : (0 : ℝ) ≤ (_ + 1 : ℕ))] using hs
  simpa only [sum_nyquistPowerIncrement, sub_div, sub_zero, Function.comp_def] using
    hq.sub (hp.const_div_atTop (((N + 1 : ℕ) : ℝ) ^ r))

theorem tendsto_sum_nyquistWeightCellWidth_normalized (N : ℕ) :
    Tendsto (fun M => (∑ k ∈ Finset.range M, nyquistWeightCellWidth (N + k)) /
      nyquistResidualNode M) atTop (𝓝 1) := by
  have hl : Tendsto (fun M : ℕ =>
      Real.log (((N + M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp (tendsto_nyquist_shifted_ratio N)
  have herr : Tendsto (fun M : ℕ =>
      (Real.log (((N + M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ)) - nyquistResidualNode N) /
        nyquistResidualNode M) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (hl.sub tendsto_const_nhds).mul (tendsto_nyquistResidualNode.const_div_atTop 1)
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add herr
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [tendsto_nyquistResidualNode.eventually (eventually_gt_atTop 0)] with M hM
  have he : Real.log (((N + M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ)) =
      nyquistResidualNode (N + M) - nyquistResidualNode M :=
    Real.log_div (by positivity) (by positivity)
  rw [he, sum_nyquistWeightCellWidth]
  field_simp [hM.ne']
  ring

end
end GaloisForLFunctions.BiScaleUncertainty
