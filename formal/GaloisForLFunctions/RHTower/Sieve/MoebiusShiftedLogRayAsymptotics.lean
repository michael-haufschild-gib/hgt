import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicRealCutoffArbitraryLogRate
import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogPowerRealCutoff

/-!
# Shifted logarithmic Möbius kernels on interior rays

On the logarithmic layer `t = v * log X`, the remaining cutoff is
`X * exp (-v * log X) = X^(1-v)`.  For every fixed `v < 1`, it tends to infinity and the affine
shift exactly restores the original logarithmic scale: the linear kernel tends to `1`, while the
quadratic kernel divided by `log X` tends to `2`.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

private theorem tendsto_finset_sum_real {A X : Type*}
    {l : Filter A} (s : Finset X) (f : X → A → ℝ) (g : X → ℝ)
    (h : ∀ x ∈ s, Tendsto (f x) l (nhds (g x))) :
    Tendsto (fun a => ∑ x ∈ s, f x a) l (nhds (∑ x ∈ s, g x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds : Tendsto (fun _ : A => (0 : ℝ)) l (nhds 0))
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      exact (h x (by simp)).add (ih (fun y hy => h y (by simp [hy])))

private theorem weighted_binomial_derivative_sum (p : ℕ) (v : ℝ) :
    (∑ q ∈ Finset.range (p + 1),
      ((p + 1).choose q : ℝ) * ((p + 1 - q : ℕ) : ℝ) *
        v ^ q * (1 - v) ^ (p - q)) = (p + 1 : ℕ) := by
  have hcoeff (q : ℕ) :
      (p + 1 - q) * (p + 1).choose q = (p + 1) * p.choose q := by
    calc
      (p + 1 - q) * (p + 1).choose q =
          (p + 1).choose q * (p + 1 - q) := Nat.mul_comm _ _
      _ = (p + 1).choose (q + 1) * (q + 1) :=
        (Nat.choose_succ_right_eq (p + 1) q).symm
      _ = (p + 1) * p.choose q :=
        (Nat.add_one_mul_choose_eq p q).symm
  calc
    (∑ q ∈ Finset.range (p + 1),
        ((p + 1).choose q : ℝ) * ((p + 1 - q : ℕ) : ℝ) *
          v ^ q * (1 - v) ^ (p - q)) =
      (p + 1 : ℝ) * ∑ q ∈ Finset.range (p + 1),
        (p.choose q : ℝ) * v ^ q * (1 - v) ^ (p - q) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          have hc :
              ((p + 1 - q : ℕ) : ℝ) * ((p + 1).choose q : ℝ) =
                (p + 1 : ℝ) * (p.choose q : ℝ) := by
            exact_mod_cast hcoeff q
          calc
            ((p + 1).choose q : ℝ) * ((p + 1 - q : ℕ) : ℝ) *
                v ^ q * (1 - v) ^ (p - q) =
              (((p + 1 - q : ℕ) : ℝ) * ((p + 1).choose q : ℝ)) *
                v ^ q * (1 - v) ^ (p - q) := by ring
            _ = ((p + 1 : ℝ) * (p.choose q : ℝ)) *
                v ^ q * (1 - v) ^ (p - q) := by rw [hc]
            _ = (p + 1 : ℝ) *
                ((p.choose q : ℝ) * v ^ q * (1 - v) ^ (p - q)) := by ring
    _ = (p + 1 : ℝ) * (v + (1 - v)) ^ p := by
      rw [add_pow]
      apply congrArg ((p + 1 : ℝ) * ·)
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = (p + 1 : ℕ) := by norm_num

/-- Remaining cutoff on the logarithmic ray of relative depth `v`. -/
def moebiusShiftedLogRay (v X : ℝ) : ℝ :=
  X * Real.exp (-v * Real.log X)

theorem moebiusShiftedLogRay_eq_rpow {v X : ℝ} (hX : 0 < X) :
    moebiusShiftedLogRay v X = X ^ (1 - v) := by
  rw [moebiusShiftedLogRay, Real.rpow_def_of_pos hX]
  calc
    X * Real.exp (-v * Real.log X) =
        Real.exp (Real.log X) * Real.exp (-v * Real.log X) := by
          rw [Real.exp_log hX]
    _ = Real.exp (Real.log X + (-v * Real.log X)) := by
      rw [Real.exp_add]
    _ = Real.exp (Real.log X * (1 - v)) := by congr 1; ring

theorem log_moebiusShiftedLogRay {v X : ℝ} (hX : 0 < X) :
    Real.log (moebiusShiftedLogRay v X) =
      (1 - v) * Real.log X := by
  rw [moebiusShiftedLogRay_eq_rpow hX, Real.log_rpow hX]

/-- Every interior logarithmic ray retains a cofinal cutoff. -/
theorem tendsto_moebiusShiftedLogRay_atTop {v : ℝ} (hv : v < 1) :
    Tendsto (moebiusShiftedLogRay v) atTop atTop := by
  have h := tendsto_rpow_atTop (sub_pos.mpr hv)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  exact (moebiusShiftedLogRay_eq_rpow hX).symm

/-- Every positive shifted logarithmic power has its universal leading coefficient on each fixed
interior logarithmic ray. -/
theorem tendsto_moebiusShiftedLogPowerKernelReal_div_log_pow_logRay
    (p : ℕ) {v : ℝ} (hv : v < 1) :
    Tendsto (fun X : ℝ =>
      moebiusShiftedLogPowerKernelReal (p + 1) (v * Real.log X)
          (moebiusShiftedLogRay v X) / Real.log X ^ p)
      atTop (nhds ((p + 1 : ℕ) : ℝ)) := by
  have hY := tendsto_moebiusShiftedLogRay_atTop hv
  have hlogratio : Tendsto
      (fun X : ℝ => Real.log (moebiusShiftedLogRay v X) / Real.log X)
      atTop (nhds (1 - v)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hXpos : 0 < X := by linarith
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    rw [log_moebiusShiftedLogRay hXpos]
    field_simp [hlogX]
  have hlower : Tendsto (fun X : ℝ =>
      ∑ q ∈ Finset.range (p + 1),
        ((p + 1).choose q : ℝ) * (v * Real.log X) ^ q *
          moebiusLogPowerKernelReal (p + 1 - q)
            (moebiusShiftedLogRay v X) / Real.log X ^ p)
      atTop (nhds (∑ q ∈ Finset.range (p + 1),
        ((p + 1).choose q : ℝ) * ((p + 1 - q : ℕ) : ℝ) *
          v ^ q * (1 - v) ^ (p - q))) := by
    apply tendsto_finset_sum_real
    intro q hq
    have hqle : q ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
    let r : ℕ := p - q
    have hdeg : p + 1 - q = r + 1 := by dsimp [r]; omega
    have hpqr : p = q + r := by dsimp [r]; omega
    have hkernel :=
      (tendsto_moebiusLogPowerKernelReal_div_log_pow r).comp hY
    have hscaled := hkernel.mul (hlogratio.pow r)
    have hconst := hscaled.const_mul
      (((p + 1).choose q : ℝ) * v ^ q)
    have htarget :
        (((p + 1).choose q : ℝ) * v ^ q) *
            (((r + 1 : ℕ) : ℝ) * (1 - v) ^ r) =
          ((p + 1).choose q : ℝ) * ((p + 1 - q : ℕ) : ℝ) *
            v ^ q * (1 - v) ^ (p - q) := by
      have hrplus : r + 1 = p + 1 - q := by dsimp [r]; omega
      have hr : r = p - q := rfl
      rw [hrplus, hr]
      ring
    rw [htarget] at hconst
    refine hconst.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hY.eventually (eventually_gt_atTop (1 : ℝ))] with X hX hYX
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    have hlogY : Real.log (moebiusShiftedLogRay v X) ≠ 0 :=
      (Real.log_pos hYX).ne'
    simp only [Function.comp_apply]
    rw [hdeg]
    calc
      (((p + 1).choose q : ℝ) * v ^ q) *
          (moebiusLogPowerKernelReal (r + 1) (moebiusShiftedLogRay v X) /
              Real.log (moebiusShiftedLogRay v X) ^ r *
            (Real.log (moebiusShiftedLogRay v X) / Real.log X) ^ r) =
        (((p + 1).choose q : ℝ) * v ^ q) *
          (moebiusLogPowerKernelReal (r + 1) (moebiusShiftedLogRay v X) /
            Real.log X ^ r) := by
              rw [div_pow]
              field_simp [hlogY]
      _ = ((p + 1).choose q : ℝ) * (v * Real.log X) ^ q *
          moebiusLogPowerKernelReal (r + 1) (moebiusShiftedLogRay v X) /
            Real.log X ^ p := by
              rw [hpqr, pow_add]
              field_simp [hlogX]
              ring
  have hlograte : Tendsto (fun X : ℝ => Real.log X *
      RHTower.deningerHarmonicPartial ⌊moebiusShiftedLogRay v X⌋₊)
      atTop (nhds 0) := by
    have hrate :=
      (tendsto_log_pow_mul_deningerHarmonicPartial_natFloor_zero 1).comp hY
    have hscaled := hrate.const_mul (1 / (1 - v))
    simp only [one_div, mul_zero] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hvne : 1 - v ≠ 0 := by linarith
    simp only [Function.comp_apply, pow_one]
    rw [log_moebiusShiftedLogRay hX]
    field_simp [hvne]
  have hendpointCore := hlograte.const_mul (v ^ (p + 1))
  simp only [mul_zero] at hendpointCore
  have hendpoint : Tendsto (fun X : ℝ =>
      ((p + 1).choose (p + 1) : ℝ) * (v * Real.log X) ^ (p + 1) *
          moebiusLogPowerKernelReal (p + 1 - (p + 1))
            (moebiusShiftedLogRay v X) / Real.log X ^ p)
      atTop (nhds 0) := by
    refine hendpointCore.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    rw [show p + 1 - (p + 1) = 0 by omega]
    simp only [Nat.choose_self, Nat.cast_one, one_mul]
    rw [moebiusLogPowerKernelReal_zero]
    rw [pow_succ, mul_div_assoc]
    field_simp [hlogX]
    ring
  have hsum := hlower.add hendpoint
  rw [add_zero, weighted_binomial_derivative_sum p v] at hsum
  refine hsum.congr' ?_
  filter_upwards with X
  symm
  conv_lhs =>
    rw [moebiusShiftedLogPowerKernelReal_eq_sum]
    rw [Finset.sum_range_succ]
    rw [add_div]
    rw [Finset.sum_div]

/-- The shifted linear kernel has limit one on every fixed interior logarithmic ray. -/
theorem tendsto_moebiusShiftedLogKernelReal_logRay_one
    {v : ℝ} (hv : v < 1) :
    Tendsto (fun X : ℝ =>
      moebiusShiftedLogKernelReal (v * Real.log X)
        (moebiusShiftedLogRay v X)) atTop (nhds 1) := by
  have hY := tendsto_moebiusShiftedLogRay_atTop hv
  have hmain := tendsto_coprimeLogMoebius_one.comp hY
  have hrate :=
    (tendsto_log_pow_mul_deningerHarmonicPartial_natFloor_zero 1).comp hY
  have hlograte : Tendsto (fun X : ℝ => Real.log X *
      RHTower.deningerHarmonicPartial ⌊moebiusShiftedLogRay v X⌋₊)
      atTop (nhds 0) := by
    have hscaled := hrate.const_mul (1 / (1 - v))
    simp only [one_div, mul_zero] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hvne : 1 - v ≠ 0 := by linarith
    simp only [Function.comp_apply, pow_one]
    rw [log_moebiusShiftedLogRay hX]
    field_simp [hvne]
  have herror := hlograte.const_mul v
  simp only [mul_zero] at herror
  have hsum := hmain.add herror
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with X
  rw [moebiusShiftedLogKernelReal_eq]
  simp only [Function.comp_apply]
  ring

/-- The shifted quadratic kernel has leading coefficient two on every fixed interior
logarithmic ray. -/
theorem tendsto_moebiusShiftedLogSqKernelReal_div_log_logRay_two
    {v : ℝ} (hv : v < 1) :
    Tendsto (fun X : ℝ =>
      moebiusShiftedLogSqKernelReal (v * Real.log X)
          (moebiusShiftedLogRay v X) / Real.log X)
      atTop (nhds 2) := by
  have hY := tendsto_moebiusShiftedLogRay_atTop hv
  have hlogratio : Tendsto
      (fun X : ℝ => Real.log (moebiusShiftedLogRay v X) / Real.log X)
      atTop (nhds (1 - v)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hXpos : 0 < X := by linarith
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    rw [log_moebiusShiftedLogRay hXpos]
    field_simp [hlogX]
  have hmainRatio := tendsto_moebiusDoubleLogKernelReal_div_log_two.comp hY
  have hmain : Tendsto (fun X : ℝ =>
      moebiusDoubleLogKernelReal (moebiusShiftedLogRay v X) / Real.log X)
      atTop (nhds (2 * (1 - v))) := by
    have hmul := hmainRatio.mul hlogratio
    refine hmul.congr' ?_
    filter_upwards [hY.eventually (eventually_gt_atTop (1 : ℝ)),
      eventually_gt_atTop (1 : ℝ)] with X hRay hX
    have hlogRay : Real.log (moebiusShiftedLogRay v X) ≠ 0 :=
      (Real.log_pos hRay).ne'
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    simp only [Function.comp_apply]
    field_simp [hlogRay, hlogX]
  have hlinear := tendsto_coprimeLogMoebius_one.comp hY
  have hmiddle : Tendsto (fun X : ℝ =>
      2 * (v * Real.log X) *
          coprimeLogMoebius 1 (moebiusShiftedLogRay v X) / Real.log X)
      atTop (nhds (2 * v)) := by
    have hscaled := hlinear.const_mul (2 * v)
    simp only [mul_one] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    simp only [Function.comp_apply]
    field_simp [hlogX]
  have hrate :=
    (tendsto_log_pow_mul_deningerHarmonicPartial_natFloor_zero 1).comp hY
  have hlograte : Tendsto (fun X : ℝ => Real.log X *
      RHTower.deningerHarmonicPartial ⌊moebiusShiftedLogRay v X⌋₊)
      atTop (nhds 0) := by
    have hscaled := hrate.const_mul (1 / (1 - v))
    simp only [one_div, mul_zero] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hvne : 1 - v ≠ 0 := by linarith
    simp only [Function.comp_apply, pow_one]
    rw [log_moebiusShiftedLogRay hX]
    field_simp [hvne]
  have herror : Tendsto (fun X : ℝ =>
      (v * Real.log X) ^ 2 *
          RHTower.deningerHarmonicPartial ⌊moebiusShiftedLogRay v X⌋₊ /
        Real.log X) atTop (nhds 0) := by
    have hscaled := hlograte.const_mul (v ^ 2)
    simp only [mul_zero] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    field_simp [hlogX]
  have hsum := (hmain.add hmiddle).add herror
  have hlim : 2 * (1 - v) + 2 * v + 0 = (2 : ℝ) := by ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  rw [moebiusShiftedLogSqKernelReal_eq]
  field_simp [hlogX]

end

end RHTower.Sieve
