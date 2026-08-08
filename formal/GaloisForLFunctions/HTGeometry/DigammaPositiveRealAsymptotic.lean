import GaloisForLFunctions.HTGeometry.DigammaAsymptotic
import GaloisForLFunctions.RHTower.TrigammaVertical

/-!
# Continuous positive-real digamma asymptotic

The corpus already contains the exact integer asymptotic for `digamma` and strict monotonicity of
its real part on the positive ray.  Floor interpolation upgrades these two facts to the continuous
positive-real asymptotic.  This is the missing order-zero input for completed-Xi far-right moment
limits.
-/

open Complex Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem tendsto_re_digamma_natCast_add_one_sub_log :
    Tendsto
      (fun N : ℕ =>
        (Complex.digamma ((N : ℂ) + 1)).re - Real.log ((N : ℝ) + 1))
      atTop (nhds 0) := by
  have h : Tendsto
      (fun N : ℕ =>
        (Complex.digamma ((N : ℂ) + 1) - Complex.log ((N : ℂ) + 1)).re)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp
      RHTower.digamma_natCast_add_one_sub_log_tendsto
  apply h.congr'
  filter_upwards with N
  rw [Complex.sub_re]
  congr 1
  rw [Complex.log_re]
  have hnorm : ‖(N : ℂ) + 1‖ = (N : ℝ) + 1 := by
    calc
      ‖(N : ℂ) + 1‖ = ‖(((N : ℝ) + 1 : ℝ) : ℂ)‖ := by push_cast; ring
      _ = ‖(N : ℝ) + 1‖ := Complex.norm_real _
      _ = (N : ℝ) + 1 := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]

private theorem tendsto_floor_add_div_add_one (c : ℝ) :
    Tendsto
      (fun x : ℝ => (((⌊x⌋₊ : ℕ) : ℝ) + c) / (x + 1))
      atTop (nhds 1) := by
  have hfloor : Tendsto (fun x : ℝ => ((⌊x⌋₊ : ℕ) : ℝ) / x) atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto
      (fun x : ℝ => ((⌊x⌋₊ : ℕ) : ℝ) / x + c * x⁻¹)
      atTop (nhds 1) := by
    simpa using hfloor.add (hinv.const_mul c)
  have hden : Tendsto (fun x : ℝ => 1 + x⁻¹) atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).add hinv
  have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  rw [div_one] at hquot
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  change (((((⌊x⌋₊ : ℕ) : ℝ) / x) + c * x⁻¹) / (1 + x⁻¹)) =
    ((((⌊x⌋₊ : ℕ) : ℝ) + c) / (x + 1))
  field_simp [hx.ne']

private theorem tendsto_log_floor_add_sub_log_add_one (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun x : ℝ =>
        Real.log (((⌊x⌋₊ : ℕ) : ℝ) + c) - Real.log (x + 1))
      atTop (nhds 0) := by
  have hratio := tendsto_floor_add_div_add_one c
  have hlog : Tendsto
      (fun x : ℝ => Real.log ((((⌊x⌋₊ : ℕ) : ℝ) + c) / (x + 1)))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  apply hlog.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_div (by positivity) (by positivity)]

/-- The real part of `digamma (x + 1)` differs from `log (x + 1)` by a vanishing quantity on the
continuous positive ray. -/
theorem tendsto_re_digamma_add_one_sub_log :
    Tendsto
      (fun x : ℝ =>
        (Complex.digamma ((x : ℂ) + 1)).re - Real.log (x + 1))
      atTop (nhds 0) := by
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hfloorSucc : Tendsto (fun x : ℝ => ⌊x⌋₊ + 1) atTop atTop := by
    refine tendsto_atTop.2 fun N => ?_
    filter_upwards [hfloor.eventually_ge_atTop N] with x hx
    omega
  have hbaseLow : Tendsto
      (fun x : ℝ =>
        (Complex.digamma (((⌊x⌋₊ : ℕ) : ℂ) + 1)).re -
          Real.log (((⌊x⌋₊ : ℕ) : ℝ) + 1))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      tendsto_re_digamma_natCast_add_one_sub_log.comp hfloor
  have hbaseHigh : Tendsto
      (fun x : ℝ =>
        (Complex.digamma (((⌊x⌋₊ + 1 : ℕ) : ℂ) + 1)).re -
          Real.log (((⌊x⌋₊ + 1 : ℕ) : ℝ) + 1))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      tendsto_re_digamma_natCast_add_one_sub_log.comp hfloorSucc
  have hlogLow := tendsto_log_floor_add_sub_log_add_one 1 (by norm_num)
  have hlogHigh := tendsto_log_floor_add_sub_log_add_one 2 (by norm_num)
  have hlow : Tendsto
      (fun x : ℝ =>
        (Complex.digamma ((((⌊x⌋₊ : ℕ) : ℝ) + 1 : ℝ) : ℂ)).re -
          Real.log (x + 1))
      atTop (nhds 0) := by
    convert hbaseLow.add hlogLow using 1
    · funext x
      push_cast
      ring_nf
    · ring
  have hhigh : Tendsto
      (fun x : ℝ =>
        (Complex.digamma ((((⌊x⌋₊ : ℕ) : ℝ) + 2 : ℝ) : ℂ)).re -
          Real.log (x + 1))
      atTop (nhds 0) := by
    convert hbaseHigh.add hlogHigh using 1
    · funext x
      push_cast
      ring_nf
    · ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hfloorLe : (((⌊x⌋₊ : ℕ) : ℝ) ≤ x) := Nat.floor_le hx.le
    have hmono := RHTower.strictMonoOn_re_digamma_ofReal.monotoneOn
      (show 0 < ((⌊x⌋₊ : ℕ) : ℝ) + 1 by positivity)
      (show 0 < x + 1 by linarith)
      (by linarith)
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using
      sub_le_sub_right hmono (Real.log (x + 1))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hfloorLt : x < (((⌊x⌋₊ : ℕ) : ℝ) + 1) := Nat.lt_floor_add_one x
    have hmono := RHTower.strictMonoOn_re_digamma_ofReal.monotoneOn
      (show 0 < x + 1 by linarith)
      (show 0 < ((⌊x⌋₊ : ℕ) : ℝ) + 2 by positivity)
      (by linarith)
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using
      sub_le_sub_right hmono (Real.log (x + 1))

/-- Continuous positive-real form of the digamma logarithmic asymptotic. -/
theorem tendsto_re_digamma_ofReal_sub_log :
    Tendsto
      (fun x : ℝ => (Complex.digamma (x : ℂ)).re - Real.log x)
      atTop (nhds 0) := by
  have hshift : Tendsto (fun x : ℝ => x - 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1) tendsto_id
  apply (tendsto_re_digamma_add_one_sub_log.comp hshift).congr'
  filter_upwards with x
  simp

end

end GaloisForLFunctions.HTGeometry
