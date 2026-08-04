import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorLimit

/-!
# The main term's two factors

The main term is `W(1)` times the bracket.  Both have limits:

* the bracket is `4·arctan(T/w)` with `T/w = t⁹·exp(t)/A → ∞`, so it tends to `2π`;
* the mass `W(1)` lies between `N` and `N + H` with `H/N = exp(-(log N)^{1/20}) → 0`, so `W(1)/N`
  tends to `1`.

Together the main term is `2π·N·(1 + o(1))`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-- The cutoff's transform at `1` is the real mass. -/
theorem mellin_smoothWeight_one_eq_ofReal {N H : ℝ} :
    mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
      = ((∫ x in Ioi (0 : ℝ), smoothWeight N H x : ℝ) : ℂ) := by
  rw [mellin_smoothWeight_one]
  exact integral_ofReal (𝕜 := ℂ)

/-- The relative smoothing width vanishes. -/
theorem tendsto_chebWidth_div : Tendsto (fun x : ℝ => chebWidth x / x) atTop (𝓝 0) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (-((Real.log x) ^ ((1 : ℝ) / 20)))) atTop (𝓝 0) := by
    have hroot : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 20)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hroot)
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [chebWidth, Real.exp_neg]
  field_simp

/-- **The cutoff's mass is asymptotically the cutoff.** -/
theorem tendsto_mass_div :
    Tendsto (fun x : ℝ => (∫ y in Ioi (0 : ℝ), smoothWeight x (chebWidth x) y) / x)
      atTop (𝓝 1) := by
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hupper : Tendsto (fun x : ℝ => 1 + chebWidth x / x) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ)) |>.add tendsto_chebWidth_div
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hone hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [le_div_iff₀ hx, one_mul]
    exact le_integral_smoothWeight hx.le (chebWidth_pos hx)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_le_iff₀ hx]
    have h := integral_smoothWeight_le (N := x) (H := chebWidth x) hx.le (chebWidth_pos hx)
    have hrw : (1 + chebWidth x / x) * x = x + chebWidth x := by field_simp
    rw [hrw]
    exact h

/-- The ratio of height to strip width grows without bound. -/
theorem tendsto_height_div_width :
    Tendsto (fun x : ℝ => chebHeight x / (zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))
      atTop atTop := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  refine tendsto_atTop_mono' atTop ?_ tendsto_chebHeight
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx
  have hpow9 : (1 : ℝ) ≤ (Real.log x) ^ ((9 : ℝ) / 10) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx (by norm_num : (0 : ℝ) ≤ 9 / 10)
    rwa [Real.one_rpow] at h
  have hw0 : (0 : ℝ) < zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10) := by positivity
  have hwle : zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hT0 : (0 : ℝ) < chebHeight x := Real.exp_pos _
  rw [le_div_iff₀ hw0]
  nlinarith [hT0, hwle]

/-- **The bracket tends to `2π`.** -/
theorem tendsto_bracket_at_choice :
    Tendsto (fun x : ℝ =>
        2 * Real.arctan (chebHeight x / (zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))
          - 2 * Real.arctan (chebHeight x
              / (-(zetaLowerA / (Real.log x) ^ ((9 : ℝ) / 10)))))
      atTop (𝓝 (2 * Real.pi)) := by
  have harc : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have hcomp := harc.comp tendsto_height_div_width
  have hsum := (hcomp.const_mul (4 : ℝ))
  have hlim : (4 : ℝ) * (Real.pi / 2) = 2 * Real.pi := by ring
  rw [hlim] at hsum
  refine hsum.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [div_neg, Real.arctan_neg]
  ring

end RHTower.Sieve
