import GaloisForLFunctions.RHTower.MobiusSparseForbiddenDeletion

/-!
# The coprime square-root card's explicit iterated-logarithm schedule

For every fixed `η > 0`, this module formalizes the card's concrete choice

`h(x) = (log log (3x))^(1+η)`.

It proves all elementary admissibility conditions used there: `h / log log (3x) → ∞`,
`h → ∞`, `h / x → 0`, and eventually `10 ≤ h ≤ x`.  These statements are unconditional
real-asymptotic facts and introduce no Möbius or short-interval estimate.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- The explicit slowly growing schedule advertised on the coprime square-root card. -/
def coprimeSquareRootLogLogSchedule (η x : ℝ) : ℝ :=
  (Real.log (Real.log (3 * x))) ^ (1 + η)

/-- The corresponding square-root interval length from equation `(4)`. -/
def coprimeSquareRootLogLogWindow (η x : ℝ) : ℝ :=
  Real.sqrt x * coprimeSquareRootLogLogSchedule η x

private theorem tendsto_three_mul_atTop :
    Tendsto (fun x : ℝ => 3 * x) atTop atTop := by
  simpa only [id_eq] using
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3))

private theorem tendsto_logLog_three_mul_atTop :
    Tendsto (fun x : ℝ => Real.log (Real.log (3 * x))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_three_mul_atTop)

/-- The schedule grows faster than the iterated logarithm itself. -/
theorem tendsto_coprimeSquareRootLogLogSchedule_div_logLog {η : ℝ} (hη : 0 < η) :
    Tendsto (fun x : ℝ =>
      coprimeSquareRootLogLogSchedule η x / Real.log (Real.log (3 * x)))
      atTop atTop := by
  have hlim : Tendsto (fun x : ℝ => (Real.log (Real.log (3 * x))) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_logLog_three_mul_atTop
  refine hlim.congr' ?_
  filter_upwards [tendsto_logLog_three_mul_atTop.eventually_ge_atTop 1] with x hx
  have hpos : 0 < Real.log (Real.log (3 * x)) := lt_of_lt_of_le (by norm_num) hx
  rw [coprimeSquareRootLogLogSchedule, Real.rpow_add hpos, Real.rpow_one]
  field_simp

/-- The schedule itself tends to infinity. -/
theorem tendsto_coprimeSquareRootLogLogSchedule_atTop {η : ℝ} (hη : 0 < η) :
    Tendsto (coprimeSquareRootLogLogSchedule η) atTop atTop := by
  have hexp : 0 < 1 + η := by linarith
  exact (tendsto_rpow_atTop hexp).comp tendsto_logLog_three_mul_atTop

/-- The schedule is sublinear. -/
theorem tendsto_coprimeSquareRootLogLogSchedule_div_self {η : ℝ} :
    Tendsto (fun x : ℝ => coprimeSquareRootLogLogSchedule η x / x) atTop (𝓝 0) := by
  have hy := tendsto_three_mul_atTop
  have hfirst : Tendsto (fun x : ℝ =>
      coprimeSquareRootLogLogSchedule η x / Real.log (3 * x)) atTop (𝓝 0) := by
    have hraw := (RHTower.tendsto_logLog_rpow_div_log_rpow (1 + η)
      (s := (1 : ℝ)) (by norm_num)).comp hy
    simpa only [coprimeSquareRootLogLogSchedule, Function.comp_def, Real.rpow_one] using hraw
  have hraw : Tendsto (fun x : ℝ => Real.log (3 * x) / (3 * x)) atTop (𝓝 0) := by
    have hraw' := (RHTower.tendsto_log_rpow_div_rpow (1 : ℝ)
      (s := (1 : ℝ)) (by norm_num)).comp hy
    simpa only [Function.comp_def, Real.rpow_one] using hraw'
  have hsecond : Tendsto (fun x : ℝ => Real.log (3 * x) / x) atTop (𝓝 0) := by
    have hscaled := hraw.const_mul (3 : ℝ)
    simp only [mul_zero] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hproduct := hfirst.mul hsecond
  simp only [mul_zero] at hproduct
  refine hproduct.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlogpos : 0 < Real.log (3 * x) := by
    apply Real.log_pos
    nlinarith
  field_simp

/-- Eventually the explicit schedule lies in the card's admissible range `10 ≤ h ≤ x`. -/
theorem eventually_coprimeSquareRootLogLogSchedule_admissible {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, 10 ≤ coprimeSquareRootLogLogSchedule η x ∧
      coprimeSquareRootLogLogSchedule η x ≤ x := by
  have hlower := (tendsto_coprimeSquareRootLogLogSchedule_atTop hη).eventually_ge_atTop 10
  have hratio := (tendsto_coprimeSquareRootLogLogSchedule_div_self (η := η)).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hlower, hratio, eventually_gt_atTop (0 : ℝ)] with x hlower hratio hx
  refine ⟨hlower, ?_⟩
  exact le_of_lt ((div_lt_one hx).mp hratio)

private theorem tendsto_logLog_three_mul_div_log :
    Tendsto (fun x : ℝ => Real.log (Real.log (3 * x)) / Real.log x) atTop (𝓝 0) := by
  have hraw := (RHTower.tendsto_logLog_rpow_div_log_rpow (1 : ℝ)
    (s := (1 : ℝ)) (by norm_num)).comp tendsto_three_mul_atTop
  have hfirst : Tendsto (fun x : ℝ =>
      Real.log (Real.log (3 * x)) / Real.log (3 * x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using hraw
  have hratio : Tendsto (fun x : ℝ => Real.log (3 * x) / Real.log x) atTop (𝓝 1) := by
    have hzero := Filter.Tendsto.const_div_atTop Real.tendsto_log_atTop (Real.log 3)
    have hlim := hzero.add (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)))
    simp only [zero_add] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hx0)]
    field_simp
  have hproduct := hfirst.mul hratio
  simp only [mul_one] at hproduct
  refine hproduct.congr' ?_
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hx1 : 1 < x := lt_trans he hx
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have hlog3x : Real.log (3 * x) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    nlinarith
  field_simp

private theorem tendsto_log_logLog_three_mul_div_log :
    Tendsto (fun x : ℝ => Real.log (Real.log (Real.log (3 * x))) / Real.log x)
      atTop (𝓝 0) := by
  have hraw := (RHTower.tendsto_log_rpow_div_rpow (1 : ℝ)
    (s := (1 : ℝ)) (by norm_num)).comp tendsto_logLog_three_mul_atTop
  have hfirst : Tendsto (fun x : ℝ =>
      Real.log (Real.log (Real.log (3 * x))) / Real.log (Real.log (3 * x)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using hraw
  have hproduct := hfirst.mul tendsto_logLog_three_mul_div_log
  simp only [mul_zero] at hproduct
  refine hproduct.congr' ?_
  filter_upwards [tendsto_logLog_three_mul_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hB hx
  have hBne : Real.log (Real.log (3 * x)) ≠ 0 := by linarith
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  field_simp

/-- Every fixed schedule exponent is subpower on the logarithmic scale. -/
theorem tendsto_log_coprimeSquareRootLogLogSchedule_div_log {η : ℝ} :
    Tendsto (fun x : ℝ =>
      Real.log (coprimeSquareRootLogLogSchedule η x) / Real.log x)
      atTop (𝓝 0) := by
  have hlim := tendsto_log_logLog_three_mul_div_log.const_mul (1 + η)
  simp only [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [tendsto_logLog_three_mul_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hB hx
  have hBpos : 0 < Real.log (Real.log (3 * x)) := by linarith
  rw [coprimeSquareRootLogLogSchedule, Real.log_rpow hBpos]
  ring

/-- The advertised interval has logarithmic exponent `1/2`, i.e. `X^(1/2+o(1))`. -/
theorem tendsto_log_coprimeSquareRootLogLogWindow_div_log_half {η : ℝ} :
    Tendsto (fun x : ℝ => Real.log (coprimeSquareRootLogLogWindow η x) / Real.log x)
      atTop (𝓝 ((1 : ℝ) / 2)) := by
  have hlim := (tendsto_const_nhds (x := ((1 : ℝ) / 2)) (f := (atTop : Filter ℝ))).add
    (tendsto_log_coprimeSquareRootLogLogSchedule_div_log (η := η))
  simp only [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [tendsto_logLog_three_mul_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hB hx
  have hx0 : 0 < x := by linarith
  have hsqrt : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx0)
  have hschedule : coprimeSquareRootLogLogSchedule η x ≠ 0 := by
    rw [coprimeSquareRootLogLogSchedule]
    exact ne_of_gt (Real.rpow_pos_of_pos (by linarith) (1 + η))
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [coprimeSquareRootLogLogWindow, Real.log_mul hsqrt hschedule, Real.log_sqrt hx0.le]
  field_simp

end

end RHTower.Sieve
