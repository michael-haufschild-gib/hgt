/-
# The `k`-th root of a Gamma value along a linear ray

Binet's formula writes `log Γ(a)` as the Stirling main term plus a kernel bounded by `1/(8a)`.
Dividing by `x` along `a = cx + b` kills every term except the leading pair, so

`Γ(cx+b)^{1/x} / x^c → (c/e)^c`.

This is the exact root asymptotic that a shift lattice of degree `d` needs: its Gamma factors
advance by `λ/d` per step, so their roots contribute `(λ/(de))^{λ/d}` rather than the degree-one
value `1/e`.

Main results:
* `integral_Ioi_inv_sq_shift`, `abs_binetKernel_le` — the Binet kernel is at most `1/(8a)`.
* `abs_log_Gamma_sub_stirling_le` — Stirling with an explicit remainder.
* `tendsto_log_Gamma_linear_div` — `log Γ(cx+b)/x − c log x → c log c − c`.
* `tendsto_Gamma_linear_rpow_inv` — **`Γ(cx+b)^{1/x}/x^c → (c/e)^c`**.
* `tendsto_Gamma_linear_rpow_inv_nat` — the same along the natural numbers.
* `tendsto_factorial_rpow_inv_div` — `(k!)^{1/k}/k → 1/e`.
-/
import GaloisForLFunctions.HTGeometry.BinetLogGamma

open Filter Topology Real MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The Binet kernel is at most `1/(8a)` -/

theorem integrableOn_invSqShift {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1 / (x + a) ^ 2) (Ioi (0 : ℝ)) := by
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (g := fun x : ℝ => -(1 / (x + a)))
    (l := 0) ?_ ?_ ?_ ?_
  · have : ContinuousAt (fun x : ℝ => -(1 / (x + a))) 0 := by
      refine ContinuousAt.neg (ContinuousAt.div continuousAt_const (by fun_prop) ?_)
      simpa using ne_of_gt ha
    exact this.continuousWithinAt
  · intro x hx
    have hxa : (0 : ℝ) < x + a := by
      have : (0 : ℝ) < x := hx
      linarith
    exact ((hasDerivAt_invShift hxa).neg).congr_deriv (by ring)
  · intro x hx
    have hxa : (0 : ℝ) < x + a := by
      have : (0 : ℝ) < x := hx
      linarith
    positivity
  · have hlim : Tendsto (fun x : ℝ => x + a) atTop atTop :=
      tendsto_atTop_add_const_right _ a tendsto_id
    have hinv0 : Tendsto (fun x : ℝ => (x + a)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hlim
    have hneg : Tendsto (fun x : ℝ => -((x + a)⁻¹)) atTop (𝓝 (-0)) := hinv0.neg
    rw [neg_zero] at hneg
    exact hneg.congr fun x => by rw [one_div]

/-- The total mass of the Binet weight: `∫_0^∞ (x+a)^{-2} dx = 1/a`. -/
theorem integral_Ioi_inv_sq_shift {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), 1 / (x + a) ^ 2 = 1 / a := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => -(1 / (y + a))) (1 / (x + a) ^ 2) x := by
    intro x hx
    have hxa : (0 : ℝ) < x + a := by
      have : (0 : ℝ) < x := hx
      linarith
    exact ((hasDerivAt_invShift hxa).neg).congr_deriv (by ring)
  have hcont : ContinuousWithinAt (fun y : ℝ => -(1 / (y + a))) (Ici (0 : ℝ)) 0 := by
    have : ContinuousAt (fun x : ℝ => -(1 / (x + a))) 0 := by
      refine ContinuousAt.neg (ContinuousAt.div continuousAt_const (by fun_prop) ?_)
      simpa using ne_of_gt ha
    exact this.continuousWithinAt
  have hlim : Tendsto (fun x : ℝ => -(1 / (x + a))) atTop (𝓝 0) := by
    have hlim' : Tendsto (fun x : ℝ => x + a) atTop atTop :=
      tendsto_atTop_add_const_right _ a tendsto_id
    have hinv0 : Tendsto (fun x : ℝ => (x + a)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hlim'
    have hneg : Tendsto (fun x : ℝ => -((x + a)⁻¹)) atTop (𝓝 (-0)) := hinv0.neg
    rw [neg_zero] at hneg
    exact hneg.congr fun x => by rw [one_div]
  have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_invSqShift ha) hlim
  rw [this]
  simp

/-- **The Binet kernel is at most `1/(8a)`.**  The periodic Bernoulli half is bounded by `1/8`
and the weight `(x+a)^{-2}` has total mass `1/a` on the half line. -/
theorem abs_binetKernel_le {a : ℝ} (ha : 0 < a) : |binetKernel a| ≤ 1 / (8 * a) := by
  have hdom : IntegrableOn (fun x : ℝ => (1 / 8 : ℝ) * (1 / (x + a) ^ 2)) (Ioi (0 : ℝ)) :=
    (integrableOn_invSqShift ha).const_mul _
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖bernoulliHalfPer x / (x + a) ^ 2‖ ≤ (1 / 8 : ℝ) * (1 / (x + a) ^ 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hxa : (0 : ℝ) < x + a := by linarith
    have hker := abs_bernoulliHalfPer_le x
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x + a) ^ 2),
      div_le_iff₀ (by positivity)]
    have hsimp : (1 / 8 : ℝ) * (1 / (x + a) ^ 2) * (x + a) ^ 2 = 1 / 8 := by field_simp
    rw [hsimp]
    exact hker
  have hmain := MeasureTheory.norm_integral_le_of_norm_le hdom hbound
  have hval : ∫ x in Ioi (0 : ℝ), (1 / 8 : ℝ) * (1 / (x + a) ^ 2) = 1 / (8 * a) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_inv_sq_shift ha]
    field_simp
  rw [hval] at hmain
  simpa [binetKernel, Real.norm_eq_abs] using hmain

/-- **Stirling's formula with an explicit remainder.** -/
theorem abs_log_Gamma_sub_stirling_le {a : ℝ} (ha : 0 < a) :
    |Real.log (Real.Gamma a) - ((a - 1 / 2) * Real.log a - a + Real.log (2 * π) / 2)|
      ≤ 1 / (8 * a) := by
  have hb := log_Gamma_eq_binet ha
  have heq : Real.log (Real.Gamma a) - ((a - 1 / 2) * Real.log a - a + Real.log (2 * π) / 2)
      = -binetKernel a := by rw [hb]; ring
  rw [heq, abs_neg]
  exact abs_binetKernel_le ha

/-! ## The root asymptotic along a linear ray -/

variable {c b : ℝ}

theorem tendsto_log_div_atTop : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

theorem tendsto_log_linear_div (hc : 0 < c) (b : ℝ) :
    Tendsto (fun x : ℝ => Real.log (c * x + b) / x) atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => c * x + b) atTop atTop := by
    exact Filter.tendsto_atTop_add_const_right _ b ((tendsto_id.const_mul_atTop hc))
  have h1 : Tendsto (fun x : ℝ => Real.log (c * x + b) / (c * x + b)) atTop (𝓝 0) :=
    tendsto_log_div_atTop.comp hshift
  have h2 : Tendsto (fun x : ℝ => (c * x + b) / x) atTop (𝓝 c) := by
    have hbx : Tendsto (fun x : ℝ => b / x) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_id b
    have := (tendsto_const_nhds (x := c) (α := ℝ) (f := atTop)).add hbx
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hmul := h1.mul h2
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-b / c)] with x hx hxb
  have hcx : (0 : ℝ) < c * x + b := by
    have : -b / c < x := hxb
    have := (div_lt_iff₀ hc).mp this
    linarith
  field_simp

/-- **Stirling, divided by `x` along the ray `a = cx + b`.** -/
theorem tendsto_log_Gamma_linear_div (hc : 0 < c) (b : ℝ) :
    Tendsto (fun x : ℝ => Real.log (Real.Gamma (c * x + b)) / x - c * Real.log x) atTop
      (𝓝 (c * Real.log c - c)) := by
  set E : ℝ → ℝ := fun x =>
    Real.log (Real.Gamma (c * x + b))
      - ((c * x + b - 1 / 2) * Real.log (c * x + b) - (c * x + b) + Real.log (2 * π) / 2) with hE
  set M : ℝ → ℝ := fun x =>
    c * Real.log ((c * x + b) / x) + (b - 1 / 2) * (Real.log (c * x + b) / x)
      - c - b / x + Real.log (2 * π) / (2 * x) with hM
  -- the error term, divided by `x`, vanishes
  have hEzero : Tendsto (fun x : ℝ => E x / x) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.const_div_atTop tendsto_id (1 / 8 : ℝ))
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ((1 - b) / c)] with x hx hxb
    have hcx : (1 : ℝ) ≤ c * x + b := by
      have := (div_le_iff₀ hc).mp hxb
      linarith
    have hcx0 : (0 : ℝ) < c * x + b := by linarith
    have hbound := abs_log_Gamma_sub_stirling_le hcx0
    have hEval : |E x| ≤ 1 / (8 * (c * x + b)) := hbound
    have hle : 1 / (8 * (c * x + b)) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    simp only [id_eq]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx, div_le_div_iff₀ hx hx]
    nlinarith [hEval, hle, abs_nonneg (E x)]
  -- the main term converges
  have hMlim : Tendsto M atTop (𝓝 (c * Real.log c - c)) := by
    have h1 : Tendsto (fun x : ℝ => (c * x + b) / x) atTop (𝓝 c) := by
      have hbx : Tendsto (fun x : ℝ => b / x) atTop (𝓝 0) :=
        Filter.Tendsto.const_div_atTop tendsto_id b
      have := (tendsto_const_nhds (x := c) (α := ℝ) (f := atTop)).add hbx
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp
    have h2 : Tendsto (fun x : ℝ => Real.log ((c * x + b) / x)) atTop (𝓝 (Real.log c)) :=
      (Real.continuousAt_log hc.ne').tendsto.comp h1
    have h3 : Tendsto (fun x : ℝ => Real.log (c * x + b) / x) atTop (𝓝 0) :=
      tendsto_log_linear_div hc b
    have h4 : Tendsto (fun x : ℝ => b / x) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_id b
    have h5 : Tendsto (fun x : ℝ => Real.log (2 * π) / (2 * x)) atTop (𝓝 0) := by
      have hx2 : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
        tendsto_id.const_mul_atTop (by norm_num)
      exact Filter.Tendsto.const_div_atTop hx2 _
    have hA : Tendsto (fun x : ℝ => c * Real.log ((c * x + b) / x)) atTop
        (𝓝 (c * Real.log c)) := tendsto_const_nhds.mul h2
    have hB : Tendsto (fun x : ℝ => (b - 1 / 2) * (Real.log (c * x + b) / x)) atTop
        (𝓝 ((b - 1 / 2) * 0)) := tendsto_const_nhds.mul h3
    have hlim := (((hA.add hB).sub
      (tendsto_const_nhds (x := c) (α := ℝ) (f := atTop))).sub h4).add h5
    have heq : c * Real.log c + (b - 1 / 2) * 0 - c - 0 + 0 = c * Real.log c - c := by ring
    rw [heq] at hlim
    exact hlim
  -- the two pieces reassemble
  have hsum := hEzero.add hMlim
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-b / c)] with x hx hxb
  have hcx : (0 : ℝ) < c * x + b := by
    have := (div_lt_iff₀ hc).mp hxb
    linarith
  have hlogdiv : Real.log ((c * x + b) / x) = Real.log (c * x + b) - Real.log x :=
    Real.log_div hcx.ne' hx.ne'
  simp only [hE, hM, hlogdiv]
  field_simp
  ring

/-- `exp (c log c − c) = (c/e)^c`. -/
theorem exp_stirling_eq_rpow (hc : 0 < c) :
    Real.exp (c * Real.log c - c) = (c / Real.exp 1) ^ c := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_div hc.ne' (Real.exp_ne_zero 1),
    Real.log_exp]
  ring_nf

/-- **The root asymptotic of a Gamma value along a linear ray**:
`Γ(cx+b)^{1/x} / x^c → (c/e)^c`. -/
theorem tendsto_Gamma_linear_rpow_inv (hc : 0 < c) (b : ℝ) :
    Tendsto (fun x : ℝ => Real.Gamma (c * x + b) ^ (1 / x) / x ^ c) atTop
      (𝓝 ((c / Real.exp 1) ^ c)) := by
  have hlim := (Real.continuous_exp.tendsto _).comp (tendsto_log_Gamma_linear_div hc b)
  rw [exp_stirling_eq_rpow hc] at *
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-b / c)] with x hx hxb
  have hcx : (0 : ℝ) < c * x + b := by
    have := (div_lt_iff₀ hc).mp hxb
    linarith
  have hG : 0 < Real.Gamma (c * x + b) := Real.Gamma_pos_of_pos hcx
  show Real.exp (Real.log (Real.Gamma (c * x + b)) / x - c * Real.log x)
      = Real.Gamma (c * x + b) ^ (1 / x) / x ^ c
  rw [Real.rpow_def_of_pos hG, Real.rpow_def_of_pos hx, ← Real.exp_sub]
  congr 1
  field_simp

/-- The root asymptotic along the natural numbers. -/
theorem tendsto_Gamma_linear_rpow_inv_nat (hc : 0 < c) (b : ℝ) :
    Tendsto (fun k : ℕ => Real.Gamma (c * (k : ℝ) + b) ^ (1 / (k : ℝ)) / (k : ℝ) ^ c) atTop
      (𝓝 ((c / Real.exp 1) ^ c)) :=
  (tendsto_Gamma_linear_rpow_inv hc b).comp tendsto_natCast_atTop_atTop

/-- **The root of the factorial**: `(k!)^{1/k}/k → 1/e`. -/
theorem tendsto_factorial_rpow_inv_div :
    Tendsto (fun k : ℕ => ((k.factorial : ℝ)) ^ (1 / (k : ℝ)) / (k : ℝ)) atTop
      (𝓝 (1 / Real.exp 1)) := by
  have h := tendsto_Gamma_linear_rpow_inv_nat (c := 1) one_pos 1
  rw [Real.rpow_one] at h
  refine h.congr fun k => ?_
  rw [one_mul, Real.Gamma_nat_eq_factorial, Real.rpow_one]

end

end GaloisForLFunctions.HTGeometry
