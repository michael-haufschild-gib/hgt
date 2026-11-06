import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheInnerFieldOfZeta

/-!
# The Euler columns of the inner field

The inner field `I_E(w) = ∫ log|E| P_w − log|E(w)|` of a datum `E` is the Green potential of its right zeros (`hasSum_innerOf`). On
the simplest arithmetic datum, the column `F(s) = 1 − c p^{−s}`, it is explicit.

* **The reflection of a column** (`norm_column_line`). On `Re s = ½`, `|1 − c x| = (|c|/√p)|1 − (p/c̄)x|` at `x = p^{−s}`. So the line cannot distinguish a column from its reflection, up to the constant `|c|/√p`.
* **The closed form** (`innerOf_column`). If `|c| > √p`, then `I_F(w) = log(|c|/√p) + log|G(w)| − log|F(w)|`, with `G` the reflected column, which has no right zeros. If `|c| ≤ √p`, the column is outer and `I_F = 0` (`innerOf_column_of_le`).
* **Inner mass at infinity is the Mahler measure** (`tendsto_innerOf_column`, `tendsto_innerOf_column_of_le`). `I_F(σ + it) → log⁺(|c|/√p)` as `σ → ∞`: the mass of the curve chain, for the single inverse root `β = c/√p`.
  Finite inner degree forces the limit `0`, and here the right zeros are periodic (`column_periodic`, `exists_column_zero`). So the limit at infinity measures impurity per period.
* **A finite inner factor** (`innerOf_linear`). The datum `E(s) = s − ρ` has `I_E = G(·, ρ)`. A finite nontrivial inner factor exists as soon as no arithmetic is
  required, which is why the question "finite and nontrivial?" belongs to arithmetic functions only.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- The inner field of a datum. -/
def innerOf (E : ℂ → ℂ) (w : ℂ) : ℝ :=
  (∫ τ : ℝ, Real.log ‖E (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) - Real.log ‖E w‖

variable {E : ℂ → ℂ}

/-- The inner field is the Green potential of the right zeros. -/
theorem hasSum_innerOf (hE : IsHalfPlaneDatum E) {w : ℂ} (hw : IsCentre E w) :
    HasSum (fun ρ : RightZeros E => (analyticOrderNatAt E ρ : ℝ) * greenKernel w ρ) (innerOf E w) :=
  (hasSum_poissonJensen hE hw).2

theorem innerOf_eq_zero_of_no_right_zeros (hE : IsHalfPlaneDatum E) {w : ℂ} (hw : IsCentre E w)
    (hz : ∀ ρ : ℂ, 1 / 2 < ρ.re → E ρ ≠ 0) : innerOf E w = 0 := by
  rw [innerOf, (integrable_and_integral_log_of_no_right_zeros hE hw hz).2, sub_self]

/-- The Poisson kernel is a probability density. -/
theorem integrable_and_integral_poisson {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (halfPlanePoissonKernel w) ∧ ∫ τ : ℝ, halfPlanePoissonKernel w τ = 1 := by
  set e : ℂ := ((Real.exp 1 : ℝ) : ℂ) with he
  have hn : ‖e‖ = Real.exp 1 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hE : IsHalfPlaneDatum fun _ : ℂ => e := by
    refine ⟨differentiable_const _, Real.exp 1 + 1, ?_, fun s _ => ?_⟩
    · linarith [Real.exp_pos 1]
    · rw [hn]
      have h2 : 1 ≤ (‖s‖ + 2) ^ 2 := by nlinarith [norm_nonneg s]
      nlinarith [Real.exp_pos 1]
  have he0 : e ≠ 0 := by
    rw [← norm_pos_iff, hn]
    exact Real.exp_pos _
  have hc : IsCentre (fun _ : ℂ => e) w :=
    ⟨hw, he0, Real.exp 1, 0, Real.exp_pos _, fun σ _ => by rw [hn]⟩
  have h := integrable_and_integral_log_of_no_right_zeros hE hc fun _ _ => he0
  simp only [hn, Real.log_exp, one_mul] at h
  exact h

/-! ### Columns -/

/-- The column `1 − c p^{−s}`. -/
def column (p : ℝ) (c s : ℂ) : ℂ := 1 - c * (p : ℂ) ^ (-s)

variable {p : ℝ} {c : ℂ}

theorem norm_cpow_neg (hp : 1 < p) (s : ℂ) : ‖(p : ℂ) ^ (-s)‖ = p ^ (-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]

theorem differentiable_column (hp : 1 < p) (c : ℂ) : Differentiable ℂ (column p c) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by linarith : p ≠ 0)
  unfold column
  exact (differentiable_const _).sub
    ((differentiable_const _).mul (differentiable_neg.const_cpow (Or.inl hp0)))

theorem rpow_neg_le_of_half_le (hp : 1 < p) {σ : ℝ} (hσ : 1 / 2 ≤ σ) : p ^ (-σ) ≤ p ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)

theorem isHalfPlaneDatum_column (hp : 1 < p) (c : ℂ) : IsHalfPlaneDatum (column p c) := by
  refine ⟨differentiable_column hp c, 1 + ‖c‖, by linarith [norm_nonneg c], fun s hs => ?_⟩
  have h1 : ‖column p c s‖ ≤ 1 + ‖c‖ := by
    unfold column
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_cpow_neg hp]
    have h2 : p ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp.le (by linarith)
    have := mul_le_mul_of_nonneg_left h2 (norm_nonneg c)
    linarith
  have h2 : 1 ≤ (‖s‖ + 2) ^ 2 := by nlinarith [norm_nonneg s]
  nlinarith [norm_nonneg c]

/-- The base of the exponentials tends to `0`. -/
theorem tendsto_rpow_neg (hp : 1 < p) : Tendsto (fun σ : ℝ => p ^ (-σ)) atTop (𝓝 0) := by
  have hl : 0 < Real.log p := Real.log_pos hp
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hl)
  refine h.congr fun σ => ?_
  simp only [Function.comp, id]
  rw [Real.rpow_def_of_pos (by linarith)]
  congr 1
  ring

theorem norm_sub_one_column (hp : 1 < p) (c s : ℂ) : ‖column p c s - 1‖ = ‖c‖ * p ^ (-s.re) := by
  have e : column p c s - 1 = -(c * (p : ℂ) ^ (-s)) := by
    unfold column
    ring
  rw [e, norm_neg, norm_mul, norm_cpow_neg hp]

/-- A column tends to `1` to the right. -/
theorem tendsto_column (hp : 1 < p) (c : ℂ) (t : ℝ) :
    Tendsto (fun σ : ℝ => column p c ((σ : ℂ) + t * I)) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [norm_sub_one_column hp]
  have h := (tendsto_rpow_neg hp).const_mul ‖c‖
  rw [mul_zero] at h
  refine h.congr fun σ => ?_
  simp

/-- A column is at least `½` far to the right. -/
theorem exists_ray_bound (hp : 1 < p) (c : ℂ) :
    ∃ σ₁ : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ t : ℝ, 1 / 2 ≤ ‖column p c ((σ : ℂ) + t * I)‖ := by
  have h := ((tendsto_rpow_neg hp).const_mul ‖c‖).eventually (gt_mem_nhds
    (by rw [mul_zero]; norm_num : ‖c‖ * (0 : ℝ) < 1 / 2))
  obtain ⟨σ₁, hσ₁⟩ := eventually_atTop.mp h
  refine ⟨σ₁, fun σ hσ t => ?_⟩
  have h1 := hσ₁ σ hσ
  have h2 := norm_sub_one_column hp c ((σ : ℂ) + t * I)
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  rw [hre] at h2
  have h3 : ‖(1 : ℂ)‖ - ‖column p c ((σ : ℂ) + t * I)‖ ≤ ‖column p c ((σ : ℂ) + t * I) - 1‖ := by
    rw [norm_sub_rev (column p c _) 1]
    exact norm_sub_norm_le _ _
  rw [norm_one, h2] at h3
  linarith

/-- A column is a centre wherever it does not vanish. -/
theorem isCentre_column (hp : 1 < p) (c : ℂ) {w : ℂ} (hw : 1 / 2 < w.re) (h0 : column p c w ≠ 0) :
    IsCentre (column p c) w := by
  obtain ⟨σ₁, hσ₁⟩ := exists_ray_bound hp c
  exact ⟨hw, h0, 1 / 2, σ₁, by norm_num, fun σ hσ => hσ₁ σ hσ _⟩

/-- A column with `|d| p^{−½} < 1` has no zero in `Re s ≥ ½`. -/
theorem column_ne_zero_of_small (hp : 1 < p) {d : ℂ} (hd : ‖d‖ * p ^ (-(1 / 2 : ℝ)) < 1) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : column p d s ≠ 0 := by
  intro h0
  have h1 := norm_sub_one_column hp d s
  rw [h0, zero_sub, norm_neg, norm_one] at h1
  have h2 := mul_le_mul_of_nonneg_left (rpow_neg_le_of_half_le hp hs) (norm_nonneg d)
  linarith

theorem sqrt_inv_eq_rpow (hp : 1 < p) : p ^ (-(1 / 2 : ℝ)) = (Real.sqrt p)⁻¹ := by
  rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow]

/-- **The line does not distinguish a column from its reflection.** -/
theorem norm_column_line (hp : 1 < p) (hc : c ≠ 0) (τ : ℝ) :
    ‖column p c (1 / 2 + τ * I)‖ = ‖c‖ / Real.sqrt p * ‖column p (p / conj c) (1 / 2 + τ * I)‖ := by
  set s : ℂ := 1 / 2 + τ * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  set x : ℂ := (p : ℂ) ^ (-s) with hx
  have hp0 : 0 < p := by linarith
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hxn : ‖x‖ = (Real.sqrt p)⁻¹ := by
    rw [hx, norm_cpow_neg hp, hre, sqrt_inv_eq_rpow hp]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hconj : conj c ≠ 0 := (map_ne_zero _).mpr hc
  have hxx : (p : ℂ) * (x * conj x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hxn]
    have : (Real.sqrt p)⁻¹ ^ 2 = p⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hp0.le]
    rw [this]
    push_cast
    exact mul_inv_cancel₀ hpC
  have hG : column p (p / conj c) s = -((p : ℂ) * x / conj c) * conj (column p c s) := by
    simp only [column, ← hx, map_sub, map_one, map_mul]
    field_simp
    linear_combination -(conj c) * hxx
  have hconjn : ‖conj c‖ = ‖c‖ := RCLike.norm_conj c
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [hG, norm_mul, norm_neg, norm_div, norm_mul, hxn, hconjn, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hp0]
  have hpp : p = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt hp0.le).symm
  field_simp
  rw [Real.sq_sqrt hp0.le]

theorem reflected_small (hp : 1 < p) (hc : Real.sqrt p < ‖c‖) :
    ‖(p : ℂ) / conj c‖ * p ^ (-(1 / 2 : ℝ)) < 1 := by
  have hp0 : 0 < p := by linarith
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hcn : 0 < ‖c‖ := hsq.trans hc
  rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0,
    sqrt_inv_eq_rpow hp]
  have e : p / ‖c‖ * (Real.sqrt p)⁻¹ = Real.sqrt p / ‖c‖ := by
    have hpp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
    calc p / ‖c‖ * (Real.sqrt p)⁻¹ = (Real.sqrt p * Real.sqrt p) / ‖c‖ * (Real.sqrt p)⁻¹ := by rw [hpp]
      _ = Real.sqrt p / ‖c‖ := by field_simp
  rw [e, div_lt_one hcn]
  exact hc

/-- **The closed form** beyond the reflection threshold. -/
theorem innerOf_column (hp : 1 < p) (hc : Real.sqrt p < ‖c‖) {w : ℂ} (hw : IsCentre (column p c) w) :
    innerOf (column p c) w =
      Real.log (‖c‖ / Real.sqrt p) + Real.log ‖column p (p / conj c) w‖ - Real.log ‖column p c w‖ := by
  have hp0 : 0 < p := by linarith
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hcn : 0 < ‖c‖ := hsq.trans hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcn
  set a : ℝ := ‖c‖ / Real.sqrt p with ha
  have ha0 : 0 < a := div_pos hcn hsq
  set d : ℂ := (p : ℂ) / conj c with hd
  have hsmall := reflected_small hp hc
  have hG : IsCentre (column p d) w :=
    isCentre_column hp d hw.re_gt (column_ne_zero_of_small hp hsmall hw.re_gt.le)
  have hGz : ∀ ρ : ℂ, 1 / 2 < ρ.re → column p d ρ ≠ 0 := fun ρ hρ =>
    column_ne_zero_of_small hp hsmall hρ.le
  obtain ⟨hint, hval⟩ := integrable_and_integral_log_of_no_right_zeros
    (isHalfPlaneDatum_column hp d) hG hGz
  obtain ⟨hP, hP1⟩ := integrable_and_integral_poisson hw.re_gt
  have hpt : ∀ τ : ℝ, Real.log ‖column p c (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ =
      Real.log a * halfPlanePoissonKernel w τ +
        Real.log ‖column p d (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ := fun τ => by
    have hne : column p d (1 / 2 + τ * I) ≠ 0 :=
      column_ne_zero_of_small hp hsmall (by simp)
    rw [norm_column_line hp hc0 τ, Real.log_mul ha0.ne' (norm_ne_zero_iff.mpr hne)]
    ring
  rw [innerOf, integral_congr_ae (Eventually.of_forall hpt),
    integral_add (hP.const_mul _) hint, integral_const_mul, hP1, hval, mul_one]

/-- Below the reflection threshold a column is outer. -/
theorem innerOf_column_of_le (hp : 1 < p) (hc : ‖c‖ ≤ Real.sqrt p) {w : ℂ}
    (hw : IsCentre (column p c) w) : innerOf (column p c) w = 0 := by
  refine innerOf_eq_zero_of_no_right_zeros (isHalfPlaneDatum_column hp c) hw fun ρ hρ h0 => ?_
  have hp0 : 0 < p := by linarith
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have h1 := norm_sub_one_column hp c ρ
  rw [h0, zero_sub, norm_neg, norm_one] at h1
  have h2 : p ^ (-ρ.re) < p ^ (-(1 / 2 : ℝ)) := Real.rpow_lt_rpow_of_exponent_lt hp (by linarith)
  rw [sqrt_inv_eq_rpow hp] at h2
  have h3 : ‖c‖ * (Real.sqrt p)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hsq]
    exact hc
  have hrp : 0 < p ^ (-ρ.re) := Real.rpow_pos_of_pos hp0 _
  by_cases hc0 : ‖c‖ = 0
  · rw [hc0, zero_mul] at h1
    exact one_ne_zero h1
  · have hcn : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg c) (Ne.symm hc0)
    have := mul_lt_mul_of_pos_left h2 hcn
    linarith

/-- **Inner mass at infinity** beyond the threshold: the Mahler measure `log(|c|/√p)`. -/
theorem tendsto_innerOf_column (hp : 1 < p) (hc : Real.sqrt p < ‖c‖) (t : ℝ) :
    Tendsto (fun σ : ℝ => innerOf (column p c) ((σ : ℂ) + t * I)) atTop
      (𝓝 (Real.log (‖c‖ / Real.sqrt p))) := by
  have h1 : Tendsto (fun σ : ℝ => Real.log ‖column p (p / conj c) ((σ : ℂ) + t * I)‖) atTop (𝓝 0) := by
    have := ((tendsto_column hp ((p : ℂ) / conj c) t).norm).log (by simp)
    simpa using this
  have h2 : Tendsto (fun σ : ℝ => Real.log ‖column p c ((σ : ℂ) + t * I)‖) atTop (𝓝 0) := by
    have := ((tendsto_column hp c t).norm).log (by simp)
    simpa using this
  have h3 := (tendsto_const_nhds (x := Real.log (‖c‖ / Real.sqrt p))).add h1 |>.sub h2
  simp only [add_zero, sub_zero] at h3
  refine h3.congr' ?_
  obtain ⟨σ₁, hσ₁⟩ := exists_ray_bound hp c
  filter_upwards [eventually_ge_atTop σ₁, eventually_gt_atTop (1 / 2 : ℝ)] with σ hσ hσ2
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have h0 : column p c ((σ : ℂ) + t * I) ≠ 0 := by
    intro h
    have := hσ₁ σ hσ t
    rw [h, norm_zero] at this
    linarith
  exact (innerOf_column hp hc (isCentre_column hp c (by rw [hre]; exact hσ2) h0)).symm

/-- **Inner mass at infinity** below the threshold is `0`. -/
theorem tendsto_innerOf_column_of_le (hp : 1 < p) (hc : ‖c‖ ≤ Real.sqrt p) (t : ℝ) :
    Tendsto (fun σ : ℝ => innerOf (column p c) ((σ : ℂ) + t * I)) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨σ₁, hσ₁⟩ := exists_ray_bound hp c
  filter_upwards [eventually_ge_atTop σ₁, eventually_gt_atTop (1 / 2 : ℝ)] with σ hσ hσ2
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have h0 : column p c ((σ : ℂ) + t * I) ≠ 0 := by
    intro h
    have := hσ₁ σ hσ t
    rw [h, norm_zero] at this
    linarith
  exact (innerOf_column_of_le hp hc (isCentre_column hp c (by rw [hre]; exact hσ2) h0)).symm

/-- A column is periodic with period `2π/log p`. -/
theorem column_periodic (hp : 1 < p) (c s : ℂ) :
    column p c (s + 2 * Real.pi * I / Real.log p) = column p c s := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by linarith : p ≠ 0)
  have hl : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hp).ne'
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := (Complex.ofReal_log (by linarith)).symm
  unfold column
  congr 2
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hp0, hlog]
  have e : (Real.log p : ℂ) * -(s + 2 * Real.pi * I / Real.log p) =
      (Real.log p : ℂ) * -s - 2 * Real.pi * I := by
    field_simp
    ring
  rw [e, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]

/-- **Beyond the threshold a column has a right zero**, and by periodicity infinitely many. -/
theorem exists_column_zero (hp : 1 < p) (hc : Real.sqrt p < ‖c‖) :
    ∃ ρ : ℂ, 1 / 2 < ρ.re ∧ column p c ρ = 0 := by
  have hp0 : 0 < p := by linarith
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hcn : 0 < ‖c‖ := hsq.trans hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcn
  have hl : 0 < Real.log p := Real.log_pos hp
  have hlC : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := (Complex.ofReal_log hp0.le).symm
  refine ⟨Complex.log c / Real.log p, ?_, ?_⟩
  · have hre : (Complex.log c / (Real.log p : ℂ)).re = Real.log ‖c‖ / Real.log p := by
      rw [Complex.div_ofReal_re, Complex.log_re]
    rw [hre, lt_div_iff₀ hl]
    have h1 : Real.log (Real.sqrt p) < Real.log ‖c‖ := Real.log_lt_log hsq hc
    rw [Real.log_sqrt hp0.le] at h1
    linarith
  · unfold column
    rw [Complex.cpow_def_of_ne_zero hpC, hlog]
    have e : (Real.log p : ℂ) * -(Complex.log c / (Real.log p : ℂ)) = -Complex.log c := by
      field_simp
    rw [e, Complex.exp_neg, Complex.exp_log hc0, mul_inv_cancel₀ hc0, sub_self]

/-! ### A finite inner factor -/

/-- The linear datum `s − ρ`. -/
theorem isHalfPlaneDatum_linear (ρ : ℂ) : IsHalfPlaneDatum fun s => s - ρ := by
  refine ⟨differentiable_id.sub_const ρ, 1 + ‖ρ‖, by linarith [norm_nonneg ρ], fun s _ => ?_⟩
  have h1 : ‖s - ρ‖ ≤ ‖s‖ + ‖ρ‖ := norm_sub_le _ _
  have h2 : (‖s‖ + 2) ^ 2 ≥ ‖s‖ + 2 := by nlinarith [norm_nonneg s]
  nlinarith [norm_nonneg s, norm_nonneg ρ]

theorem isCentre_linear {ρ w : ℂ} (hw : 1 / 2 < w.re) (hne : w ≠ ρ) : IsCentre (fun s => s - ρ) w := by
  refine ⟨hw, sub_ne_zero.mpr hne, 1, ‖ρ‖ + 1, one_pos, fun σ hσ => ?_⟩
  have h1 := Complex.abs_re_le_norm ((σ : ℂ) + (w.im : ℂ) * I)
  have h2 : ((σ : ℂ) + (w.im : ℂ) * I).re = σ := by simp
  rw [h2] at h1
  have h3 := le_abs_self σ
  have h4 := norm_sub_norm_le ((σ : ℂ) + (w.im : ℂ) * I) ρ
  linarith

/-- **A finite inner factor**: the datum `s − ρ` has inner field `G(·, ρ)`. -/
theorem innerOf_linear {ρ w : ℂ} (hρ : 1 / 2 < ρ.re) (hw : 1 / 2 < w.re) (hne : w ≠ ρ) :
    innerOf (fun s => s - ρ) w = greenKernel w ρ := by
  have hS := hasSum_innerOf (isHalfPlaneDatum_linear ρ) (isCentre_linear hw hne)
  let r : RightZeros (fun s => s - ρ) := ⟨ρ, sub_self ρ, hρ⟩
  have hu : ∀ z : RightZeros (fun s => s - ρ), z = r := fun z => Subtype.ext (sub_eq_zero.mp z.2.1)
  have hord : analyticOrderNatAt (fun s : ℂ => s - ρ) ρ = 1 := by
    have han : AnalyticAt ℂ (fun s : ℂ => s - ρ) ρ := by fun_prop
    have h1 : analyticOrderAt (fun s : ℂ => s - ρ) ρ = ((1 : ℕ) : ℕ∞) := by
      rw [han.analyticOrderAt_eq_natCast]
      refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun z => ?_⟩
      simp
    rw [analyticOrderNatAt, h1]
    rfl
  have hsingle : HasSum (fun z : RightZeros (fun s => s - ρ) =>
      (analyticOrderNatAt (fun s : ℂ => s - ρ) (z : ℂ) : ℝ) * greenKernel w z) (greenKernel w ρ) := by
    have h0 := hasSum_single (f := fun z : RightZeros (fun s => s - ρ) =>
      (analyticOrderNatAt (fun s : ℂ => s - ρ) (z : ℂ) : ℝ) * greenKernel w z) r
      (fun z hz => absurd (hu z) hz)
    simpa [r, hord] using h0
  exact hS.unique hsingle

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
