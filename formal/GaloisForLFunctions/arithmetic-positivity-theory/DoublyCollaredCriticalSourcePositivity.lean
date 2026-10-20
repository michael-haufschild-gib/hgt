import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalCompleteFormPolynomialWindows

/-!
# Doubly collared critical sources: compact tests with block positivity uniform in the truncation

The **doubly collared critical source** is

`g^V(x) = χ(e^{-x}/V) σ(e^{-x} - 1) g_b(x)`, with `χ(u) = 1 - σ(u - 1)`.

It is continuous with support in `[-log(2V), 0]`: the lower collar removes the endpoint and the
upper cutoff truncates smoothly on `v = e^{-x} ∈ [V, 2V]`. This module proves that the complete
critical energy of `g^V` is positive definite on every high dyadic block, uniformly in the
truncation length `V`.

* **Prime channel.** For `r ≥ 2` the two upper cutoffs merge, and the dilation weight is
  `w_λ = ψ χ(λ·)` with `λ = r/V`. Since `λ σ'(λv - 1)` vanishes unless `λ < 2/v`, the second
  derivatives satisfy `‖w_λ''‖₁ ≤ ‖ψ''‖₁ + 4 sup|σ'| ‖ψ'‖₁ + 4 sup|σ''| ‖ψ‖₁`, uniformly in `λ`.
  The dyadic dilation inequality then bounds the prime channel by `C_T ∑ b_n²`.
* **Archimedean channel.** The low band of `g^V` is that of the collared source plus the far
  layer `h = (1 - χ) g_c`, whose mass is at most `(U/V) ∑ b_n²` by the dilated `ℓ²` ceiling. The
  Riesz window `[2, 2 + L]` lies inside the truncation, so the high band carries `A_c/4` of the
  mass for `V ≥ V₀`, and `Lévy(g^V) ≥ s_T (log M - c_T) ∑ b_n²`.
* **Gamma and polar channels.** `ac^V(0) ≤ U ∑ b_n²`. Both half-exponential moments are
  integrals of `B_b` against weights vanishing at `v = 1` and at infinity, so they are bounded
  by parts against the bounded primitive, with constants uniform in `V`.

Hence there is `M₀` such that for every `M ≥ M₀`, every `V ≥ V₀`, every dyadic block at `M` and
every nonzero pattern, the complete energy of the compact source `g^V` is positive.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
open _root_.Zeta23

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ### The upper cutoff and doubly collared critical sources -/

/-- **Upper cutoff** `χ(u) = 1 - σ(u - 1)`: equal to `1` on `u ≤ 1`, to `0` on `u ≥ 2`, smooth. -/
def criticalUpperCutoff (u : ℝ) : ℝ := 1 - Real.smoothTransition (u - 1)

theorem criticalUpperCutoff_eq_one {u : ℝ} (hu : u ≤ 1) : criticalUpperCutoff u = 1 := by
  rw [criticalUpperCutoff, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem criticalUpperCutoff_eq_zero {u : ℝ} (hu : 2 ≤ u) : criticalUpperCutoff u = 0 := by
  rw [criticalUpperCutoff, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem criticalUpperCutoff_nonneg (u : ℝ) : 0 ≤ criticalUpperCutoff u := by
  unfold criticalUpperCutoff; linarith [Real.smoothTransition.le_one (u - 1)]

theorem criticalUpperCutoff_le_one (u : ℝ) : criticalUpperCutoff u ≤ 1 := by
  unfold criticalUpperCutoff; linarith [Real.smoothTransition.nonneg (u - 1)]

theorem continuous_criticalUpperCutoff : Continuous criticalUpperCutoff := by
  unfold criticalUpperCutoff
  exact continuous_const.sub (Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const))

/-- **Doubly collared critical source** `g^V(x) = χ(e^{-x}/V) σ(e^{-x} - 1) g_b(x)`: the collared
critical source truncated smoothly on `v = e^{-x} ∈ [V, 2V]`. It is continuous with support in
`[-log(2V), 0]`. -/
def criticalTruncatedSource (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  criticalUpperCutoff (Real.exp (-x) / V) * criticalCollaredSource S b x

/-- The far layer `h = g_c - g^V` removed by the upper cutoff. -/
def criticalTruncationTail (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  (1 - criticalUpperCutoff (Real.exp (-x) / V)) * criticalCollaredSource S b x

theorem criticalTruncatedSource_add_tail (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    criticalTruncatedSource V S b x + criticalTruncationTail V S b x = criticalCollaredSource S b x := by
  unfold criticalTruncatedSource criticalTruncationTail; ring

/-- Clock change of variables `∫_{x ≤ 0} K(e^{-x}) dx = ∫_1^∞ K(v)/v dv`. -/
theorem integral_Iic_zero_comp_exp_neg (K : ℝ → ℝ) :
    (∫ x in Iic (0 : ℝ), K (Real.exp (-x))) = ∫ v in Ioi (1 : ℝ), K v / v := by
  have h1 := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ => K (Real.exp y))
  simp only [neg_zero] at h1
  have h2 := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (fun v => K v / v)
  rw [Real.image_exp_Ioi, Real.exp_zero] at h2
  rw [h2, h1]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [abs_of_pos (Real.exp_pos y), smul_eq_mul]
  have := Real.exp_pos y
  field_simp

private theorem collared_source_eq {S : Finset ℕ} {b : ℕ → ℝ} {x : ℝ} (hx : x ≤ 0) :
    criticalCollaredSource S b x = Real.smoothTransition (Real.exp (-x) - 1) *
      (Real.exp (x / 2) * realPhaseCombination S b (Real.exp (-x))) := by
  simp only [criticalCollaredSource, criticalFactorialSource,
    indicator_of_mem (show x ∈ Iic 0 from hx), factorialPhaseCombination_re_eq]

private theorem collared_source_pos {S : Finset ℕ} {b : ℕ → ℝ} {x : ℝ} (hx : 0 < x) :
    criticalCollaredSource S b x = 0 := by
  simp only [criticalCollaredSource, criticalFactorialSource,
    indicator_of_notMem (show x ∉ Iic 0 from not_le.mpr hx), mul_zero]

/-- **Truncated mass in the dilation variable.** For `V > 0`,
`∫ (g^V)² = ∫_{v>1} σ(v - 1)² χ(v/V)² B_b(v)²/v² dv`. -/
theorem integral_criticalTruncatedSource_sq_eq (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    ∫ x, criticalTruncatedSource V S b x ^ 2 = ∫ v in Ioi 1, Real.smoothTransition (v - 1) ^ 2 *
      criticalUpperCutoff (v / V) ^ 2 * realPhaseCombination S b v ^ 2 / v ^ 2 := by
  set H : ℝ → ℝ := fun v => Real.smoothTransition (v - 1) ^ 2 * criticalUpperCutoff (v / V) ^ 2 *
    realPhaseCombination S b v ^ 2
  have hpt : ∀ x, criticalTruncatedSource V S b x ^ 2 =
      (Iic (0 : ℝ)).indicator (fun x => Real.exp x * H (Real.exp (-x))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx), criticalTruncatedSource, collared_source_eq hx]
      have : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; ring_nf
      simp only [H]
      rw [mul_pow, mul_pow, mul_pow, this]
      ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), criticalTruncatedSource,
        collared_source_pos (not_le.mp hx)]
      ring
  rw [funext hpt, integral_indicator measurableSet_Iic, integral_Iic_zero_exp_mul_comp_exp_neg H]

/-- **Tail mass in the dilation variable.** For `V > 0`,
`∫ h² = ∫_{v>1} σ(v - 1)² (1 - χ(v/V))² B_b(v)²/v² dv`. -/
theorem integral_criticalTruncationTail_sq_eq (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    ∫ x, criticalTruncationTail V S b x ^ 2 = ∫ v in Ioi 1, Real.smoothTransition (v - 1) ^ 2 *
      (1 - criticalUpperCutoff (v / V)) ^ 2 * realPhaseCombination S b v ^ 2 / v ^ 2 := by
  set H : ℝ → ℝ := fun v => Real.smoothTransition (v - 1) ^ 2 * (1 - criticalUpperCutoff (v / V)) ^ 2 *
    realPhaseCombination S b v ^ 2
  have hpt : ∀ x, criticalTruncationTail V S b x ^ 2 =
      (Iic (0 : ℝ)).indicator (fun x => Real.exp x * H (Real.exp (-x))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx), criticalTruncationTail, collared_source_eq hx]
      have : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; ring_nf
      simp only [H]
      rw [mul_pow, mul_pow, mul_pow, this]
      ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), criticalTruncationTail,
        collared_source_pos (not_le.mp hx)]
      ring
  rw [funext hpt, integral_indicator measurableSet_Iic, integral_Iic_zero_exp_mul_comp_exp_neg H]

/-- **Truncated dilation correlation.** For `r ≥ 2` and `V > 0`, the lower collar of the dilated
copy is inactive and the two upper cutoffs merge:
`∫ g^V(x) g^V(x - log r) dx = r^{-1/2} ∫_{v>1} ψ(v) χ(rv/V) B_b(v) B_b(rv) dv`. -/
theorem integral_criticalTruncatedSource_mul_dilate {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ)
    {r : ℕ} (hr : 2 ≤ r) :
    ∫ x, criticalTruncatedSource V S b x * criticalTruncatedSource V S b (x - Real.log r) =
      1 / Real.sqrt r * ∫ v in Ioi 1, criticalCollarWeight v * criticalUpperCutoff (r * v / V) *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v)) := by
  have hr0 : (0 : ℝ) < r := by positivity
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hsqrt : Real.exp (Real.log r / 2) = Real.sqrt r := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr0]; ring_nf
  have hpt : ∀ x, criticalTruncatedSource V S b x * criticalTruncatedSource V S b (x - Real.log r) =
      (Iic (0 : ℝ)).indicator (fun x => 1 / Real.sqrt r * (Real.exp x *
        (Real.smoothTransition (Real.exp (-x) - 1) * criticalUpperCutoff (r * Real.exp (-x) / V) *
          (realPhaseCombination S b (Real.exp (-x)) * realPhaseCombination S b (r * Real.exp (-x)))))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx)]
      have hxr : x - Real.log r ≤ 0 := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ r)]
      have hexp : Real.exp (-(x - Real.log r)) = r * Real.exp (-x) := by
        rw [neg_sub, Real.exp_sub, Real.exp_log hr0, Real.exp_neg]; field_simp
      have he1 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
      have hc : Real.smoothTransition (r * Real.exp (-x) - 1) = 1 :=
        Real.smoothTransition.one_of_one_le (by nlinarith)
      have hcut : criticalUpperCutoff (Real.exp (-x) / V) * criticalUpperCutoff (r * Real.exp (-x) / V) =
          criticalUpperCutoff (r * Real.exp (-x) / V) := by
        rcases le_or_gt 2 (r * Real.exp (-x) / V) with h | h
        · rw [criticalUpperCutoff_eq_zero h, mul_zero]
        · have : Real.exp (-x) / V ≤ 1 := by
            rw [div_le_one hV]
            have h' : r * Real.exp (-x) < 2 * V := by rwa [div_lt_iff₀ hV] at h
            nlinarith
          rw [criticalUpperCutoff_eq_one this, one_mul]
      have hhalf : Real.exp ((x - Real.log r) / 2) = Real.exp (x / 2) / Real.sqrt r := by
        rw [← hsqrt, ← Real.exp_sub]; ring_nf
      have hxx : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by rw [← Real.exp_add]; ring_nf
      rw [criticalTruncatedSource, criticalTruncatedSource, collared_source_eq hx,
        collared_source_eq hxr, hexp, hc, hhalf]
      rw [← hxx]
      calc _ = criticalUpperCutoff (Real.exp (-x) / V) * criticalUpperCutoff (r * Real.exp (-x) / V) *
            (1 / Real.sqrt r * (Real.exp (x / 2) * Real.exp (x / 2) *
              (Real.smoothTransition (Real.exp (-x) - 1) * (realPhaseCombination S b (Real.exp (-x)) *
                realPhaseCombination S b (r * Real.exp (-x)))))) := by ring
        _ = _ := by rw [hcut]; ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), criticalTruncatedSource,
        collared_source_pos (not_le.mp hx)]
      ring
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Iic, integral_const_mul,
    integral_Iic_zero_exp_mul_comp_exp_neg (fun v => Real.smoothTransition (v - 1) *
      criticalUpperCutoff (r * v / V) * (realPhaseCombination S b v * realPhaseCombination S b (r * v)))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [criticalCollarWeight]
  ring

/-! ### Derivative bounds of the smooth transition -/

private theorem contDiff_deriv_smoothTransition : ContDiff ℝ (⊤ : ℕ∞) (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2

private theorem contDiff_deriv_deriv_smoothTransition :
    ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv Real.smoothTransition)) :=
  (contDiff_infty_iff_deriv.mp contDiff_deriv_smoothTransition).2

private theorem eq_zero_outside_of_locally {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ y, y < 0 → f y = 0) (h1 : ∀ y, 1 < y → f y = 0) {y : ℝ} (hy : y ∉ Ioo (0 : ℝ) 1) :
    f y = 0 := by
  have hT : IsClosed {y | f y = 0} := isClosed_eq hf continuous_const
  rcases le_or_gt y 0 with hy0 | hy0
  · have := (hT.closure_subset_iff (s := Iio 0)).mpr (fun z hz => h0 z hz)
    rw [closure_Iio' nonempty_Iio] at this
    exact this hy0
  · have hy1 : 1 ≤ y := by
      by_contra h; exact hy ⟨hy0, not_le.mp h⟩
    have := (hT.closure_subset_iff (s := Ioi 1)).mpr (fun z hz => h1 z hz)
    rw [closure_Ioi' nonempty_Ioi] at this
    exact this hy1

private theorem smoothTransition_locally_const {y : ℝ} (hy : y < 0 ∨ 1 < y) :
    ∃ c : ℝ, Real.smoothTransition =ᶠ[𝓝 y] fun _ => c := by
  rcases hy with hy | hy
  · refine ⟨0, ?_⟩
    filter_upwards [Iio_mem_nhds hy] with z hz
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
  · refine ⟨1, ?_⟩
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact Real.smoothTransition.one_of_one_le (le_of_lt hz)

/-- The smooth transition is flat outside `(0, 1)`: `σ' = 0` there. -/
private theorem deriv_smoothTransition_eq_zero {y : ℝ} (hy : y ∉ Ioo (0 : ℝ) 1) :
    deriv Real.smoothTransition y = 0 := by
  refine eq_zero_outside_of_locally contDiff_deriv_smoothTransition.continuous (fun z hz => ?_)
    (fun z hz => ?_) hy
  · obtain ⟨c, hc⟩ := smoothTransition_locally_const (Or.inl hz)
    rw [hc.deriv_eq, deriv_const]
  · obtain ⟨c, hc⟩ := smoothTransition_locally_const (Or.inr hz)
    rw [hc.deriv_eq, deriv_const]

/-- `σ'' = 0` outside `(0, 1)`. -/
private theorem deriv_deriv_smoothTransition_eq_zero {y : ℝ} (hy : y ∉ Ioo (0 : ℝ) 1) :
    deriv (deriv Real.smoothTransition) y = 0 := by
  have hloc {z : ℝ} (hz : z < 0 ∨ 1 < z) : deriv Real.smoothTransition =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    rcases hz with hz | hz
    · filter_upwards [Iio_mem_nhds hz] with w hw
      exact deriv_smoothTransition_eq_zero fun h => (lt_irrefl _ (lt_trans h.1 hw))
    · filter_upwards [Ioi_mem_nhds hz] with w hw
      exact deriv_smoothTransition_eq_zero fun h => (lt_irrefl _ (lt_trans h.2 hw))
  refine eq_zero_outside_of_locally contDiff_deriv_deriv_smoothTransition.continuous
    (fun z hz => ?_) (fun z hz => ?_) hy
  · rw [(hloc (Or.inl hz)).deriv_eq, deriv_const]
  · rw [(hloc (Or.inr hz)).deriv_eq, deriv_const]

private theorem exists_abs_le_of_support {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ y, y ∉ Ioo (0 : ℝ) 1 → f y = 0) : ∃ C, 0 ≤ C ∧ ∀ y, |f y| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ Ioo (0 : ℝ) 1
  · have := hC y (Ioo_subset_Icc_self hy)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [h y hy, abs_zero]; exact le_max_right _ _

private theorem exists_abs_deriv_smoothTransition_le :
    ∃ C, 0 ≤ C ∧ ∀ y, |deriv Real.smoothTransition y| ≤ C :=
  exists_abs_le_of_support contDiff_deriv_smoothTransition.continuous
    fun _ hy => deriv_smoothTransition_eq_zero hy

private theorem exists_abs_deriv_deriv_smoothTransition_le :
    ∃ C, 0 ≤ C ∧ ∀ y, |deriv (deriv Real.smoothTransition) y| ≤ C :=
  exists_abs_le_of_support contDiff_deriv_deriv_smoothTransition.continuous
    fun _ hy => deriv_deriv_smoothTransition_eq_zero hy

/-- Slope bound `sup |σ'|` of the smooth transition. -/
def smoothTransitionSlope : ℝ := Classical.choose exists_abs_deriv_smoothTransition_le

/-- Curvature bound `sup |σ''|` of the smooth transition. -/
def smoothTransitionCurvature : ℝ := Classical.choose exists_abs_deriv_deriv_smoothTransition_le

theorem smoothTransitionSlope_nonneg : 0 ≤ smoothTransitionSlope :=
  (Classical.choose_spec exists_abs_deriv_smoothTransition_le).1

theorem abs_deriv_smoothTransition_le (y : ℝ) : |deriv Real.smoothTransition y| ≤ smoothTransitionSlope :=
  (Classical.choose_spec exists_abs_deriv_smoothTransition_le).2 y

theorem smoothTransitionCurvature_nonneg : 0 ≤ smoothTransitionCurvature :=
  (Classical.choose_spec exists_abs_deriv_deriv_smoothTransition_le).1

theorem abs_deriv_deriv_smoothTransition_le (y : ℝ) :
    |deriv (deriv Real.smoothTransition) y| ≤ smoothTransitionCurvature :=
  (Classical.choose_spec exists_abs_deriv_deriv_smoothTransition_le).2 y

/-- On `v ≥ 1` the scaled slope `λ σ'(λv - 1)` is at most `2 sup|σ'|`, since it vanishes unless `λ < 2`. -/
theorem abs_mul_deriv_smoothTransition_le {lam v : ℝ} (hl : 0 ≤ lam) (hv : 1 ≤ v) :
    |lam * deriv Real.smoothTransition (lam * v - 1)| ≤ 2 * smoothTransitionSlope := by
  by_cases h : lam * v - 1 ∈ Ioo (0 : ℝ) 1
  · have hl2 : lam ≤ 2 := by nlinarith [h.2]
    rw [abs_mul, abs_of_nonneg hl]
    exact mul_le_mul hl2 (abs_deriv_smoothTransition_le _) (abs_nonneg _) (by norm_num)
  · rw [deriv_smoothTransition_eq_zero h, mul_zero, abs_zero]
    have := smoothTransitionSlope_nonneg; positivity

/-- On `v ≥ 1` the scaled curvature `λ² σ''(λv - 1)` is at most `4 sup|σ''|`. -/
theorem abs_sq_mul_deriv_deriv_smoothTransition_le {lam v : ℝ} (hl : 0 ≤ lam) (hv : 1 ≤ v) :
    |lam ^ 2 * deriv (deriv Real.smoothTransition) (lam * v - 1)| ≤ 4 * smoothTransitionCurvature := by
  by_cases h : lam * v - 1 ∈ Ioo (0 : ℝ) 1
  · have hl2 : lam ≤ 2 := by nlinarith [h.2]
    rw [abs_mul, abs_of_nonneg (sq_nonneg lam)]
    have : lam ^ 2 ≤ 4 := by nlinarith
    exact mul_le_mul this (abs_deriv_deriv_smoothTransition_le _) (abs_nonneg _) (by norm_num)
  · rw [deriv_deriv_smoothTransition_eq_zero h, mul_zero, abs_zero]
    have := smoothTransitionCurvature_nonneg; positivity

/-! ### The truncated collar weight -/

/-- **Truncated collar weight** `w_λ(v) = ψ(v) χ(λv)`: the weight of the dilation correlations of a
doubly collared source, with `λ = r/V`. -/
def criticalTruncatedWeight (lam v : ℝ) : ℝ := criticalCollarWeight v * criticalUpperCutoff (lam * v)

/-- First derivative of the truncated weight. -/
def criticalTruncatedWeightDeriv (lam v : ℝ) : ℝ :=
  deriv criticalCollarWeight v * criticalUpperCutoff (lam * v) +
    criticalCollarWeight v * -(lam * deriv Real.smoothTransition (lam * v - 1))

/-- Second derivative of the truncated weight. -/
def criticalTruncatedWeightDeriv2 (lam v : ℝ) : ℝ :=
  deriv (deriv criticalCollarWeight) v * criticalUpperCutoff (lam * v) +
    2 * (deriv criticalCollarWeight v * -(lam * deriv Real.smoothTransition (lam * v - 1))) +
    criticalCollarWeight v * -(lam ^ 2 * deriv (deriv Real.smoothTransition) (lam * v - 1))

private theorem hasDerivAt_cutoff_scale (lam v : ℝ) :
    HasDerivAt (fun v => criticalUpperCutoff (lam * v))
      (-(lam * deriv Real.smoothTransition (lam * v - 1))) v := by
  have hσ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (lam * v - 1)) (lam * v - 1) :=
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) _).hasDerivAt
  have hin : HasDerivAt (fun v => lam * v - 1) lam v := by
    simpa using ((hasDerivAt_id v).const_mul lam).sub_const 1
  have h := (hσ.comp v hin).const_sub 1
  have h' : HasDerivAt (fun v => criticalUpperCutoff (lam * v))
      (-(deriv Real.smoothTransition (lam * v - 1) * lam)) v := h
  refine h'.congr_deriv ?_
  ring

private theorem hasDerivAt_slope_scale (lam v : ℝ) :
    HasDerivAt (fun v => -(lam * deriv Real.smoothTransition (lam * v - 1)))
      (-(lam ^ 2 * deriv (deriv Real.smoothTransition) (lam * v - 1))) v := by
  have hσ : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) (lam * v - 1)) (lam * v - 1) :=
    (contDiff_deriv_smoothTransition.differentiable (by simp) _).hasDerivAt
  have hin : HasDerivAt (fun v => lam * v - 1) lam v := by
    simpa using ((hasDerivAt_id v).const_mul lam).sub_const 1
  refine (((hσ.comp v hin).const_mul lam).neg).congr_deriv ?_
  ring

theorem hasDerivAt_criticalTruncatedWeight (lam v : ℝ) :
    HasDerivAt (criticalTruncatedWeight lam) (criticalTruncatedWeightDeriv lam v) v :=
  ((hasDerivAt_criticalCollarWeight v).mul (hasDerivAt_cutoff_scale lam v)).congr_deriv (by
    unfold criticalTruncatedWeightDeriv; ring)

theorem hasDerivAt_criticalTruncatedWeightDeriv (lam v : ℝ) :
    HasDerivAt (criticalTruncatedWeightDeriv lam) (criticalTruncatedWeightDeriv2 lam v) v := by
  have h1 := (hasDerivAt_deriv_criticalCollarWeight v).mul (hasDerivAt_cutoff_scale lam v)
  have h2 := (hasDerivAt_criticalCollarWeight v).mul (hasDerivAt_slope_scale lam v)
  exact (h1.add h2).congr_deriv (by unfold criticalTruncatedWeightDeriv2; ring)

private theorem abs_cutoff_le (u : ℝ) : |criticalUpperCutoff u| ≤ 1 := by
  rw [abs_of_nonneg (criticalUpperCutoff_nonneg u)]; exact criticalUpperCutoff_le_one u

theorem abs_criticalTruncatedWeight_le (lam v : ℝ) :
    |criticalTruncatedWeight lam v| ≤ |criticalCollarWeight v| := by
  rw [criticalTruncatedWeight, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cutoff_le _)

theorem abs_criticalTruncatedWeightDeriv_le {lam v : ℝ} (hl : 0 ≤ lam) (hv : 1 ≤ v) :
    |criticalTruncatedWeightDeriv lam v| ≤
      |deriv criticalCollarWeight v| + 2 * smoothTransitionSlope * |criticalCollarWeight v| := by
  unfold criticalTruncatedWeightDeriv
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cutoff_le _)
  · rw [abs_mul, abs_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_mul_deriv_smoothTransition_le hl hv) (abs_nonneg _)

theorem abs_criticalTruncatedWeightDeriv2_le {lam v : ℝ} (hl : 0 ≤ lam) (hv : 1 ≤ v) :
    |criticalTruncatedWeightDeriv2 lam v| ≤ |deriv (deriv criticalCollarWeight) v| +
      4 * smoothTransitionSlope * |deriv criticalCollarWeight v| +
        4 * smoothTransitionCurvature * |criticalCollarWeight v| := by
  unfold criticalTruncatedWeightDeriv2
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cutoff_le _)
  · rw [abs_mul, abs_two, abs_mul, abs_neg]
    have := abs_mul_deriv_smoothTransition_le hl hv
    nlinarith [abs_nonneg (deriv criticalCollarWeight v)]
  · rw [abs_mul, abs_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_sq_mul_deriv_deriv_smoothTransition_le hl hv) (abs_nonneg _)

private theorem continuous_criticalTruncatedWeight (lam : ℝ) : Continuous (criticalTruncatedWeight lam) :=
  contDiff_criticalCollarWeight.continuous.mul (continuous_criticalUpperCutoff.comp (continuous_const.mul continuous_id))

private theorem continuous_criticalTruncatedWeightDeriv (lam : ℝ) :
    Continuous (criticalTruncatedWeightDeriv lam) := by
  unfold criticalTruncatedWeightDeriv
  exact (contDiff_deriv_criticalCollarWeight.continuous.mul
    (continuous_criticalUpperCutoff.comp (continuous_const.mul continuous_id))).add
    (contDiff_criticalCollarWeight.continuous.mul (continuous_const.mul
      (contDiff_deriv_smoothTransition.continuous.comp ((continuous_const.mul continuous_id).sub continuous_const))).neg)

private theorem continuous_criticalTruncatedWeightDeriv2 (lam : ℝ) :
    Continuous (criticalTruncatedWeightDeriv2 lam) := by
  unfold criticalTruncatedWeightDeriv2
  have hdd := (contDiff_infty_iff_deriv.mp contDiff_deriv_criticalCollarWeight).2.continuous
  exact ((hdd.mul (continuous_criticalUpperCutoff.comp (continuous_const.mul continuous_id))).add
    (continuous_const.mul (contDiff_deriv_criticalCollarWeight.continuous.mul (continuous_const.mul
      (contDiff_deriv_smoothTransition.continuous.comp ((continuous_const.mul continuous_id).sub continuous_const))).neg))).add
    (contDiff_criticalCollarWeight.continuous.mul (continuous_const.mul
      (contDiff_deriv_deriv_smoothTransition.continuous.comp
        ((continuous_const.mul continuous_id).sub continuous_const))).neg)

theorem integrableOn_criticalTruncatedWeight (lam : ℝ) :
    IntegrableOn (criticalTruncatedWeight lam) (Ioi 1) :=
  integrableOn_criticalCollarWeight.abs.mono' (continuous_criticalTruncatedWeight lam).aestronglyMeasurable
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact abs_criticalTruncatedWeight_le lam v)

theorem integrableOn_criticalTruncatedWeightDeriv {lam : ℝ} (hl : 0 ≤ lam) :
    IntegrableOn (criticalTruncatedWeightDeriv lam) (Ioi 1) := by
  refine (integrableOn_deriv_criticalCollarWeight.abs.add
    (integrableOn_criticalCollarWeight.abs.const_mul (2 * smoothTransitionSlope))).mono'
    (continuous_criticalTruncatedWeightDeriv lam).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [Real.norm_eq_abs]
  exact abs_criticalTruncatedWeightDeriv_le hl (le_of_lt hv)

/-- Curvature constant `(‖ψ''‖₁ + 4 sup|σ'| ‖ψ'‖₁ + 4 sup|σ''| ‖ψ‖₁)/(4π²)` of truncated weights. -/
def criticalTruncatedCurvature : ℝ :=
  ((∫ v in Ioi 1, |deriv (deriv criticalCollarWeight) v|) +
    4 * smoothTransitionSlope * (∫ v in Ioi 1, |deriv criticalCollarWeight v|) +
      4 * smoothTransitionCurvature * ∫ v in Ioi 1, |criticalCollarWeight v|) / (4 * Real.pi ^ 2)

theorem criticalTruncatedCurvature_nonneg : 0 ≤ criticalTruncatedCurvature := by
  unfold criticalTruncatedCurvature
  have h1 : 0 ≤ ∫ v in Ioi 1, |deriv (deriv criticalCollarWeight) v| := integral_nonneg fun _ => abs_nonneg _
  have h2 : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
  have h3 : 0 ≤ ∫ v in Ioi 1, |criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
  have := smoothTransitionSlope_nonneg
  have := smoothTransitionCurvature_nonneg
  positivity

/-- **Uniform transform bounds of truncated weights.** For every `λ ≥ 0`:
`|F_{w_λ}| ≤ ‖ψ‖₁` and `|F_{w_λ}(f)| ≤ κ_T/f²`, uniformly in `λ`. -/
theorem abs_weightCosineTransform_criticalTruncatedWeight_le {lam : ℝ} (hl : 0 ≤ lam) :
    (∀ f, |weightCosineTransform (criticalTruncatedWeight lam) f| ≤ criticalCollarMass) ∧
    (∀ f, f ≠ 0 → |weightCosineTransform (criticalTruncatedWeight lam) f| ≤
      criticalTruncatedCurvature / f ^ 2) := by
  have hψ := integrableOn_criticalCollarWeight
  have hψ1 := integrableOn_deriv_criticalCollarWeight
  have hψ2 := integrableOn_deriv_deriv_criticalCollarWeight
  have hi : IntegrableOn (criticalTruncatedWeight lam) (Ioi 1) :=
    hψ.abs.mono' (continuous_criticalTruncatedWeight lam).aestronglyMeasurable
      (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact abs_criticalTruncatedWeight_le lam v)
  have hi1 : IntegrableOn (criticalTruncatedWeightDeriv lam) (Ioi 1) := by
    refine (hψ1.abs.add (hψ.abs.const_mul (2 * smoothTransitionSlope))).mono'
      (continuous_criticalTruncatedWeightDeriv lam).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs]
    exact abs_criticalTruncatedWeightDeriv_le hl (le_of_lt hv)
  have hi2 : IntegrableOn (criticalTruncatedWeightDeriv2 lam) (Ioi 1) := by
    refine ((hψ2.abs.add (hψ1.abs.const_mul (4 * smoothTransitionSlope))).add
      (hψ.abs.const_mul (4 * smoothTransitionCurvature))).mono'
      (continuous_criticalTruncatedWeightDeriv2 lam).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs]
    exact abs_criticalTruncatedWeightDeriv2_le hl (le_of_lt hv)
  refine ⟨fun f => ?_, fun f hf => ?_⟩
  · unfold weightCosineTransform criticalCollarMass
    refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on ?_ hψ.abs measurableSet_Ioi
      fun v _ => ?_)
    · exact (hi.mul_bdd (by fun_prop : Continuous fun v => Real.cos (2 * Real.pi * f * v)).aestronglyMeasurable
        (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)).abs
    · rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans
        (abs_criticalTruncatedWeight_le lam v)
  · have hω : 2 * Real.pi * f ≠ 0 := mul_ne_zero (by positivity) hf
    have h0 : criticalTruncatedWeight lam 1 = 0 := by
      rw [criticalTruncatedWeight, criticalCollarWeight_eq_zero le_rfl, zero_mul]
    have h0' : criticalTruncatedWeightDeriv lam 1 = 0 := by
      simp [criticalTruncatedWeightDeriv, deriv_criticalCollarWeight_eq_zero le_rfl,
        criticalCollarWeight_eq_zero le_rfl]
    have ht : Tendsto (criticalTruncatedWeight lam) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (g := fun v => |criticalCollarWeight v|) (fun _ => norm_nonneg _) (fun v => by
        rw [Real.norm_eq_abs]; exact abs_criticalTruncatedWeight_le lam v)
        (by simpa using tendsto_criticalCollarWeight_atTop.abs)
    have ht' : Tendsto (criticalTruncatedWeightDeriv lam) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (by simpa using (tendsto_deriv_criticalCollarWeight_atTop.abs.add
          (tendsto_criticalCollarWeight_atTop.abs.const_mul (2 * smoothTransitionSlope))))
      filter_upwards [eventually_ge_atTop 1] with v hv
      rw [Real.norm_eq_abs]
      exact abs_criticalTruncatedWeightDeriv_le hl hv
    have h := abs_integral_Ioi_mul_cos_le_of_flat (a := 1)
      (fun x _ => hasDerivAt_criticalTruncatedWeight lam x)
      (fun x _ => hasDerivAt_criticalTruncatedWeightDeriv lam x) h0 h0' hi hi1 hi2 ht ht' hω
    unfold weightCosineTransform
    refine h.trans ?_
    have hbound : (∫ v in Ioi 1, |criticalTruncatedWeightDeriv2 lam v|) ≤
        (∫ v in Ioi 1, |deriv (deriv criticalCollarWeight) v|) +
          4 * smoothTransitionSlope * (∫ v in Ioi 1, |deriv criticalCollarWeight v|) +
            4 * smoothTransitionCurvature * ∫ v in Ioi 1, |criticalCollarWeight v| := by
      have hsum : (∫ v in Ioi 1, (|deriv (deriv criticalCollarWeight) v| +
          4 * smoothTransitionSlope * |deriv criticalCollarWeight v| +
            4 * smoothTransitionCurvature * |criticalCollarWeight v|)) =
          (∫ v in Ioi 1, |deriv (deriv criticalCollarWeight) v|) +
            4 * smoothTransitionSlope * (∫ v in Ioi 1, |deriv criticalCollarWeight v|) +
              4 * smoothTransitionCurvature * ∫ v in Ioi 1, |criticalCollarWeight v| := by
        rw [integral_add, integral_add, integral_const_mul, integral_const_mul]
        · exact hψ2.abs
        · exact hψ1.abs.const_mul _
        · exact hψ2.abs.add (hψ1.abs.const_mul _)
        · exact hψ.abs.const_mul _
      rw [← hsum]
      refine setIntegral_mono_on hi2.abs ((hψ2.abs.add (hψ1.abs.const_mul _)).add
        (hψ.abs.const_mul _)) measurableSet_Ioi fun v hv => ?_
      exact abs_criticalTruncatedWeightDeriv2_le hl (le_of_lt hv)
    unfold criticalTruncatedCurvature
    rw [div_div, show (2 * Real.pi * f) ^ 2 = 4 * Real.pi ^ 2 * f ^ 2 by ring]
    gcongr

/-! ### The truncated prime channel -/

/-- Prime atom `Λ(r)/√r · ∫ g^V(x) g^V(x - log r) dx` of a doubly collared source. -/
def criticalTruncatedPrimeAtom (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0) *
    ∫ x, criticalTruncatedSource V S b x * criticalTruncatedSource V S b (x - Real.log r)

/-- Prime channel of a doubly collared source. -/
def criticalTruncatedPrimeEnergy (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑' r : ℕ, criticalTruncatedPrimeAtom V S b r

/-- Truncated prime constant `(4/π⁴) K(‖ψ‖₁, κ_T) ∑ Λ(r) r^{-3/2}`, independent of `V`. -/
def criticalTruncatedPrimeConstant : ℝ :=
  4 / Real.pi ^ 4 * dyadicDilationConstant criticalCollarMass criticalTruncatedCurvature *
    ∑' r : ℕ, envelopePrimeMajorant 1 r

private theorem abs_criticalTruncatedPrimeAtom_le {V : ℝ} (hV : 0 < V) {S : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) (r : ℕ) :
    |criticalTruncatedPrimeAtom V S b r| ≤
      4 / Real.pi ^ 4 * dyadicDilationConstant criticalCollarMass criticalTruncatedCurvature *
        (∑ n ∈ S, b n ^ 2) * envelopePrimeMajorant 1 r := by
  unfold criticalTruncatedPrimeAtom envelopePrimeMajorant
  split_ifs with hr
  · have hr0 : (0 : ℝ) < r := by positivity
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
    have hl : 0 ≤ (r : ℝ) / V := by positivity
    obtain ⟨hA, hB⟩ := abs_weightCosineTransform_criticalTruncatedWeight_le hl
    have hK := abs_integral_weight_realPhaseCombination_dilate_le
      (integrableOn_criticalTruncatedWeight ((r : ℝ) / V)) hA hB criticalTruncatedCurvature_nonneg
      hM hS b (r := r) (by omega)
    have hw : (∫ v in Ioi 1, criticalCollarWeight v * criticalUpperCutoff (r * v / V) *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v))) =
        ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
          (realPhaseCombination S b v * realPhaseCombination S b (r * v)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      simp only [criticalTruncatedWeight]
      rw [show (r : ℝ) / V * v = r * v / V by ring]
    rw [integral_criticalTruncatedSource_mul_dilate hV S b hr, hw, abs_mul, abs_mul,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le),
      abs_of_pos (by positivity : 0 < 1 / Real.sqrt r)]
    have hpow : (r : ℝ) ^ ((1 : ℝ) + 1 / 2) = Real.sqrt r * Real.sqrt r * Real.sqrt r := by
      rw [Real.rpow_add hr0, Real.rpow_one, ← Real.sqrt_eq_rpow, Real.mul_self_sqrt hr0.le]
    rw [hpow]
    have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := r))
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r * |_|)
        ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
          (4 / Real.pi ^ 4 * (dyadicDilationConstant criticalCollarMass criticalTruncatedCurvature /
            Real.sqrt r) * ∑ n ∈ S, b n ^ 2)) := by gcongr
      _ = _ := by field_simp
  · simp

/-- **Uniform truncated prime channel.** For every `V > 0`, every dyadic block and every real
coefficient vector, `|P(g^V)| ≤ C_T ∑ b_n²` with `C_T` independent of `V`. -/
theorem abs_criticalTruncatedPrimeEnergy_le {V : ℝ} (hV : 0 < V) {S : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) :
    |criticalTruncatedPrimeEnergy V S b| ≤ criticalTruncatedPrimeConstant * ∑ n ∈ S, b n ^ 2 := by
  set C := 4 / Real.pi ^ 4 * dyadicDilationConstant criticalCollarMass criticalTruncatedCurvature *
    ∑ n ∈ S, b n ^ 2
  have hsum : Summable (envelopePrimeMajorant 1) :=
    summable_envelopePrimeMajorant_of_half_lt (by norm_num)
  have hbd := abs_criticalTruncatedPrimeAtom_le hV hM hS b
  have habs : Summable fun r => ‖criticalTruncatedPrimeAtom V S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => by rw [Real.norm_eq_abs]; exact hbd r)
      (hsum.mul_left C)
  unfold criticalTruncatedPrimeEnergy
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ?_
  refine (habs.tsum_le_tsum (fun r => by rw [Real.norm_eq_abs]; exact hbd r) (hsum.mul_left C)).trans
    (le_of_eq ?_)
  rw [tsum_mul_left]
  unfold criticalTruncatedPrimeConstant
  ring

/-! ### Mass, tail and logarithmic coercivity of doubly collared sources -/

private theorem admissible_of_abs_le {f g : ℝ → ℝ} (hf : AdmissibleSource f) (hg : Measurable g)
    (hle : ∀ x, |g x| ≤ |f x|) : AdmissibleSource g := by
  have hm : AEStronglyMeasurable (fun x => (g x : ℂ)) volume :=
    (Complex.measurable_ofReal.comp hg).aestronglyMeasurable
  have h : ∀ᵐ x ∂volume, ‖(g x : ℂ)‖ ≤ ‖(f x : ℂ)‖ := Eventually.of_forall fun x => by
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]; exact hle x
  exact ⟨hf.1.norm.mono' hm (by simpa using h), hf.2.of_le hm h⟩

private theorem measurable_criticalCollaredSource (S : Finset ℕ) (b : ℕ → ℝ) :
    Measurable (criticalCollaredSource S b) :=
  (by fun_prop : Continuous fun x : ℝ => Real.smoothTransition (Real.exp (-x) - 1)).measurable.mul
    (measurable_criticalFactorialSource S b)

private theorem measurable_cutoff_exp (V : ℝ) : Measurable fun x : ℝ => criticalUpperCutoff (Real.exp (-x) / V) :=
  (continuous_criticalUpperCutoff.comp (by fun_prop : Continuous fun x : ℝ => Real.exp (-x) / V)).measurable

theorem admissibleSource_criticalTruncatedSource (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    AdmissibleSource (criticalTruncatedSource V S b) :=
  admissible_of_abs_le (admissibleSource_criticalCollaredSource S b)
    ((measurable_cutoff_exp V).mul (measurable_criticalCollaredSource S b)) fun x => by
      rw [criticalTruncatedSource, abs_mul, abs_of_nonneg (criticalUpperCutoff_nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (criticalUpperCutoff_le_one _)

theorem admissibleSource_criticalTruncationTail (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    AdmissibleSource (criticalTruncationTail V S b) :=
  admissible_of_abs_le (admissibleSource_criticalCollaredSource S b)
    ((measurable_const.sub (measurable_cutoff_exp V)).mul (measurable_criticalCollaredSource S b)) fun x => by
      rw [criticalTruncationTail, abs_mul, abs_of_nonneg (by linarith [criticalUpperCutoff_le_one (Real.exp (-x) / V)])]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [criticalUpperCutoff_nonneg (Real.exp (-x) / V)])

private theorem abs_realPhaseCombination_le' (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |realPhaseCombination S b v| ≤ 2 * ∑ n ∈ S, |b n| := by
  unfold realPhaseCombination
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [abs_mul]
  nlinarith [abs_factorialPhaseProfile_le (n + 1) v, abs_nonneg (b n)]

private theorem realPhaseCombination_sq_eq (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    realPhaseCombination S b v ^ 2 = ‖factorialPhaseCombination S (fun n => (b n : ℂ)) v‖ ^ 2 := by
  have h : (((factorialPhaseCombination S (fun n => (b n : ℂ)) v).re : ℝ) : ℂ) =
      factorialPhaseCombination S (fun n => (b n : ℂ)) v := factorialPhaseCombination_ofReal_re S b v
  rw [← h, Complex.norm_real, Real.norm_eq_abs, sq_abs, factorialPhaseCombination_re_eq]

/-- **Truncated mass floor.** For `V ≥ 2 + L`, `∫ (g^V)² ≥ A_c ∑ b_n²`. -/
theorem integral_criticalTruncatedSource_sq_ge {V : ℝ} (hV : 2 + factorialWindowLength ≤ V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    criticalCollarMassLower * ∑ n ∈ S, b n ^ 2 ≤ ∫ x, criticalTruncatedSource V S b x ^ 2 := by
  set L := factorialWindowLength
  have hL := factorialWindowLength_pos
  have hVpos : 0 < V := by linarith
  set R := realPhaseCombination S b
  set H : ℝ → ℝ := fun v => Real.smoothTransition (v - 1) ^ 2 * criticalUpperCutoff (v / V) ^ 2 *
    R v ^ 2 / v ^ 2
  have hcR : Continuous fun v => R v ^ 2 := by
    have h := continuous_factorialPhaseCombination S (fun n => (b n : ℂ))
    exact ((Complex.continuous_re.comp h).congr fun v => factorialPhaseCombination_re_eq S b v).pow 2
  have hHint : IntegrableOn H (Ioi 1) := by
    have hw : IntegrableOn (fun v : ℝ => (2 * ∑ n ∈ S, |b n|) ^ 2 * v ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _
    refine hw.mono' ((((by fun_prop : Continuous fun v => Real.smoothTransition (v - 1) ^ 2).mul
      ((continuous_criticalUpperCutoff.comp (continuous_id.div_const V)).pow 2)).mul
      hcR).aestronglyMeasurable.div₀ (measurable_id.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    have h1 : Real.smoothTransition (v - 1) ^ 2 ≤ 1 :=
      pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
    have h2 : criticalUpperCutoff (v / V) ^ 2 ≤ 1 :=
      pow_le_one₀ (criticalUpperCutoff_nonneg _) (criticalUpperCutoff_le_one _)
    have h3 : R v ^ 2 ≤ (2 * ∑ n ∈ S, |b n|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_realPhaseCombination_le' S b v) 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [H]; positivity), Real.rpow_neg hv0.le,
      Real.rpow_two, ← div_eq_mul_inv]
    simp only [H]
    gcongr
    calc Real.smoothTransition (v - 1) ^ 2 * criticalUpperCutoff (v / V) ^ 2 * R v ^ 2 ≤ 1 * 1 * R v ^ 2 := by
          gcongr
      _ ≤ _ := by rw [one_mul, one_mul]; exact h3
  have hfloor : L / (16 * Real.pi ^ 4) * ∑ n ∈ S, b n ^ 2 ≤ ∫ v in Ioc 2 (2 + L), R v ^ 2 := by
    have h := factorialPhaseCombination_window_lower S (fun n => (b n : ℂ)) 2
    rw [intervalIntegral.integral_of_le (by linarith)] at h
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    refine h.trans (le_of_eq (setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_))
    exact (realPhaseCombination_sq_eq S b v).symm
  have hwin : (∫ v in Ioc 2 (2 + L), R v ^ 2) / (2 + L) ^ 2 ≤ ∫ v in Ioc 2 (2 + L), H v := by
    rw [← integral_div]
    refine setIntegral_mono_on (hcR.integrableOn_Icc.mono_set Ioc_subset_Icc_self |>.div_const _)
      (hHint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi one_le_two)))
      measurableSet_Ioc fun v hv => ?_
    have hv2 : 2 < v := hv.1
    have hσ : Real.smoothTransition (v - 1) = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    have hχ : criticalUpperCutoff (v / V) = 1 :=
      criticalUpperCutoff_eq_one (by rw [div_le_one hVpos]; linarith [hv.2])
    simp only [H, hσ, hχ, one_pow, one_mul]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ (by linarith) hv.2 2)
  have hsub : (∫ v in Ioc 2 (2 + L), H v) ≤ ∫ v in Ioi 1, H v :=
    setIntegral_mono_set hHint (Eventually.of_forall fun v => by simp only [H]; positivity)
      (Eventually.of_forall (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi one_le_two)))
  rw [integral_criticalTruncatedSource_sq_eq]
  unfold criticalCollarMassLower
  calc L / (16 * Real.pi ^ 4) / (2 + L) ^ 2 * ∑ n ∈ S, b n ^ 2 =
        (L / (16 * Real.pi ^ 4) * ∑ n ∈ S, b n ^ 2) / (2 + L) ^ 2 := by ring
    _ ≤ (∫ v in Ioc 2 (2 + L), R v ^ 2) / (2 + L) ^ 2 := by gcongr
    _ ≤ _ := hwin.trans hsub

/-- **Tail mass.** For `V ≥ 1`, the far layer removed by the upper cutoff has
`∫ h² ≤ (U/V) ∑ b_n²`. -/
theorem integral_criticalTruncationTail_sq_le {V : ℝ} (hV : 1 ≤ V) (S : Finset ℕ) (b : ℕ → ℝ) :
    ∫ x, criticalTruncationTail V S b x ^ 2 ≤ criticalCollarMassUpper / V * ∑ n ∈ S, b n ^ 2 := by
  have hV0 : 0 < V := by linarith
  set R := realPhaseCombination S b
  set G : ℝ → ℝ := fun v => R v ^ 2 / v ^ 2
  have hG0 (v : ℝ) : 0 ≤ G v := by simp only [G]; positivity
  have hdil := integral_Ioi_one_rpow_neg_two_mul_norm_sq_dilate_le S (fun n => (b n : ℂ)) hV
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hdil
  have hdilR : (∫ u in Ioi 1, u ^ (-2 : ℝ) * R (V * u) ^ 2) ≤ criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by
    refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_) hdil
    rw [realPhaseCombination_sq_eq]
  have hGint : IntegrableOn G (Ioi V) := by
    have h := integrableOn_rpow_neg_two_mul_norm_sq_factorialPhaseCombination S (fun n => (b n : ℂ))
    refine (h.mono_set (Ioi_subset_Ioi hV)).congr_fun (fun v hv => ?_) measurableSet_Ioi
    have hv0 : 0 < v := lt_of_lt_of_le hV0 (le_of_lt hv)
    simp only [G]
    rw [← realPhaseCombination_sq_eq, Real.rpow_neg hv0.le, Real.rpow_two]
    ring
  have hsubst : ∫ v in Ioi V, G v = V⁻¹ * ∫ u in Ioi 1, u ^ (-2 : ℝ) * R (V * u) ^ 2 := by
    have h := integral_comp_mul_left_Ioi G 1 hV0
    rw [mul_one, smul_eq_mul] at h
    rw [show (∫ v in Ioi V, G v) = V * ∫ u in Ioi 1, G (V * u) by
      rw [h]; field_simp]
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := lt_trans one_pos hu
    simp only [G]
    rw [Real.rpow_neg hu0.le, Real.rpow_two]
    field_simp
  have hpt : ∀ v ∈ Ioi (1 : ℝ), Real.smoothTransition (v - 1) ^ 2 * (1 - criticalUpperCutoff (v / V)) ^ 2 *
      R v ^ 2 / v ^ 2 ≤ (Ioi V).indicator G v := by
    intro v hv
    by_cases hvV : v ∈ Ioi V
    · rw [indicator_of_mem hvV]
      have h1 : Real.smoothTransition (v - 1) ^ 2 ≤ 1 :=
        pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
      have h2 : (1 - criticalUpperCutoff (v / V)) ^ 2 ≤ 1 :=
        pow_le_one₀ (by linarith [criticalUpperCutoff_le_one (v / V)])
          (by linarith [criticalUpperCutoff_nonneg (v / V)])
      simp only [G]
      gcongr
      calc Real.smoothTransition (v - 1) ^ 2 * (1 - criticalUpperCutoff (v / V)) ^ 2 * R v ^ 2 ≤
            1 * 1 * R v ^ 2 := by gcongr
        _ = R v ^ 2 := by ring
    · rw [indicator_of_notMem hvV]
      have : criticalUpperCutoff (v / V) = 1 :=
        criticalUpperCutoff_eq_one (by rw [div_le_one hV0]; exact not_lt.mp hvV)
      rw [this, sub_self]; simp
  rw [integral_criticalTruncationTail_sq_eq]
  calc (∫ v in Ioi 1, Real.smoothTransition (v - 1) ^ 2 * (1 - criticalUpperCutoff (v / V)) ^ 2 *
        R v ^ 2 / v ^ 2) ≤ ∫ v in Ioi 1, (Ioi V).indicator G v := by
        refine setIntegral_mono_on ?_ ((hGint.integrable_indicator measurableSet_Ioi).integrableOn)
          measurableSet_Ioi hpt
        refine ((hGint.integrable_indicator measurableSet_Ioi).integrableOn).mono' ?_ ?_
        · exact ((((by fun_prop : Continuous fun v => Real.smoothTransition (v - 1) ^ 2).mul
            ((continuous_const.sub (continuous_criticalUpperCutoff.comp (continuous_id.div_const V))).pow 2)).mul
            (by
              have h := continuous_factorialPhaseCombination S (fun n => (b n : ℂ))
              exact ((Complex.continuous_re.comp h).congr fun v =>
                factorialPhaseCombination_re_eq S b v).pow 2 : Continuous fun v => R v ^ 2)).aestronglyMeasurable.div₀
            (measurable_id.pow_const 2).aestronglyMeasurable)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact hpt v hv
    _ = ∫ v in Ioi V, G v := by
        rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi hV)]
    _ ≤ V⁻¹ * (criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2) := by
        rw [hsubst]; gcongr
    _ = criticalCollarMassUpper / V * ∑ n ∈ S, b n ^ 2 := by ring

/-- Truncation threshold `V₀ = max(2 + L, 8U/A_c)`. -/
def criticalTruncationThreshold : ℝ :=
  max (2 + factorialWindowLength) (8 * criticalCollarMassUpper / criticalCollarMassLower)

/-- Slope `e^{-1/2} A_c/4` of the truncated logarithmic law. -/
def criticalTruncatedArchLogSlope : ℝ := Real.exp (-(1 / 2 : ℝ)) * (criticalCollarMassLower / 4)

/-- Offset `3 + log(1/η(A_c/2, D_c))` of the truncated logarithmic law. -/
def criticalTruncatedArchLogOffset : ℝ :=
  3 + Real.log (1 / lowFreqRelativeCutoff (criticalCollarMassLower / 2) criticalCollarLowFreqConstant)

theorem criticalTruncatedArchLogSlope_pos : 0 < criticalTruncatedArchLogSlope := by
  unfold criticalTruncatedArchLogSlope
  have := criticalCollarMassLower_pos
  positivity

/-- **Truncated archimedean log-coercivity.** For every family on scales `n + 1 ≥ M ≥ 2`, every
`V ≥ V₀` and every real coefficient vector, `Lévy(g^V) ≥ s_T (log M - c_T) ∑ b_n²`. The low band of
`g^V` is that of the collared source up to the far layer, whose mass is `O(1/V)`. -/
theorem ofReal_le_criticalTruncatedLevyEnergy (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ n ∈ S, M ≤ n + 1) {V : ℝ} (hV : criticalTruncationThreshold ≤ V) :
    ENNReal.ofReal (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) *
      ∑ n ∈ S, b n ^ 2) ≤ sourceLevyEnergy (criticalTruncatedSource V S b) := by
  set A := criticalCollarMassLower
  set D := criticalCollarLowFreqConstant
  set U := criticalCollarMassUpper
  set η := lowFreqRelativeCutoff (A / 2) D
  set E := ∑ n ∈ S, b n ^ 2
  set g := criticalTruncatedSource V S b
  have hA : 0 < A := criticalCollarMassLower_pos
  have hD : 0 < D := criticalCollarLowFreqConstant_pos
  have hη : 0 < η := lowFreqRelativeCutoff_pos (by positivity) hD
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hU : 0 ≤ U := by unfold U criticalCollarMassUpper; have := factorialUnitIntervalUpper_pos; positivity
  have hL := factorialWindowLength_pos
  have hV1 : 2 + factorialWindowLength ≤ V := (le_max_left _ _).trans hV
  have hV2 : 8 * U / A ≤ V := (le_max_right _ _).trans hV
  have hVpos : 0 < V := by linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set R := η * M
  have hRpos : 0 < R := mul_pos hη hMpos
  have hlogR : Real.log M - criticalTruncatedArchLogOffset = Real.log R - 3 := by
    unfold criticalTruncatedArchLogOffset
    rw [Real.log_mul hη.ne' hMpos.ne', one_div, Real.log_inv]; ring
  rw [hlogR]
  have hs : 0 < criticalTruncatedArchLogSlope := criticalTruncatedArchLogSlope_pos
  rcases le_or_gt (Real.log R - 3) 0 with hneg | hpos
  · rw [ENNReal.ofReal_of_nonpos]
    · exact zero_le
    · have : criticalTruncatedArchLogSlope * (Real.log R - 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs.le hneg
      nlinarith
  have hR1 : 1 ≤ R := by
    by_contra h
    have := Real.log_nonpos hRpos.le (not_le.mp h).le
    linarith
  have hg := admissibleSource_criticalTruncatedSource V S b
  have hgc := admissibleSource_criticalCollaredSource S b
  have hh := admissibleSource_criticalTruncationTail V S b
  have hhigh := sourceLevyEnergy_ge_highBand hg hR1
  have hmi := integrable_levySourceSpectralDensity hg
  have hhi := integrable_levySourceSpectralDensity hh
  -- the spectrum of `g^V` is that of the collared source minus that of the far layer
  have hsplit : ∀ t, levySourceSpectralDensity g t ≤
      2 * levySourceSpectralDensity (criticalCollaredSource S b) t +
        2 * levySourceSpectralDensity (criticalTruncationTail V S b) t := by
    intro t
    have hfun : (fun x => (g x : ℂ)) = (fun x => (criticalCollaredSource S b x : ℂ)) +
        (-1 : ℂ) • fun x => (criticalTruncationTail V S b x : ℂ) := by
      funext x
      have := criticalTruncatedSource_add_tail V S b x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, g]
      rw [← this]; push_cast; ring
    unfold levySourceSpectralDensity
    rw [hfun, RHTower.WeilSpectral.paperFT_add_smul_real hgc.1 hh.1, neg_one_mul, ← sub_eq_add_neg]
    have := norm_sub_le (paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t)
      (paperFT (fun x => (criticalTruncationTail V S b x : ℂ)) t)
    nlinarith [norm_nonneg (paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t -
      paperFT (fun x => (criticalTruncationTail V S b x : ℂ)) t),
      sq_nonneg (‖paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t‖ -
        ‖paperFT (fun x => (criticalTruncationTail V S b x : ℂ)) t‖),
      norm_nonneg (paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t),
      norm_nonneg (paperFT (fun x => (criticalTruncationTail V S b x : ℂ)) t)]
  have hlowc : ∀ t ∈ Icc (-R) R, levySourceSpectralDensity (criticalCollaredSource S b) t ≤
      2 * D ^ 2 / M * E := by
    intro t ht
    refine norm_sq_paperFT_criticalCollaredSource_le S b hM hS ?_
    have hηπ : η ≤ Real.pi := (min_le_right _ _).trans (min_le_left _ _)
    calc |t| ≤ R := abs_le.mpr ht
      _ ≤ Real.pi * M := mul_le_mul_of_nonneg_right hηπ hMpos.le
  have htail := integral_criticalTruncationTail_sq_le (V := V) (by linarith) S b
  have hhtot := integral_levySourceSpectralDensity hh
  have hhnn : ∀ t, 0 ≤ levySourceSpectralDensity (criticalTruncationTail V S b) t := fun t => sq_nonneg _
  have hlow : 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g t ≤
      A / 2 * E + 2 * (U / V * E) := by
    have h1 : (∫ t in Icc (-R) R, levySourceSpectralDensity g t) ≤
        ∫ t in Icc (-R) R, (2 * (2 * D ^ 2 / M * E) +
          2 * levySourceSpectralDensity (criticalTruncationTail V S b) t) :=
      setIntegral_mono_on hmi.integrableOn ((integrableOn_const (by simp)).add
        (hhi.integrableOn.const_mul 2)) measurableSet_Icc fun t ht => (hsplit t).trans
          (by gcongr; exact hlowc t ht)
    have h2 : (∫ t in Icc (-R) R, (2 * (2 * D ^ 2 / M * E) +
        2 * levySourceSpectralDensity (criticalTruncationTail V S b) t)) ≤
        (2 * R) * (2 * (2 * D ^ 2 / M * E)) +
          2 * (2 * Real.pi * ∫ x, criticalTruncationTail V S b x ^ 2) := by
      have hc : IntegrableOn (fun _ : ℝ => 2 * (2 * D ^ 2 / M * E)) (Icc (-R) R) :=
        integrableOn_const (by simp)
      rw [integral_add hc (hhi.integrableOn.const_mul 2), setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, integral_const_mul, ← hhtot]
      rw [show R - -R = 2 * R by ring]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hhi (Eventually.of_forall hhnn)) (by norm_num))
    have hpi : 0 < Real.pi := Real.pi_pos
    have h3 : 1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E)) ≤ (A / 2) / 2 * E := by
      have := low_band_plancherel_energy_le_half_arch (A := A / 2) hD hE hM
      calc 1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E)) =
            (1 / (2 * Real.pi)) * (2 * η * (M : ℝ)) * (2 * D ^ 2 * E / (M : ℝ)) := by ring
        _ ≤ _ := this
    calc 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g t ≤
          1 / (2 * Real.pi) * ((2 * R) * (2 * (2 * D ^ 2 / M * E)) +
            2 * (2 * Real.pi * ∫ x, criticalTruncationTail V S b x ^ 2)) := by
          gcongr; exact h1.trans h2
      _ = 2 * (1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E))) +
            2 * ∫ x, criticalTruncationTail V S b x ^ 2 := by field_simp
      _ ≤ 2 * ((A / 2) / 2 * E) + 2 * (U / V * E) := by gcongr
      _ = A / 2 * E + 2 * (U / V * E) := by ring
  have hUV : 2 * (U / V * E) ≤ A / 4 * E := by
    have : U / V ≤ A / 8 := by
      rw [div_le_iff₀ hVpos]
      have := (div_le_iff₀ hA).mp hV2
      linarith
    nlinarith
  have hmass := integral_criticalTruncatedSource_sq_ge hV1 S b
  have htot := integral_levySourceSpectralDensity hg
  have hsplit2 := integral_add_compl (measurableSet_Icc (a := -R) (b := R)) hmi
  have hhighmass : A / 4 * E ≤ 1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, levySourceSpectralDensity g t := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : 1 / (2 * Real.pi) * ∫ t, levySourceSpectralDensity g t = ∫ y, g y ^ 2 := by
      rw [htot]; field_simp; rfl
    rw [← hsplit2, mul_add] at h1
    linarith
  refine le_trans ?_ hhigh
  have hc0 : 0 ≤ Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3) := by positivity
  rw [show criticalTruncatedArchLogSlope * (Real.log R - 3) * E =
      (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3)) * (A / 4 * E) by
      unfold criticalTruncatedArchLogSlope; ring, ENNReal.ofReal_mul hc0]
  gcongr

/-! ### Gamma and polar channels of doubly collared sources -/

/-- **Truncated mass ceiling.** `ac^V(0) = ∫ (g^V)² ≤ U ∑ b_n²`. -/
theorem sourceAutocorrelation_criticalTruncatedSource_zero_le (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    sourceAutocorrelation (criticalTruncatedSource V S b) 0 ≤ criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by
  have hsq (g : ℝ → ℝ) : sourceAutocorrelation g 0 = ∫ y, g y ^ 2 := by
    unfold sourceAutocorrelation; simp only [sub_zero, sq]
  have hgc := admissibleSource_criticalCollaredSource S b
  have hint : Integrable fun y => criticalCollaredSource S b y ^ 2 := by
    have := (memLp_two_iff_integrable_sq_norm hgc.1.aestronglyMeasurable).mp hgc.2
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using this
  rw [hsq]
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) hint
    (Eventually.of_forall fun y => ?_)) ?_
  · simp only [criticalTruncatedSource]
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _)
      (pow_le_one₀ (criticalUpperCutoff_nonneg _) (criticalUpperCutoff_le_one _))
  · rw [← hsq]; exact sourceAutocorrelation_criticalCollaredSource_zero_le S b

/-- **Integration by parts against the bounded primitive.** If `w` is differentiable on `[1, ∞)`,
vanishes at `1` and at infinity, and `w, w'` are integrable on `(1, ∞)`, then
`|∫_{v>1} w(v) B_b(v) dv| ≤ ‖w'‖₁ · 12 ∑ |b_n|/(n+1)`. -/
theorem abs_integral_weight_mul_phase_le {w w' : ℝ → ℝ} (hw : ∀ v ∈ Ici (1 : ℝ), HasDerivAt w (w' v) v)
    (hw1 : w 1 = 0) (hwt : Tendsto w atTop (𝓝 0)) (hwi : IntegrableOn w (Ioi 1))
    (hwi' : IntegrableOn w' (Ioi 1)) (S : Finset ℕ) (b : ℕ → ℝ) :
    |∫ v in Ioi 1, w v * (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re| ≤
      (∫ v in Ioi 1, |w' v|) * (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) := by
  set G := criticalFactorialPhasePrimitive S b
  set P := 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hGb (v : ℝ) : |G v| ≤ P := criticalFactorialPhasePrimitive_bound S b v
  have hP : 0 ≤ P := (abs_nonneg _).trans (hGb 0)
  set F : ℝ → ℝ := fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re
  have hFc : Continuous F := Complex.continuous_re.comp (continuous_factorialPhaseCombination _ _)
  have hFb (v : ℝ) : ‖F v‖ ≤ 2 * ∑ n ∈ S, |b n| := by
    have h := (Complex.abs_re_le_norm _).trans
      (norm_factorialPhaseCombination_le S (fun n => (b n : ℂ)) v)
    simpa [Complex.norm_real] using h
  have hGc : ContinuousOn G (Ioi 0) := fun x hx =>
    (criticalFactorialPhasePrimitive_hasDerivAt S b hx).continuousAt.continuousWithinAt
  have hint1 : IntegrableOn (w * F) (Ioi 1) :=
    hwi.mul_bdd hFc.aestronglyMeasurable (Eventually.of_forall hFb)
  have hint2 : IntegrableOn (w' * G) (Ioi 1) :=
    hwi'.mul_bdd ((hGc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hGb v)
  have hlim1 : Tendsto (w * G) (𝓝[>] 1) (𝓝 0) := by
    have h := ((hw 1 self_mem_Ici).continuousAt.mul
      (criticalFactorialPhasePrimitive_hasDerivAt S b one_pos).continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    have h0 : (w * G) 1 = 0 := by simp [hw1]
    rwa [h0] at h
  have hlim2 : Tendsto (w * G) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun v => ?_) (by simpa using hwt.norm.mul_const P)
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs (G v)]
    exact mul_le_mul_of_nonneg_left (hGb v) (norm_nonneg _)
  have e := integral_Ioi_mul_deriv_eq_deriv_mul (u := w) (v := G) (u' := w') (v' := F) (a' := 0) (b' := 0)
    (fun x hx => hw x (Ioi_subset_Ici_self hx))
    (fun x hx => criticalFactorialPhasePrimitive_hasDerivAt S b (lt_trans one_pos hx))
    hint1 hint2 hlim1 hlim2
  change |∫ v in Ioi 1, w v * F v| ≤ _
  rw [e, sub_self, zero_sub, abs_neg, ← integral_mul_const]
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hint2.abs
    (hwi'.abs.mul_const P) measurableSet_Ioi fun v _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hGb v) (abs_nonneg _)

/-- Upper polar readout `∫ g^V(x) e^{x/2} dx` of a doubly collared source. -/
def criticalTruncatedPolarReadout (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∫ x, criticalTruncatedSource V S b x * Real.exp (x / 2)

/-- Lower polar readout `∫ g^V(x) e^{-x/2} dx` of a doubly collared source. -/
def criticalTruncatedPolarEndpoint (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∫ x, criticalTruncatedSource V S b x * Real.exp (-(x / 2))

/-- Endpoint weight of the truncated lower readout `ρ(v) χ(v/V)`, `ρ = σ(v - 1)/v`. -/
def criticalTruncatedEndpointWeight (V v : ℝ) : ℝ :=
  criticalCollarEndpointWeight v * criticalUpperCutoff (1 / V * v)

private theorem truncated_readout_eq {V : ℝ} (S : Finset ℕ) (b : ℕ → ℝ) :
    criticalTruncatedPolarReadout V S b = ∫ v in Ioi 1, criticalTruncatedWeight (1 / V) v *
      (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re := by
  set F : ℝ → ℝ := fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re
  have hpt : ∀ x, criticalTruncatedSource V S b x * Real.exp (x / 2) = (Iic (0 : ℝ)).indicator
      (fun x => Real.exp x * (Real.smoothTransition (Real.exp (-x) - 1) *
        criticalUpperCutoff (Real.exp (-x) / V) * F (Real.exp (-x)))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx), criticalTruncatedSource, collared_source_eq hx]
      have : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by rw [← Real.exp_add]; ring_nf
      rw [← this]
      simp only [F, factorialPhaseCombination_re_eq]
      ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), criticalTruncatedSource,
        collared_source_pos (not_le.mp hx)]
      ring
  unfold criticalTruncatedPolarReadout
  rw [funext hpt, integral_indicator measurableSet_Iic,
    integral_Iic_zero_exp_mul_comp_exp_neg (fun v => Real.smoothTransition (v - 1) *
      criticalUpperCutoff (v / V) * F v)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [criticalTruncatedWeight, criticalCollarWeight, F]
  rw [show 1 / V * v = v / V by ring]
  ring

private theorem truncated_endpoint_eq {V : ℝ} (S : Finset ℕ) (b : ℕ → ℝ) :
    criticalTruncatedPolarEndpoint V S b = ∫ v in Ioi 1, criticalTruncatedEndpointWeight V v *
      (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re := by
  set F : ℝ → ℝ := fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re
  have hpt : ∀ x, criticalTruncatedSource V S b x * Real.exp (-(x / 2)) = (Iic (0 : ℝ)).indicator
      (fun x => Real.smoothTransition (Real.exp (-x) - 1) * criticalUpperCutoff (Real.exp (-x) / V) *
        F (Real.exp (-x))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx), criticalTruncatedSource, collared_source_eq hx]
      have : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by rw [← Real.exp_add]; simp
      simp only [F, factorialPhaseCombination_re_eq]
      calc _ = criticalUpperCutoff (Real.exp (-x) / V) * Real.smoothTransition (Real.exp (-x) - 1) *
            realPhaseCombination S b (Real.exp (-x)) * (Real.exp (x / 2) * Real.exp (-(x / 2))) := by ring
        _ = _ := by rw [this]; ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx), criticalTruncatedSource,
        collared_source_pos (not_le.mp hx)]
      ring
  unfold criticalTruncatedPolarEndpoint
  rw [funext hpt, integral_indicator measurableSet_Iic,
    integral_Iic_zero_comp_exp_neg (fun v => Real.smoothTransition (v - 1) *
      criticalUpperCutoff (v / V) * F v)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [criticalTruncatedEndpointWeight, criticalCollarEndpointWeight, F]
  rw [show 1 / V * v = v / V by ring]
  ring

/-- Refined scaled slope on `v > 0`: `|λ σ'(λv - 1)| ≤ 2 sup|σ'|/v`, since it vanishes unless `λ < 2/v`. -/
theorem abs_mul_deriv_smoothTransition_le_div {lam v : ℝ} (hl : 0 ≤ lam) (hv : 0 < v) :
    |lam * deriv Real.smoothTransition (lam * v - 1)| ≤ 2 * smoothTransitionSlope / v := by
  by_cases h : lam * v - 1 ∈ Ioo (0 : ℝ) 1
  · have hl2 : lam ≤ 2 / v := by rw [le_div_iff₀ hv]; linarith [h.2]
    rw [abs_mul, abs_of_nonneg hl]
    calc lam * |deriv Real.smoothTransition (lam * v - 1)| ≤ 2 / v * smoothTransitionSlope :=
          mul_le_mul hl2 (abs_deriv_smoothTransition_le _) (abs_nonneg _) (by positivity)
      _ = 2 * smoothTransitionSlope / v := by ring
  · rw [deriv_smoothTransition_eq_zero h, mul_zero, abs_zero]
    have := smoothTransitionSlope_nonneg; positivity

/-- Derivative of the truncated endpoint weight. -/
def criticalTruncatedEndpointWeightDeriv (V v : ℝ) : ℝ :=
  deriv criticalCollarEndpointWeight v * criticalUpperCutoff (1 / V * v) +
    criticalCollarEndpointWeight v * -(1 / V * deriv Real.smoothTransition (1 / V * v - 1))

private theorem abs_criticalCollarEndpointWeight_le {v : ℝ} (hv : 0 < v) :
    |criticalCollarEndpointWeight v| ≤ 1 / v := by
  rw [criticalCollarEndpointWeight, abs_div, abs_of_pos hv,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact div_le_div_of_nonneg_right (Real.smoothTransition.le_one _) hv.le

private theorem endpoint_weight_props {V : ℝ} (hV : 1 ≤ V) :
    (∀ v ∈ Ici (1 : ℝ), HasDerivAt (criticalTruncatedEndpointWeight V)
      (criticalTruncatedEndpointWeightDeriv V v) v) ∧
    criticalTruncatedEndpointWeight V 1 = 0 ∧
    Tendsto (criticalTruncatedEndpointWeight V) atTop (𝓝 0) ∧
    IntegrableOn (criticalTruncatedEndpointWeight V) (Ioi 1) ∧
    IntegrableOn (criticalTruncatedEndpointWeightDeriv V) (Ioi 1) ∧
    (∫ v in Ioi 1, |criticalTruncatedEndpointWeightDeriv V v|) ≤
      (∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v|) + 2 * smoothTransitionSlope := by
  have hV0 : 0 < V := by linarith
  have hl : 0 ≤ 1 / V := by positivity
  have hc : Continuous (criticalTruncatedEndpointWeight V) :=
    contDiff_criticalCollarEndpointWeight.continuous.mul
      (continuous_criticalUpperCutoff.comp (continuous_const.mul continuous_id))
  have hc' : Continuous (criticalTruncatedEndpointWeightDeriv V) := by
    unfold criticalTruncatedEndpointWeightDeriv
    exact ((contDiff_infty_iff_deriv.mp contDiff_criticalCollarEndpointWeight).2.continuous.mul
      (continuous_criticalUpperCutoff.comp (continuous_const.mul continuous_id))).add
      (contDiff_criticalCollarEndpointWeight.continuous.mul (continuous_const.mul
        (contDiff_deriv_smoothTransition.continuous.comp
          ((continuous_const.mul continuous_id).sub continuous_const))).neg)
  have hzero {v : ℝ} (hv : 2 * V ≤ v) : criticalTruncatedEndpointWeight V v = 0 := by
    rw [criticalTruncatedEndpointWeight, criticalUpperCutoff_eq_zero, mul_zero]
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hV0]; linarith
  have hw2 : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hbd' : ∀ v ∈ Ioi (1 : ℝ), |criticalTruncatedEndpointWeightDeriv V v| ≤
      |deriv criticalCollarEndpointWeight v| + 2 * smoothTransitionSlope * v ^ (-2 : ℝ) := by
    intro v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    unfold criticalTruncatedEndpointWeightDeriv
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (by rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _)
    · rw [abs_mul, abs_neg]
      have h1 := abs_criticalCollarEndpointWeight_le hv0
      have h2 := abs_mul_deriv_smoothTransition_le_div hl hv0
      have hsl := smoothTransitionSlope_nonneg
      calc |criticalCollarEndpointWeight v| * |1 / V * deriv Real.smoothTransition (1 / V * v - 1)| ≤
            1 / v * (2 * smoothTransitionSlope / v) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 2 * smoothTransitionSlope * v ^ (-2 : ℝ) := by
            rw [Real.rpow_neg hv0.le, Real.rpow_two]; field_simp
  have hi' : IntegrableOn (criticalTruncatedEndpointWeightDeriv V) (Ioi 1) := by
    refine (integrableOn_deriv_criticalCollarEndpointWeight.abs.add
      (hw2.const_mul (2 * smoothTransitionSlope))).mono' hc'.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs]; exact hbd' v hv
  refine ⟨fun v _ => ?_, ?_, ?_, ?_, hi', ?_⟩
  · exact ((hasDerivAt_criticalCollarEndpointWeight v).mul (hasDerivAt_cutoff_scale (1 / V) v)).congr_deriv
      (by unfold criticalTruncatedEndpointWeightDeriv; ring)
  · rw [criticalTruncatedEndpointWeight, criticalCollarEndpointWeight_eq_zero le_rfl, zero_mul]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (2 * V)] with v hv
    exact (hzero hv).symm
  · refine (hw2.const_mul (2 * V)).mono' hc.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    rw [Real.norm_eq_abs, Real.rpow_neg hv0.le, Real.rpow_two]
    rcases le_or_gt (2 * V) v with h | h
    · rw [hzero h, abs_zero]; positivity
    · rw [criticalTruncatedEndpointWeight, abs_mul]
      have h1 := abs_criticalCollarEndpointWeight_le hv0
      have h2 : |criticalUpperCutoff (1 / V * v)| ≤ 1 := by
        rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _
      calc |criticalCollarEndpointWeight v| * |criticalUpperCutoff (1 / V * v)| ≤ 1 / v * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ 2 * V * (v ^ 2)⁻¹ := by
            rw [mul_one, one_div, show (v ^ 2)⁻¹ = v⁻¹ * v⁻¹ by rw [sq, mul_inv]]
            have : 1 ≤ 2 * V * v⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ hv0]; linarith
            nlinarith [inv_pos.mpr hv0]
  · have hint2 : (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ)) = 1 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]; norm_num
    calc (∫ v in Ioi 1, |criticalTruncatedEndpointWeightDeriv V v|) ≤
          ∫ v in Ioi 1, (|deriv criticalCollarEndpointWeight v| + 2 * smoothTransitionSlope * v ^ (-2 : ℝ)) :=
          setIntegral_mono_on hi'.abs (integrableOn_deriv_criticalCollarEndpointWeight.abs.add
            (hw2.const_mul _)) measurableSet_Ioi hbd'
      _ = (∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v|) + 2 * smoothTransitionSlope := by
          rw [integral_add integrableOn_deriv_criticalCollarEndpointWeight.abs (hw2.const_mul _),
            integral_const_mul, hint2, mul_one]

/-- Readout constant `‖ψ'‖₁ + 2 sup|σ'| ‖ψ‖₁` of truncated upper readouts. -/
def criticalTruncatedReadoutConstant : ℝ :=
  (∫ v in Ioi 1, |deriv criticalCollarWeight v|) + 2 * smoothTransitionSlope * criticalCollarMass

/-- Endpoint constant `‖ρ'‖₁ + 2 sup|σ'|` of truncated lower readouts. -/
def criticalTruncatedEndpointConstant : ℝ :=
  (∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v|) + 2 * smoothTransitionSlope

theorem abs_criticalTruncatedPolarReadout_le {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) :
    |criticalTruncatedPolarReadout V S b| ≤
      criticalTruncatedReadoutConstant * (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) := by
  have hl : 0 ≤ 1 / V := by positivity
  rw [truncated_readout_eq]
  have ht : Tendsto (criticalTruncatedWeight (1 / V)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (g := fun v => |criticalCollarWeight v|) (fun _ => norm_nonneg _) (fun v => by
      rw [Real.norm_eq_abs]; exact abs_criticalTruncatedWeight_le _ v)
      (by simpa using tendsto_criticalCollarWeight_atTop.abs)
  have h := abs_integral_weight_mul_phase_le (w := criticalTruncatedWeight (1 / V))
    (w' := criticalTruncatedWeightDeriv (1 / V)) (fun v _ => hasDerivAt_criticalTruncatedWeight _ v)
    (by rw [criticalTruncatedWeight, criticalCollarWeight_eq_zero le_rfl, zero_mul]) ht
    (integrableOn_criticalTruncatedWeight _) (integrableOn_criticalTruncatedWeightDeriv hl) S b
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  unfold criticalTruncatedReadoutConstant criticalCollarMass
  calc (∫ v in Ioi 1, |criticalTruncatedWeightDeriv (1 / V) v|) ≤
        ∫ v in Ioi 1, (|deriv criticalCollarWeight v| + 2 * smoothTransitionSlope * |criticalCollarWeight v|) :=
        setIntegral_mono_on (integrableOn_criticalTruncatedWeightDeriv hl).abs
          (integrableOn_deriv_criticalCollarWeight.abs.add
            (integrableOn_criticalCollarWeight.abs.const_mul _)) measurableSet_Ioi
          fun v hv => abs_criticalTruncatedWeightDeriv_le hl (le_of_lt hv)
    _ = _ := by
        rw [integral_add integrableOn_deriv_criticalCollarWeight.abs
          (integrableOn_criticalCollarWeight.abs.const_mul _), integral_const_mul]

theorem abs_criticalTruncatedPolarEndpoint_le {V : ℝ} (hV : 1 ≤ V) (S : Finset ℕ) (b : ℕ → ℝ) :
    |criticalTruncatedPolarEndpoint V S b| ≤
      criticalTruncatedEndpointConstant * (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨hd, h1, ht, hi, hi', hint⟩ := endpoint_weight_props hV
  rw [truncated_endpoint_eq]
  exact (abs_integral_weight_mul_phase_le hd h1 ht hi hi' S b).trans
    (mul_le_mul_of_nonneg_right hint (by positivity))

/-! ### The complete energy of doubly collared sources -/

/-- **Complete energy of a doubly collared source** in Gamma–Lévy form:
`Lévy(g^V) + Ω(0) ac^V(0) + 2 R^V E^V - 2 P^V`. -/
def criticalTruncatedCompleteEnergy (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : EReal :=
  (sourceLevyEnergy (criticalTruncatedSource V S b) : EReal) +
    ((EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V S b) 0 +
      2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) -
      2 * criticalTruncatedPrimeEnergy V S b : ℝ) : EReal)

/-- Channel constant `K_T = |Ω(0)| U + 288 a_R a_E + 2 C_T`, independent of `V`. -/
def criticalTruncatedChannelConstant : ℝ :=
  |EF.gammaBracket 0| * criticalCollarMassUpper +
    288 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant +
    2 * criticalTruncatedPrimeConstant

theorem neg_le_criticalTruncatedChannels (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : DyadicScaleBlock S M) {V : ℝ} (hV : 1 ≤ V) :
    -(criticalTruncatedChannelConstant * ∑ n ∈ S, b n ^ 2) ≤
      EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V S b) 0 +
        2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) -
        2 * criticalTruncatedPrimeEnergy V S b := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hT : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  have hV0 : 0 < V := by linarith
  have hM0 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  set ac := sourceAutocorrelation (criticalTruncatedSource V S b) 0
  have hac0 : 0 ≤ ac := by
    unfold ac sourceAutocorrelation
    exact integral_nonneg fun y => by simp only [sub_zero]; exact mul_self_nonneg _
  have hac := sourceAutocorrelation_criticalTruncatedSource_zero_le V S b
  have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤ EF.gammaBracket 0 * ac := by
    have h1 : -(|EF.gammaBracket 0| * ac) ≤ EF.gammaBracket 0 * ac := by
      have := neg_abs_le (EF.gammaBracket 0 * ac)
      rwa [abs_mul, abs_of_nonneg hac0] at this
    have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (criticalCollarMassUpper * E) :=
      mul_le_mul_of_nonneg_left hac (abs_nonneg _)
    linarith
  have hT2 := sq_sum_abs_div_succ_le S b hM fun n hn => (hS n hn).1
  set a := criticalTruncatedReadoutConstant
  set c := criticalTruncatedEndpointConstant
  have ha : 0 ≤ a := by
    unfold a criticalTruncatedReadoutConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    have : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hc : 0 ≤ c := by
    unfold c criticalTruncatedEndpointConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
      integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    positivity
  have hpol : |criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b| ≤ 144 * a * c * E := by
    rw [abs_mul]
    have h1 := abs_criticalTruncatedPolarReadout_le hV0 S b
    have h2 := abs_criticalTruncatedPolarEndpoint_le hV S b
    have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hTE : T ^ 2 ≤ E := hT2.trans (by
      have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
      nlinarith)
    calc _ ≤ a * (12 * T) * (c * (12 * T)) := h12
      _ = 144 * a * c * T ^ 2 := by ring
      _ ≤ 144 * a * c * E := mul_le_mul_of_nonneg_left hTE (by positivity)
  have hP := abs_criticalTruncatedPrimeEnergy_le hV0 (by omega) hS b
  have hP' := (abs_le.mp hP).2
  have hpol' := (abs_le.mp hpol).1
  unfold criticalTruncatedChannelConstant
  nlinarith

/-- **Complete energy of doubly collared sources on dyadic blocks.** For every dyadic block
`[M, 2M]` (`M ≥ 2`), every truncation `V ≥ V₀` and every real coefficient vector,
`E(g^V) ≥ (s_T (log M - c_T) - K_T) ∑ b_n²`, uniformly in `V`. -/
theorem criticalTruncatedCompleteEnergy_ge (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : DyadicScaleBlock S M) {V : ℝ} (hV : criticalTruncationThreshold ≤ V) :
    (((criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
        criticalTruncatedChannelConstant) * ∑ n ∈ S, b n ^ 2 : ℝ) : EReal) ≤
      criticalTruncatedCompleteEnergy V S b := by
  set E := ∑ n ∈ S, b n ^ 2
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  set X := criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalTruncatedSource V S b) : EReal) := by
    have h1 := ofReal_le_criticalTruncatedLevyEnergy S b hM (fun n hn => (hS n hn).1) hV
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hch := neg_le_criticalTruncatedChannels S b hM hS hV1
  unfold criticalTruncatedCompleteEnergy
  rw [show (criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedChannelConstant) * E = X + -(criticalTruncatedChannelConstant * E) by ring,
    EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Positive definiteness of doubly collared sources, uniformly in the truncation.** There is a
scale `M₀` such that for every `M ≥ M₀`, every truncation `V ≥ V₀`, every dyadic block at `M` and
every nonzero real coefficient vector, the complete energy of the compact source `g^V` is strictly
positive. -/
theorem exists_criticalTruncatedCompleteEnergy_pos :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ V : ℝ, criticalTruncationThreshold ≤ V → ∀ S : Finset ℕ,
      DyadicScaleBlock S M → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
        0 < criticalTruncatedCompleteEnergy V S b := by
  have hs := criticalTruncatedArchLogSlope_pos
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop
    (criticalTruncatedArchLogOffset + criticalTruncatedChannelConstant / criticalTruncatedArchLogSlope)).and
      (eventually_ge_atTop 2))
  refine ⟨M₀, fun M hM V hV S hS b hb => ?_⟩
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  obtain ⟨j, hj, hbj⟩ := hb
  have hE : 0 < ∑ n ∈ S, b n ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hgap : 0 < criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedChannelConstant := by
    have h1 : criticalTruncatedChannelConstant / criticalTruncatedArchLogSlope <
        Real.log M - criticalTruncatedArchLogOffset := by linarith
    have h2 := (div_lt_iff₀ hs).mp h1
    linarith
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap hE))
    (criticalTruncatedCompleteEnergy_ge S b hM2 hS hV)

end GaloisForLFunctions.ArithmeticPositivityTheory
