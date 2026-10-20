import GaloisForLFunctions.«arithmetic-positivity-theory».DyadicDilationCorrelationInequality
import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalCompleteFormGrowingPatterns

/-!
# The collared critical prime channel is bounded on `ℓ²`

The critical source `g_b(x) = 1_{x ≤ 0} e^{x/2} B_b(e^{-x})` has a jump at its endpoint `x = 0`.
In the dilation picture its prime atoms are `Λ(r) r^{-1} ∫_{v>1} v^{-2} B_b(v) B_b(rv) dv`, whose
weight `v^{-2} 1_{v>1}` has a cosine transform decaying only like `1/f`. That Hilbert-type tail is
why the known bound for the critical prime channel on a dyadic block is quadratic in `∑ |b_n|`.

The **collared critical source** `g_c(x) = σ(e^{-x} - 1) g_b(x)`, with `σ` the smooth
transition, removes the endpoint on `(-log 2, 0]` and leaves the source unchanged on
`x ≤ -log 2`. For `r ≥ 2` the collar of the dilated copy is inactive, and the correlation is
`r^{-1/2} ∫_{v>1} ψ(v) B_b(v) B_b(rv) dv` with the single smooth weight `ψ(v) = σ(v - 1)/v²`.
Since `ψ` vanishes to second order at `v = 1`, two integrations by parts give
`|F_ψ(f)| ≤ ‖ψ''‖₁/(4π² f²)`. The dyadic dilation inequality then bounds every prime atom by
`Λ(r) r^{-3/2} ∑ b_n²` up to an absolute factor.

Main result: on every dyadic scale block the collared critical prime energy is at most
`C_c ∑ b_n²`, with an absolute constant `C_c`, uniformly in the scale, in the number and
positions of the atoms, and in the real coefficients.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private theorem integrableOn_mul_of_abs_le_one {g ψ : ℝ → ℝ} {a : ℝ} (hg : IntegrableOn g (Ioi a))
    (hψ : Continuous ψ) (hψ1 : ∀ x, |ψ x| ≤ 1) : IntegrableOn (g * ψ) (Ioi a) := by
  refine (hg.norm).mono' (hg.aestronglyMeasurable.mul hψ.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hψ1 x)

/-- **Second-order cosine decay.** If `φ` vanishes to second order at `a` and `φ, φ', φ''` are
integrable with `φ, φ' → 0`, two integrations by parts give
`∫_{v>a} φ(v) cos(ωv) dv = -(1/ω²) ∫_{v>a} φ''(v) cos(ωv) dv`. -/
theorem integral_Ioi_mul_cos_eq_of_flat {φ φ' φ'' : ℝ → ℝ} {a : ℝ}
    (h1 : ∀ x ∈ Ici a, HasDerivAt φ (φ' x) x) (h2 : ∀ x ∈ Ici a, HasDerivAt φ' (φ'' x) x)
    (h0 : φ a = 0) (h0' : φ' a = 0) (hi : IntegrableOn φ (Ioi a)) (hi' : IntegrableOn φ' (Ioi a))
    (hi'' : IntegrableOn φ'' (Ioi a)) (ht : Tendsto φ atTop (𝓝 0)) (ht' : Tendsto φ' atTop (𝓝 0))
    {ω : ℝ} (hω : ω ≠ 0) :
    ∫ v in Ioi a, φ v * Real.cos (ω * v) = -(1 / ω ^ 2) * ∫ v in Ioi a, φ'' v * Real.cos (ω * v) := by
  have hsin (x : ℝ) : HasDerivAt (fun y => Real.sin (ω * y) / ω) (Real.cos (ω * x)) x := by
    exact ((((hasDerivAt_id' x).const_mul ω).sin).div_const ω).congr_deriv (by field_simp)
  have hcos (x : ℝ) : HasDerivAt (fun y => -Real.cos (ω * y) / ω) (Real.sin (ω * x)) x := by
    exact (((((hasDerivAt_id' x).const_mul ω).cos).neg).div_const ω).congr_deriv (by field_simp)
  have hS : ∀ x, |Real.sin (ω * x) / ω| ≤ 1 / |ω| := fun x => by
    rw [abs_div]; exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
  have hC : ∀ x, |-Real.cos (ω * x) / ω| ≤ 1 / |ω| := fun x => by
    rw [abs_div, abs_neg]; exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
  have hlim {g ψ : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0)) (hψ : ∀ x, |ψ x| ≤ 1 / |ω|) :
      Tendsto (g * ψ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) (by simpa using hg.norm.mul_const (1 / |ω|))
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((hψ x).trans_eq (one_div _)) (abs_nonneg _)
  have hzero {g ψ : ℝ → ℝ} (hg : ContinuousAt g a) (hψ : Continuous ψ) (hga : g a = 0) :
      Tendsto (g * ψ) (𝓝[>] a) (𝓝 0) := by
    have := (hg.mul hψ.continuousAt).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))
    simpa [hga] using this
  have hcs : Continuous fun y => Real.sin (ω * y) / ω := by fun_prop
  have hcc : Continuous fun y => -Real.cos (ω * y) / ω := by fun_prop
  -- first integration by parts
  have e1 := integral_Ioi_mul_deriv_eq_deriv_mul (u := φ) (u' := φ') (a' := 0) (b' := 0)
    (fun x hx => h1 x (Ioi_subset_Ici_self hx)) (fun x _ => hsin x)
    (integrableOn_mul_of_abs_le_one hi (by fun_prop) fun x => Real.abs_cos_le_one _)
    ((hi'.norm.const_mul (1 / |ω|)).mono' (hi'.aestronglyMeasurable.mul hcs.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        simp only [Pi.mul_apply, Real.norm_eq_abs, norm_mul]
        rw [mul_comm (1 / |ω|)]; exact mul_le_mul_of_nonneg_left (hS x) (abs_nonneg _)))
    (hzero (h1 a self_mem_Ici).continuousAt hcs h0) (hlim ht hS)
  -- second integration by parts
  have e2 := integral_Ioi_mul_deriv_eq_deriv_mul (u := φ') (u' := φ'') (a' := 0) (b' := 0)
    (fun x hx => h2 x (Ioi_subset_Ici_self hx)) (fun x _ => hcos x)
    (integrableOn_mul_of_abs_le_one hi' (by fun_prop) fun x => Real.abs_sin_le_one _)
    ((hi''.norm.const_mul (1 / |ω|)).mono' (hi''.aestronglyMeasurable.mul hcc.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        simp only [Pi.mul_apply, Real.norm_eq_abs, norm_mul]
        rw [mul_comm (1 / |ω|)]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)))
    (hzero (h2 a self_mem_Ici).continuousAt hcc h0') (hlim ht' hC)
  have e1' : ∫ v in Ioi a, φ v * Real.cos (ω * v) = -(1 / ω) * ∫ v in Ioi a, φ' v * Real.sin (ω * v) := by
    rw [e1, ← integral_const_mul]
    simp only [zero_sub, sub_zero]
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    ring
  have e2' : ∫ v in Ioi a, φ' v * Real.sin (ω * v) = (1 / ω) * ∫ v in Ioi a, φ'' v * Real.cos (ω * v) := by
    rw [e2, ← integral_const_mul]
    simp only [zero_sub, sub_zero]
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    ring
  rw [e1', e2']
  field_simp

/-- Absolute form of second-order cosine decay: `|∫ φ cos(ωv)| ≤ ‖φ''‖₁ / ω²`. -/
theorem abs_integral_Ioi_mul_cos_le_of_flat {φ φ' φ'' : ℝ → ℝ} {a : ℝ}
    (h1 : ∀ x ∈ Ici a, HasDerivAt φ (φ' x) x) (h2 : ∀ x ∈ Ici a, HasDerivAt φ' (φ'' x) x)
    (h0 : φ a = 0) (h0' : φ' a = 0) (hi : IntegrableOn φ (Ioi a)) (hi' : IntegrableOn φ' (Ioi a))
    (hi'' : IntegrableOn φ'' (Ioi a)) (ht : Tendsto φ atTop (𝓝 0)) (ht' : Tendsto φ' atTop (𝓝 0))
    {ω : ℝ} (hω : ω ≠ 0) :
    |∫ v in Ioi a, φ v * Real.cos (ω * v)| ≤ (∫ v in Ioi a, |φ'' v|) / ω ^ 2 := by
  rw [integral_Ioi_mul_cos_eq_of_flat h1 h2 h0 h0' hi hi' hi'' ht ht' hω, abs_mul, abs_neg,
    abs_of_pos (by positivity : 0 < 1 / ω ^ 2), one_div_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on ?_ hi''.abs measurableSet_Ioi
    fun v _ => ?_)
  · exact (integrableOn_mul_of_abs_le_one hi'' (by fun_prop : Continuous fun v =>
      Real.cos (ω * v)) fun v => Real.abs_cos_le_one _).abs
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- **Critical collar weight** `ψ(v) = σ(v - 1)/v²`, with `σ` the smooth transition: it vanishes
on `v ≤ 1`, equals `v⁻²` on `v ≥ 2`, and is smooth on `ℝ`. -/
def criticalCollarWeight (v : ℝ) : ℝ := Real.smoothTransition (v - 1) / v ^ 2

theorem criticalCollarWeight_eq_zero {x : ℝ} (hx : x ≤ 1) : criticalCollarWeight x = 0 := by
  rw [criticalCollarWeight, Real.smoothTransition.zero_of_nonpos (by linarith), zero_div]

theorem criticalCollarWeight_eq_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    criticalCollarWeight x = 1 * x ^ (-2 : ℤ) := by
  rw [criticalCollarWeight, Real.smoothTransition.one_of_one_le (by linarith), one_mul, zpow_neg,
    one_div]
  norm_cast

theorem contDiff_criticalCollarWeight : ContDiff ℝ (⊤ : ℕ∞) criticalCollarWeight := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  rcases lt_or_ge x 1 with hx | hx
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact criticalCollarWeight_eq_zero (le_of_lt hy)
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Real.smoothTransition (y - 1)) x :=
      (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ 2) x := (contDiff_id.pow 2).contDiffAt
    exact h1.div h2 (by positivity)

theorem contDiff_deriv_criticalCollarWeight : ContDiff ℝ (⊤ : ℕ∞) (deriv criticalCollarWeight) :=
  (contDiff_infty_iff_deriv.mp contDiff_criticalCollarWeight).2

theorem hasDerivAt_criticalCollarWeight (x : ℝ) :
    HasDerivAt criticalCollarWeight (deriv criticalCollarWeight x) x :=
  ((contDiff_infty_iff_deriv.mp contDiff_criticalCollarWeight).1 x).hasDerivAt

theorem hasDerivAt_deriv_criticalCollarWeight (x : ℝ) :
    HasDerivAt (deriv criticalCollarWeight) (deriv (deriv criticalCollarWeight) x) x :=
  ((contDiff_infty_iff_deriv.mp contDiff_deriv_criticalCollarWeight).1 x).hasDerivAt

/-- The collar is flat at the endpoint: `ψ' = 0` on `v ≤ 1`. -/
theorem deriv_criticalCollarWeight_eq_zero {x : ℝ} (hx : x ≤ 1) : deriv criticalCollarWeight x = 0 := by
  have hT : IsClosed {y | deriv criticalCollarWeight y = 0} :=
    isClosed_eq contDiff_deriv_criticalCollarWeight.continuous continuous_const
  have hI : Iio (1 : ℝ) ⊆ {y | deriv criticalCollarWeight y = 0} := fun y hy => by
    have : criticalCollarWeight =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact criticalCollarWeight_eq_zero (le_of_lt hz)
    simp only [mem_setOf_eq]
    rw [this.deriv_eq, deriv_const]
  have := (hT.closure_subset_iff.mpr hI)
  rw [closure_Iio' nonempty_Iio] at this
  exact this hx

theorem deriv_criticalCollarWeight_of_two_lt {x : ℝ} (hx : 2 < x) :
    deriv criticalCollarWeight x = -2 * x ^ (-3 : ℤ) := by
  have he : criticalCollarWeight =ᶠ[𝓝 x] fun y => y ^ (-2 : ℤ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [criticalCollarWeight_eq_of_two_le (le_of_lt hy), one_mul]
  rw [he.deriv_eq, (hasDerivAt_zpow (-2) x (Or.inl (by positivity))).deriv]
  norm_num

theorem deriv_deriv_criticalCollarWeight_of_two_lt {x : ℝ} (hx : 2 < x) :
    deriv (deriv criticalCollarWeight) x = 6 * x ^ (-4 : ℤ) := by
  have he : deriv criticalCollarWeight =ᶠ[𝓝 x] fun y => -2 * y ^ (-3 : ℤ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact deriv_criticalCollarWeight_of_two_lt hy
  rw [he.deriv_eq, ((hasDerivAt_zpow (-3) x (Or.inl (by positivity))).const_mul (-2)).deriv]
  norm_num
  ring

private theorem integrableOn_Ioi_one_of_eq_zpow {g : ℝ → ℝ} (hg : Continuous g) (m : ℤ) (hm : m < -1)
    (c : ℝ) (heq : ∀ x, 2 < x → g x = c * x ^ m) : IntegrableOn g (Ioi 1) := by
  rw [← Ioc_union_Ioi_eq_Ioi one_le_two]
  refine (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self).union ?_
  refine IntegrableOn.congr_fun (((integrableOn_Ioi_rpow_of_lt (a := (m : ℝ)) (by exact_mod_cast hm)
    two_pos).const_mul c)) (fun x hx => ?_) measurableSet_Ioi
  rw [heq x hx, Real.rpow_intCast]

theorem integrableOn_criticalCollarWeight : IntegrableOn criticalCollarWeight (Ioi 1) :=
  integrableOn_Ioi_one_of_eq_zpow contDiff_criticalCollarWeight.continuous (-2) (by norm_num) 1
    fun _ hx => criticalCollarWeight_eq_of_two_le (le_of_lt hx)

theorem integrableOn_deriv_criticalCollarWeight : IntegrableOn (deriv criticalCollarWeight) (Ioi 1) :=
  integrableOn_Ioi_one_of_eq_zpow contDiff_deriv_criticalCollarWeight.continuous (-3) (by norm_num) (-2)
    fun _ hx => deriv_criticalCollarWeight_of_two_lt hx

theorem integrableOn_deriv_deriv_criticalCollarWeight :
    IntegrableOn (deriv (deriv criticalCollarWeight)) (Ioi 1) :=
  integrableOn_Ioi_one_of_eq_zpow
    (contDiff_infty_iff_deriv.mp contDiff_deriv_criticalCollarWeight).2.continuous (-4) (by norm_num) 6
    fun _ hx => deriv_deriv_criticalCollarWeight_of_two_lt hx

theorem tendsto_criticalCollarWeight_atTop : Tendsto criticalCollarWeight atTop (𝓝 0) := by
  refine (tendsto_zpow_atTop_zero (n := -2) (by norm_num)).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [criticalCollarWeight_eq_of_two_le hx, one_mul]

theorem tendsto_deriv_criticalCollarWeight_atTop :
    Tendsto (deriv criticalCollarWeight) atTop (𝓝 0) := by
  have := (tendsto_zpow_atTop_zero (𝕜 := ℝ) (n := -3) (by norm_num)).const_mul (-2)
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 2] with x hx
  rw [deriv_criticalCollarWeight_of_two_lt hx]

/-- The collar's cosine transform is bounded by `‖ψ‖₁`. -/
theorem abs_integral_criticalCollarWeight_mul_cos_le (ω : ℝ) :
    |∫ v in Ioi 1, criticalCollarWeight v * Real.cos (ω * v)| ≤ ∫ v in Ioi 1, |criticalCollarWeight v| := by
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on ?_
    integrableOn_criticalCollarWeight.abs measurableSet_Ioi fun v _ => ?_)
  · exact (integrableOn_mul_of_abs_le_one integrableOn_criticalCollarWeight
      (by fun_prop : Continuous fun v => Real.cos (ω * v)) fun v => Real.abs_cos_le_one _).abs
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- **Second-order decay of the collar transform:** `|∫ ψ cos(ωv)| ≤ ‖ψ''‖₁/ω²`. -/
theorem abs_integral_criticalCollarWeight_mul_cos_le_div_sq {ω : ℝ} (hω : ω ≠ 0) :
    |∫ v in Ioi 1, criticalCollarWeight v * Real.cos (ω * v)| ≤
      (∫ v in Ioi 1, |deriv (deriv criticalCollarWeight) v|) / ω ^ 2 :=
  abs_integral_Ioi_mul_cos_le_of_flat (fun x _ => hasDerivAt_criticalCollarWeight x)
    (fun x _ => hasDerivAt_deriv_criticalCollarWeight x) (criticalCollarWeight_eq_zero le_rfl)
    (deriv_criticalCollarWeight_eq_zero le_rfl) integrableOn_criticalCollarWeight
    integrableOn_deriv_criticalCollarWeight integrableOn_deriv_deriv_criticalCollarWeight
    tendsto_criticalCollarWeight_atTop tendsto_deriv_criticalCollarWeight_atTop hω

/-! ### The collared critical source and its prime channel -/

/-- **Collared critical source** `g_c(x) = σ(e^{-x} - 1) g_b(x)`: the critical source with its
endpoint `x = 0` smoothly removed on `(-log 2, 0]`. -/
def criticalCollaredSource (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition (Real.exp (-x) - 1) * criticalFactorialSource S b x

theorem factorialPhaseCombination_re_eq (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re = realPhaseCombination S b v := by
  simp [factorialPhaseCombination, realPhaseCombination, Complex.re_sum, ← Complex.ofReal_mul]

/-- Clock change of variables `∫_{x ≤ 0} e^x H(e^{-x}) dx = ∫_1^∞ H(v)/v² dv`. -/
theorem integral_Iic_zero_exp_mul_comp_exp_neg (H : ℝ → ℝ) :
    (∫ x in Iic (0 : ℝ), Real.exp x * H (Real.exp (-x))) = ∫ v in Ioi (1 : ℝ), H v / v ^ 2 := by
  have h1 := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ => Real.exp (-y) * H (Real.exp y))
  simp only [neg_zero, neg_neg] at h1
  have h2 := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (fun v => H v / v ^ 2)
  rw [Real.image_exp_Ioi, Real.exp_zero] at h2
  rw [h2, h1]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [abs_of_pos (Real.exp_pos y), smul_eq_mul, Real.exp_neg]
  have := Real.exp_pos y
  field_simp

/-- **Collared dilation correlation.** For `r ≥ 2` the collar of the dilated copy is inactive and
`∫ g_c(x) g_c(x - log r) dx = r^{-1/2} ∫_{v>1} ψ(v) B_b(v) B_b(rv) dv`. -/
theorem integral_criticalCollaredSource_mul_dilate (S : Finset ℕ) (b : ℕ → ℝ) {r : ℕ} (hr : 2 ≤ r) :
    ∫ x, criticalCollaredSource S b x * criticalCollaredSource S b (x - Real.log r) =
      1 / Real.sqrt r * ∫ v in Ioi 1, criticalCollarWeight v *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v)) := by
  set R := realPhaseCombination S b
  have hr0 : (0 : ℝ) < r := by positivity
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hsrc {y : ℝ} (hy : y ≤ 0) : criticalFactorialSource S b y = Real.exp (y / 2) * R (Real.exp (-y)) := by
    simp only [criticalFactorialSource, indicator_of_mem (show y ∈ Iic 0 from hy),
      factorialPhaseCombination_re_eq, R]
  have hsqrt : Real.exp (Real.log r / 2) = Real.sqrt r := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr0]; ring_nf
  have hpt : ∀ x, criticalCollaredSource S b x * criticalCollaredSource S b (x - Real.log r) =
      (Iic (0 : ℝ)).indicator (fun x => 1 / Real.sqrt r * (Real.exp x *
        (Real.smoothTransition (Real.exp (-x) - 1) * (R (Real.exp (-x)) * R (r * Real.exp (-x)))))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx)]
      have hxr : x - Real.log r ≤ 0 := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ r)]
      have hexp : Real.exp (-(x - Real.log r)) = r * Real.exp (-x) := by
        rw [neg_sub, Real.exp_sub, Real.exp_log hr0, Real.exp_neg]; field_simp
      have hc : Real.smoothTransition (r * Real.exp (-x) - 1) = 1 := by
        refine Real.smoothTransition.one_of_one_le ?_
        have : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
        nlinarith
      have hhalf : Real.exp ((x - Real.log r) / 2) = Real.exp (x / 2) / Real.sqrt r := by
        rw [← hsqrt, ← Real.exp_sub]; ring_nf
      have hxx : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by rw [← Real.exp_add]; ring_nf
      unfold criticalCollaredSource
      rw [hsrc hx, hsrc hxr, hexp, hc, hhalf]
      have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
      field_simp
      rw [← hxx]; ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx)]
      simp only [criticalCollaredSource, criticalFactorialSource,
        indicator_of_notMem (show x ∉ Iic 0 from hx), mul_zero, zero_mul]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Iic, integral_const_mul,
    integral_Iic_zero_exp_mul_comp_exp_neg (fun v => Real.smoothTransition (v - 1) * (R v * R (r * v)))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [criticalCollarWeight]
  ring

/-- Prime atom `Λ(r)/√r · ∫ g_c(x) g_c(x - log r) dx` of the collared critical source. -/
def criticalCollaredPrimeAtom (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0) *
    ∫ x, criticalCollaredSource S b x * criticalCollaredSource S b (x - Real.log r)

/-- Prime channel `∑_r Λ(r)/√r · ac_c(log r)` of the collared critical source. -/
def criticalCollaredPrimeEnergy (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑' r : ℕ, criticalCollaredPrimeAtom S b r

/-- Uniform bound `‖ψ‖₁` of the collar's cosine transform. -/
def criticalCollarMass : ℝ := ∫ v in Ioi 1, |criticalCollarWeight v|

/-- Curvature constant `‖ψ''‖₁/(4π²)` of the collar's cosine transform. -/
def criticalCollarCurvature : ℝ :=
  (∫ v in Ioi 1, |deriv (deriv criticalCollarWeight) v|) / (4 * Real.pi ^ 2)

theorem criticalCollarCurvature_nonneg : 0 ≤ criticalCollarCurvature :=
  div_nonneg (integral_nonneg fun _ => abs_nonneg _) (by positivity)

theorem abs_weightCosineTransform_criticalCollarWeight_le (f : ℝ) :
    |weightCosineTransform criticalCollarWeight f| ≤ criticalCollarMass :=
  abs_integral_criticalCollarWeight_mul_cos_le (2 * Real.pi * f)

theorem abs_weightCosineTransform_criticalCollarWeight_le_div_sq {f : ℝ} (hf : f ≠ 0) :
    |weightCosineTransform criticalCollarWeight f| ≤ criticalCollarCurvature / f ^ 2 := by
  have h := abs_integral_criticalCollarWeight_mul_cos_le_div_sq
    (ω := 2 * Real.pi * f) (mul_ne_zero (by positivity) hf)
  refine h.trans (le_of_eq ?_)
  unfold criticalCollarCurvature
  field_simp
  ring

/-- The collared prime constant `(4/π⁴) K(‖ψ‖₁, ‖ψ''‖₁/4π²) ∑ Λ(r)/r^{3/2}`. -/
def criticalCollaredPrimeConstant : ℝ :=
  4 / Real.pi ^ 4 * dyadicDilationConstant criticalCollarMass criticalCollarCurvature *
    ∑' r : ℕ, envelopePrimeMajorant 1 r

private theorem abs_criticalCollaredPrimeAtom_le {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) (r : ℕ) :
    |criticalCollaredPrimeAtom S b r| ≤
      4 / Real.pi ^ 4 * dyadicDilationConstant criticalCollarMass criticalCollarCurvature *
        (∑ n ∈ S, b n ^ 2) * envelopePrimeMajorant 1 r := by
  unfold criticalCollaredPrimeAtom envelopePrimeMajorant
  split_ifs with hr
  · have hr0 : (0 : ℝ) < r := by positivity
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
    have hK := abs_integral_weight_realPhaseCombination_dilate_le integrableOn_criticalCollarWeight
      abs_weightCosineTransform_criticalCollarWeight_le
      (fun f hf => abs_weightCosineTransform_criticalCollarWeight_le_div_sq hf)
      criticalCollarCurvature_nonneg hM hS b (r := r) (by omega)
    rw [integral_criticalCollaredSource_mul_dilate S b hr, abs_mul, abs_mul,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le),
      abs_of_pos (by positivity : 0 < 1 / Real.sqrt r)]
    have hpow : (r : ℝ) ^ ((1 : ℝ) + 1 / 2) = Real.sqrt r * Real.sqrt r * Real.sqrt r := by
      rw [Real.rpow_add hr0, Real.rpow_one, ← Real.sqrt_eq_rpow, Real.mul_self_sqrt hr0.le]
    rw [hpow]
    have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := r))
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
          |∫ v in Ioi 1, criticalCollarWeight v * (realPhaseCombination S b v * realPhaseCombination S b (r * v))|)
        ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
          (4 / Real.pi ^ 4 * (dyadicDilationConstant criticalCollarMass criticalCollarCurvature / Real.sqrt r) *
            ∑ n ∈ S, b n ^ 2)) := by gcongr
      _ = _ := by field_simp
  · simp

/-- **ℓ²-uniform collared prime channel.** On every dyadic scale block `M ≤ n + 1 ≤ 2M` and for
every real coefficient vector, the collared critical prime energy is at most
`C_c ∑ b_n²` with an absolute constant `C_c`: removing the endpoint jump turns the prime channel
into a bounded form on `ℓ²`, uniformly in the scale, the number and the positions of the atoms. -/
theorem abs_criticalCollaredPrimeEnergy_le {S : Finset ℕ} {M : ℕ} (hM : 1 ≤ M)
    (hS : DyadicScaleBlock S M) (b : ℕ → ℝ) :
    |criticalCollaredPrimeEnergy S b| ≤ criticalCollaredPrimeConstant * ∑ n ∈ S, b n ^ 2 := by
  set C := 4 / Real.pi ^ 4 * dyadicDilationConstant criticalCollarMass criticalCollarCurvature *
    ∑ n ∈ S, b n ^ 2
  have hsum : Summable (envelopePrimeMajorant 1) :=
    summable_envelopePrimeMajorant_of_half_lt (by norm_num)
  have hbd := abs_criticalCollaredPrimeAtom_le hM hS b
  have habs : Summable fun r => ‖criticalCollaredPrimeAtom S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => by rw [Real.norm_eq_abs]; exact hbd r)
      (hsum.mul_left C)
  unfold criticalCollaredPrimeEnergy
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ?_
  refine (habs.tsum_le_tsum (fun r => by rw [Real.norm_eq_abs]; exact hbd r) (hsum.mul_left C)).trans
    (le_of_eq ?_)
  rw [tsum_mul_left]
  unfold criticalCollaredPrimeConstant
  ring

end GaloisForLFunctions.ArithmeticPositivityTheory
