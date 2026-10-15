import GaloisForLFunctions.RHTower.PrimeBlindPoleCurvatureFloor
import GaloisForLFunctions.RHTower.WeilSymbolMertensExpansion
import GaloisForLFunctions.RHTower.SelbergSymbolCriticalStrip
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# The spectral density of a blind kernel and the split gap estimate

The even real autocorrelation `K_c` of a combination `c` of tests is the cosine transform of its
spectral density `ρ_c(τ) = Σ_f c_f ‖f̂(τ)‖²/(2π)`:
`K_c(x) = ∫ ρ_c(τ) cos(τx) dτ` (`blindKernel_eq_integral`).  For a nonnegative combination `ρ_c ≥ 0`,
and `ρ_c`, `|τ| ρ_c`, `√|τ| ρ_c`, `τ² ρ_c` are integrable (the tests are `C²` with compact support,
so `f̂` decays like `|τ|⁻²`).

**Split gap estimate** (`abs_blindKernel_le_of_eq_zero_endpoints_split`).  If `K_c(a) = K_c(b) = 0`
and `u ∈ [a, b]`, then for every threshold `T`
`|K_c(u)| ≤ 2 ∫_{|τ| ≥ T} ρ_c + (b − a) ∫_{|τ| < T} |τ| ρ_c`:
the interpolation of `K_c` between `a` and `b` vanishes, the high-frequency part of the spectral
measure contributes at most twice its mass, and the low-frequency part contributes through the
Lipschitz constant `|τ|` of `cos(τ·)` times the gap.  With the threshold at the local node density
this is the frequency-resolved form of the gap estimate of `PrimeBlindPoleCurvatureFloor`.
-/

open Complex MeasureTheory Set Finsupp Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-! ## The spectral density of a test -/

/-- The spectral density `‖f̂(τ)‖²/(2π)` of a test. -/
def specDensity (f : WeilTestFn) (τ : ℝ) : ℝ := ‖paperFT f.1 τ‖ ^ 2 / (2 * Real.pi)

theorem specDensity_nonneg (f : WeilTestFn) (τ : ℝ) : 0 ≤ specDensity f τ := by
  unfold specDensity; positivity

theorem continuous_paperFT_real_arg {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous fun r : ℝ => paperFT f r := by
  unfold paperFT
  refine continuous_of_dominated (bound := fun u => ‖f u‖) (fun r => ?_) (fun r => ?_) hf.norm ?_
  · exact hf.1.mul (by fun_prop : Continuous fun u : ℝ =>
      Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
  · exact Filter.Eventually.of_forall fun u => by fun_prop

theorem continuous_specDensity (f : WeilTestFn) : Continuous (specDensity f) := by
  have h := continuous_paperFT_real_arg (f := f.1)
    (f.2.1.continuous.integrable_of_hasCompactSupport f.2.2)
  exact (h.norm.pow 2).div_const _

/-- The even autocorrelation is the cosine transform of the spectral density. -/
theorem symAuto_eq_integral (f : WeilTestFn) (y : ℝ) :
    symAuto f y = ∫ τ, specDensity f τ * Real.cos (τ * y) := by
  obtain ⟨L, -, hfL⟩ := exists_levelTest f
  have h := integral_normSq_paperFT_mul_cos_eq f.2.1 (tsupport_subset_of_levelTest hfL) y
  have e : (fun τ : ℝ => specDensity f τ * Real.cos (τ * y)) =
      fun τ : ℝ => (‖paperFT f.1 τ‖ ^ 2 * Real.cos (τ * y)) / (2 * Real.pi) := by
    funext τ; unfold specDensity; ring
  rw [e, MeasureTheory.integral_div, h]
  unfold symAuto
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

theorem integrable_specDensity_mul_cos (f : WeilTestFn) (y : ℝ) :
    Integrable fun τ => specDensity f τ * Real.cos (τ * y) := by
  obtain ⟨L, -, hfL⟩ := exists_levelTest f
  have h := integrable_normSq_paperFT_mul_cos f.2.1 (tsupport_subset_of_levelTest hfL) y
  have e : (fun τ : ℝ => specDensity f τ * Real.cos (τ * y)) =
      fun τ : ℝ => (‖paperFT f.1 τ‖ ^ 2 * Real.cos (τ * y)) / (2 * Real.pi) := by
    funext τ; unfold specDensity; ring
  rw [e]
  exact h.div_const _

theorem integrable_specDensity (f : WeilTestFn) : Integrable (specDensity f) := by
  have h := integrable_specDensity_mul_cos f 0
  simpa using h

/-- Decay of the transform of a `C²` compactly supported test. -/
theorem exists_norm_paperFT_le_decay (f : WeilTestFn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖paperFT f.1 τ‖ ≤ C / (1 + |τ|) ^ 2 := by
  obtain ⟨L, -, hfL⟩ := exists_levelTest f
  refine ⟨4 * ((∫ u, ‖f.1 u‖) + ∫ u, ‖deriv (deriv f.1) u‖), by positivity, fun τ => ?_⟩
  have h := norm_paperFT_le_decay f.2.1 (fun u hu => hfL u hu) (τ : ℂ)
  simpa using h

theorem integrable_sq_mul_specDensity (f : WeilTestFn) :
    Integrable fun τ : ℝ => τ ^ 2 * specDensity f τ := by
  obtain ⟨C, hC0, hdec⟩ := exists_norm_paperFT_le_decay f
  have hmaj : Integrable fun τ : ℝ => C ^ 2 / (2 * Real.pi) * (1 + ‖τ‖) ^ (-(2 : ℝ)) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul _
  refine hmaj.mono' ((continuous_id.pow 2).mul (continuous_specDensity f)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  have hd : 0 < 1 + |τ| := by positivity
  have h3 : (1 + ‖τ‖) ^ (-(2 : ℝ)) = 1 / (1 + |τ|) ^ 2 := by
    rw [Real.norm_eq_abs, Real.rpow_neg hd.le, Real.rpow_two, one_div]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg τ) (specDensity_nonneg f τ)), h3]
  unfold specDensity
  have h1 := hdec τ
  have h2 : ‖paperFT f.1 τ‖ ^ 2 ≤ (C / (1 + |τ|) ^ 2) ^ 2 := by gcongr
  have h4 : τ ^ 2 ≤ (1 + |τ|) ^ 2 := by nlinarith [abs_nonneg τ, sq_abs τ]
  have hd2 : 0 < (1 + |τ|) ^ 2 := by positivity
  have hd4 : 0 < ((1 + |τ|) ^ 2) ^ 2 := by positivity
  have h5 : τ ^ 2 * ((C / (1 + |τ|) ^ 2) ^ 2 / (2 * Real.pi)) ≤
      C ^ 2 / (2 * Real.pi) * (1 / (1 + |τ|) ^ 2) := by
    rw [div_pow, show τ ^ 2 * (C ^ 2 / ((1 + |τ|) ^ 2) ^ 2 / (2 * Real.pi)) =
        C ^ 2 / (2 * Real.pi) * (τ ^ 2 / ((1 + |τ|) ^ 2) ^ 2) by ring]
    have hfrac : τ ^ 2 / ((1 + |τ|) ^ 2) ^ 2 ≤ 1 / (1 + |τ|) ^ 2 := by
      rw [div_le_div_iff₀ hd4 hd2]
      nlinarith
    exact mul_le_mul_of_nonneg_left hfrac (by positivity)
  calc τ ^ 2 * (‖paperFT f.1 τ‖ ^ 2 / (2 * Real.pi))
      ≤ τ ^ 2 * ((C / (1 + |τ|) ^ 2) ^ 2 / (2 * Real.pi)) := by gcongr
    _ ≤ _ := h5

theorem sqrt_abs_le_one_add_sq (τ : ℝ) : Real.sqrt |τ| ≤ 1 + τ ^ 2 := by
  rcases le_or_gt |τ| 1 with h | h
  · have : Real.sqrt |τ| ≤ 1 := Real.sqrt_le_one.mpr h
    nlinarith [sq_nonneg τ]
  · have h1 : |τ| ≤ τ ^ 2 := by nlinarith [sq_abs τ, abs_nonneg τ]
    have h2 : Real.sqrt |τ| ≤ Real.sqrt (τ ^ 2) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq_eq_abs] at h2
    nlinarith [sq_nonneg τ]

theorem abs_le_one_add_sq (τ : ℝ) : |τ| ≤ 1 + τ ^ 2 := by
  nlinarith [sq_abs τ, abs_nonneg τ, sq_nonneg (|τ| - 1)]

theorem integrable_sqrt_mul_specDensity (f : WeilTestFn) :
    Integrable fun τ : ℝ => Real.sqrt |τ| * specDensity f τ := by
  have hmaj : Integrable fun τ : ℝ => specDensity f τ + τ ^ 2 * specDensity f τ :=
    (integrable_specDensity f).add (integrable_sq_mul_specDensity f)
  refine hmaj.mono' ((Real.continuous_sqrt.comp continuous_abs).mul
    (continuous_specDensity f)).aestronglyMeasurable (Filter.Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (specDensity_nonneg f τ))]
  have := sqrt_abs_le_one_add_sq τ
  have h0 := specDensity_nonneg f τ
  nlinarith

theorem integrable_abs_mul_specDensity (f : WeilTestFn) :
    Integrable fun τ : ℝ => |τ| * specDensity f τ := by
  have hmaj : Integrable fun τ : ℝ => specDensity f τ + τ ^ 2 * specDensity f τ :=
    (integrable_specDensity f).add (integrable_sq_mul_specDensity f)
  refine hmaj.mono' (continuous_abs.mul (continuous_specDensity f)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (specDensity_nonneg f τ))]
  have := abs_le_one_add_sq τ
  have h0 := specDensity_nonneg f τ
  nlinarith

/-! ## The spectral density of a combination -/

/-- The spectral density `Σ_f c_f ‖f̂‖²/(2π)` of a combination of tests. -/
def specDensityC (c : WeilTestFn →₀ ℝ) (τ : ℝ) : ℝ := ∑ f ∈ c.support, c f * specDensity f τ

theorem specDensityC_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (τ : ℝ) :
    0 ≤ specDensityC c τ :=
  Finset.sum_nonneg fun f _ => mul_nonneg (hc f) (specDensity_nonneg f τ)

theorem continuous_specDensityC (c : WeilTestFn →₀ ℝ) : Continuous (specDensityC c) :=
  continuous_finsetSum _ fun f _ => continuous_const.mul (continuous_specDensity f)

theorem integrable_specDensityC (c : WeilTestFn →₀ ℝ) : Integrable (specDensityC c) :=
  integrable_finsetSum _ fun f _ => (integrable_specDensity f).const_mul _

theorem integrable_mul_specDensityC (c : WeilTestFn →₀ ℝ) {w : ℝ → ℝ}
    (hw : ∀ f : WeilTestFn, Integrable fun τ => w τ * specDensity f τ) :
    Integrable fun τ : ℝ => w τ * specDensityC c τ := by
  have e : (fun τ : ℝ => w τ * specDensityC c τ) =
      fun τ => ∑ f ∈ c.support, c f * (w τ * specDensity f τ) := by
    funext τ; unfold specDensityC; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun f _ => (hw f).const_mul _

theorem integrable_sq_mul_specDensityC (c : WeilTestFn →₀ ℝ) :
    Integrable fun τ : ℝ => τ ^ 2 * specDensityC c τ :=
  integrable_mul_specDensityC c fun f => integrable_sq_mul_specDensity f

theorem integrable_sqrt_mul_specDensityC (c : WeilTestFn →₀ ℝ) :
    Integrable fun τ : ℝ => Real.sqrt |τ| * specDensityC c τ :=
  integrable_mul_specDensityC c fun f => integrable_sqrt_mul_specDensity f

theorem integrable_abs_mul_specDensityC (c : WeilTestFn →₀ ℝ) :
    Integrable fun τ : ℝ => |τ| * specDensityC c τ :=
  integrable_mul_specDensityC c fun f => integrable_abs_mul_specDensity f

theorem integrable_specDensityC_mul_cos (c : WeilTestFn →₀ ℝ) (x : ℝ) :
    Integrable fun τ : ℝ => specDensityC c τ * Real.cos (τ * x) := by
  have e : (fun τ : ℝ => specDensityC c τ * Real.cos (τ * x)) =
      fun τ => ∑ f ∈ c.support, c f * (specDensity f τ * Real.cos (τ * x)) := by
    funext τ; unfold specDensityC; rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun f _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun f _ => (integrable_specDensity_mul_cos f x).const_mul _

/-- **Spectral representation of the blind kernel.** -/
theorem blindKernel_eq_integral (c : WeilTestFn →₀ ℝ) (x : ℝ) :
    blindKernel c x = ∫ τ, specDensityC c τ * Real.cos (τ * x) := by
  unfold blindKernel specDensityC
  have e : (fun τ => (∑ f ∈ c.support, c f * specDensity f τ) * Real.cos (τ * x)) =
      fun τ => ∑ f ∈ c.support, c f * (specDensity f τ * Real.cos (τ * x)) := by
    funext τ; rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun f _ => by ring
  rw [e, MeasureTheory.integral_finsetSum _ fun f _ => (integrable_specDensity_mul_cos f x).const_mul _]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MeasureTheory.integral_const_mul, symAuto_eq_integral]

/-! ## The split gap estimate -/

/-- The interpolation defect of the cosine between `a` and `b`, at `u = (1 − λ) b + λ a`. -/
theorem abs_cos_interp_defect_le_two (τ a b u lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    |Real.cos (τ * u) - (lam * Real.cos (τ * a) + (1 - lam) * Real.cos (τ * b))| ≤ 2 := by
  have ha := Real.abs_cos_le_one (τ * a)
  have hb := Real.abs_cos_le_one (τ * b)
  have hu := Real.abs_cos_le_one (τ * u)
  rw [abs_le] at ha hb hu ⊢
  constructor <;> nlinarith

theorem abs_cos_interp_defect_le_lipschitz {τ a b u lam : ℝ} (hab : a ≤ b) (hu : u ∈ Icc a b)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    |Real.cos (τ * u) - (lam * Real.cos (τ * a) + (1 - lam) * Real.cos (τ * b))| ≤
      |τ| * (b - a) := by
  have e : Real.cos (τ * u) - (lam * Real.cos (τ * a) + (1 - lam) * Real.cos (τ * b)) =
      lam * (Real.cos (τ * u) - Real.cos (τ * a)) +
        (1 - lam) * (Real.cos (τ * u) - Real.cos (τ * b)) := by ring
  have ha : |Real.cos (τ * u) - Real.cos (τ * a)| ≤ |τ| * (b - a) := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hu.1, hu.2], by linarith [hu.2]⟩)
      (abs_nonneg τ)
  have hb : |Real.cos (τ * u) - Real.cos (τ * b)| ≤ |τ| * (b - a) := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.1, hu.2]⟩)
      (abs_nonneg τ)
  rw [e]
  calc |lam * (Real.cos (τ * u) - Real.cos (τ * a)) +
        (1 - lam) * (Real.cos (τ * u) - Real.cos (τ * b))|
      ≤ lam * |Real.cos (τ * u) - Real.cos (τ * a)| +
        (1 - lam) * |Real.cos (τ * u) - Real.cos (τ * b)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (show (0 : ℝ) ≤ 1 - lam by linarith)]
    _ ≤ lam * (|τ| * (b - a)) + (1 - lam) * (|τ| * (b - a)) := by gcongr
    _ = |τ| * (b - a) := by ring

/-- **Split gap estimate.**  If the blind kernel vanishes at `a < b`, then on `[a, b]` it is bounded
by twice the spectral mass at frequencies `≥ T` plus `(b − a)` times the first spectral moment below
`T`, for every threshold `T`. -/
theorem abs_blindKernel_le_of_eq_zero_endpoints_split {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    {a b : ℝ} (hab : a < b) (ha : blindKernel c a = 0) (hb : blindKernel c b = 0) {u : ℝ}
    (hu : u ∈ Icc a b) (T : ℝ) :
    |blindKernel c u| ≤ 2 * (∫ τ in {τ : ℝ | T ≤ |τ|}, specDensityC c τ) +
      (b - a) * ∫ τ in {τ : ℝ | |τ| < T}, |τ| * specDensityC c τ := by
  have hρ0 : ∀ τ, 0 ≤ specDensityC c τ := specDensityC_nonneg hc
  have hρc : Continuous (specDensityC c) := continuous_specDensityC c
  have hba : 0 < b - a := by linarith
  set lam := (b - u) / (b - a) with hlam
  have hl0 : 0 ≤ lam := div_nonneg (by linarith [hu.2]) hba.le
  have hl1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith [hu.1]
  -- the defect function
  set E : ℝ → ℝ := fun τ => Real.cos (τ * u) - (lam * Real.cos (τ * a) + (1 - lam) * Real.cos (τ * b))
    with hE
  have hEc : Continuous E := by
    simp only [hE]
    fun_prop
  have hE2 : ∀ τ, |E τ| ≤ 2 := fun τ => abs_cos_interp_defect_le_two τ a b u lam hl0 hl1
  have hElip : ∀ τ, |E τ| ≤ |τ| * (b - a) := fun τ =>
    abs_cos_interp_defect_le_lipschitz hab.le hu hl0 hl1
  have hi_u := integrable_specDensityC_mul_cos c u
  have hi_a := integrable_specDensityC_mul_cos c a
  have hi_b := integrable_specDensityC_mul_cos c b
  have hi_ab : Integrable fun τ => lam * (specDensityC c τ * Real.cos (τ * a)) +
      (1 - lam) * (specDensityC c τ * Real.cos (τ * b)) := (hi_a.const_mul _).add (hi_b.const_mul _)
  -- K(u) = ∫ ρ E
  have hKu : blindKernel c u = ∫ τ, specDensityC c τ * E τ := by
    rw [blindKernel_eq_integral] at ha hb
    rw [blindKernel_eq_integral]
    have h1 : ∫ τ, specDensityC c τ * E τ = ∫ τ, (specDensityC c τ * Real.cos (τ * u) -
        (lam * (specDensityC c τ * Real.cos (τ * a)) +
          (1 - lam) * (specDensityC c τ * Real.cos (τ * b)))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      simp only [hE]
      ring
    rw [h1, integral_sub hi_u hi_ab,
      integral_add (f := fun τ => lam * (specDensityC c τ * Real.cos (τ * a)))
        (g := fun τ => (1 - lam) * (specDensityC c τ * Real.cos (τ * b)))
        (hi_a.const_mul _) (hi_b.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ha, hb]
    ring
  -- integrability of ρ E and the two majorants
  have hρabs : Integrable fun τ => specDensityC c τ * |E τ| := by
    refine (integrable_specDensityC c).const_mul 2 |>.mono' (hρc.mul hEc.abs).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 τ), abs_abs]
    nlinarith [hE2 τ, hρ0 τ]
  have hρτ : Integrable fun τ => (b - a) * (|τ| * specDensityC c τ) :=
    (integrable_abs_mul_specDensityC c).const_mul _
  -- |K(u)| ≤ ∫ ρ |E|
  have h1 : |blindKernel c u| ≤ ∫ τ, specDensityC c τ * |E τ| := by
    rw [hKu]
    have := norm_integral_le_integral_norm (μ := volume) fun τ => specDensityC c τ * E τ
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    show ‖specDensityC c τ * E τ‖ = specDensityC c τ * |E τ|
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 τ)]
  -- split at the threshold
  have hSm : MeasurableSet {τ : ℝ | |τ| < T} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hSc : {τ : ℝ | |τ| < T}ᶜ = {τ : ℝ | T ≤ |τ|} := by
    ext τ; simp [not_lt]
  have hsplit : ∫ τ, specDensityC c τ * |E τ| =
      (∫ τ in {τ : ℝ | |τ| < T}, specDensityC c τ * |E τ|) +
        ∫ τ in {τ : ℝ | T ≤ |τ|}, specDensityC c τ * |E τ| := by
    rw [← hSc]
    exact (integral_add_compl hSm hρabs).symm
  have hlow : ∫ τ in {τ : ℝ | |τ| < T}, specDensityC c τ * |E τ| ≤
      ∫ τ in {τ : ℝ | |τ| < T}, (b - a) * (|τ| * specDensityC c τ) := by
    refine setIntegral_mono_on hρabs.integrableOn hρτ.integrableOn hSm fun τ _ => ?_
    have := mul_le_mul_of_nonneg_left (hElip τ) (hρ0 τ)
    nlinarith [this]
  have hhigh : ∫ τ in {τ : ℝ | T ≤ |τ|}, specDensityC c τ * |E τ| ≤
      ∫ τ in {τ : ℝ | T ≤ |τ|}, 2 * specDensityC c τ := by
    refine setIntegral_mono_on hρabs.integrableOn
      ((integrable_specDensityC c).const_mul 2).integrableOn (hSc ▸ hSm.compl) fun τ _ => ?_
    have := mul_le_mul_of_nonneg_left (hE2 τ) (hρ0 τ)
    linarith
  rw [MeasureTheory.integral_const_mul] at hlow hhigh
  linarith

end

end RHTower.WeilOneSided
