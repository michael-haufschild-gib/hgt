import GaloisForLFunctions.EulerFETransportTheory.TentPairingsOfDecayingDefects
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsObeyTheTentIdentity
import GaloisForLFunctions.HTGeometry.IntervalIntegralHolderSwap
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel

/-!
# Size of the tent errors of a decaying defect

`T_ε(h, y)` is the defect paired with the tent of width `h` centred at `y` (`tentDefect`).

* `tentDefect_eq` — `T_ε(h, y) = -(1/h) Re(τ₁² J_G(τ₁) - 2τ₀² J_G(τ₀) + τ₋₁² J_G(τ₋₁))`,
  `G = tentPrimitive g`.
* Pointwise: `|T| ≤ 2h · (3/2π)‖f‖₁ (y - h)^{-1/2}` (`abs_tentDefect_le_low`) and
  `|T| ≤ (4/h)(3/2π)‖G‖₁ (hε + |y| + h)^{3/2}` (`abs_tentDefect_le_high`).
* Mean square on `[W, W']`: `∫ T² ≤ 4h² π⁻¹ ‖f‖₂²` (`integral_sq_tentDefect_le_low`) and
  `∫ T² ≤ 18 M⁴ h⁻² π⁻¹ ‖G‖₂²` with `M = hε + W' + h` (`integral_sq_tentDefect_le_high`), from the
  vertical Hardy bound `∫ ‖J_f(σ + iw)‖² dw ≤ π⁻¹ ‖f‖₂²` (`integral_norm_sq_defectLaplace_vertical_le`).
-/

open Complex MeasureTheory Filter Topology Set Function
open RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ExactEventTheory
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-! ## The second-difference formula -/

theorem tentDefectKernel_eq (g : ℝ → ℂ) (h n ε s : ℝ) :
    tentDefectKernel g h n ε s =
      ((h : ℂ) * (((1 - |s| : ℝ) : ℂ) * defectLaplace g (tentPt h n ε s))).re := by
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, tentDefectKernel, tentPt]
  ring

theorem continuous_defectLaplace_tentPt {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n : ℝ) :
    Continuous fun s => defectLaplace g (tentPt h n ε s) :=
  continuousOn_univ.mp <| (differentiableOn_defectLaplace hgm.aestronglyMeasurable hgb).continuousOn.comp
    (continuous_tentPt h n ε).continuousOn fun s _ => by
      show 0 < (tentPt h n ε s).re
      rw [tentPt_re]; positivity

/-- **The tent error is a second difference** of `τ² J_G(τ)`. -/
theorem tentDefect_eq {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (y : ℝ) :
    tentDefect g h y ε = -(1 / h) *
      (tentPt h (y / h) ε 1 ^ 2 * defectLaplace (tentPrimitive g) (tentPt h (y / h) ε 1) -
        2 * (tentPt h (y / h) ε 0 ^ 2 * defectLaplace (tentPrimitive g) (tentPt h (y / h) ε 0)) +
          tentPt h (y / h) ε (-1) ^ 2 *
            defectLaplace (tentPrimitive g) (tentPt h (y / h) ε (-1))).re := by
  have hc := continuous_defectLaplace_tentPt hgm hgb hh hε (y / h)
  have hint : IntervalIntegrable (fun s : ℝ => (h : ℂ) * (((1 - |s| : ℝ) : ℂ) *
      defectLaplace g (tentPt h (y / h) ε s))) volume (-1) 1 :=
    (continuous_const.mul ((by fun_prop : Continuous fun s : ℝ => ((1 - |s| : ℝ) : ℂ)).mul hc))
      |>.intervalIntegrable _ _
  rw [tentDefect, intervalIntegral.integral_congr (fun s _ => tentDefectKernel_eq g h (y / h) ε s)]
  have hre := Complex.reCLM.intervalIntegral_comp_comm hint
  simp only [Complex.reCLM_apply] at hre
  rw [hre, intervalIntegral.integral_const_mul,
    integral_tent_mul_defectLaplace hgm hgb hh hε (y / h)]
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set Δ := tentPt h (y / h) ε 1 ^ 2 * defectLaplace (tentPrimitive g) (tentPt h (y / h) ε 1) -
    2 * (tentPt h (y / h) ε 0 ^ 2 * defectLaplace (tentPrimitive g) (tentPt h (y / h) ε 0)) +
      tentPt h (y / h) ε (-1) ^ 2 * defectLaplace (tentPrimitive g) (tentPt h (y / h) ε (-1))
  have e : (h : ℂ) * (Δ / ((h : ℂ) * I) ^ 2) = ((-(1 / h) : ℝ) : ℂ) * Δ := by
    rw [mul_pow, I_sq]
    push_cast
    field_simp
  rw [e, Complex.re_ofReal_mul]

/-! ## Linearity -/

theorem defectLaplace_add {f₁ f₂ : ℝ → ℂ} {C₁ C₂ : ℝ} {N₁ N₂ : ℕ} (hm₁ : Measurable f₁)
    (hm₂ : Measurable f₂) (hb₁ : ∀ t, ‖f₁ t‖ ≤ C₁ * (1 + |t|) ^ N₁)
    (hb₂ : ∀ t, ‖f₂ t‖ ≤ C₂ * (1 + |t|) ^ N₂) {τ : ℂ} (hτ : 0 < τ.re) :
    defectLaplace (f₁ + f₂) τ = defectLaplace f₁ τ + defectLaplace f₂ τ := by
  unfold defectLaplace
  rw [← mul_add, ← integral_add (integrable_defectLaplace_integrand hm₁.aestronglyMeasurable hb₁ hτ)
    (integrable_defectLaplace_integrand hm₂.aestronglyMeasurable hb₂ hτ)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  ring

theorem tentDefect_add {f₁ f₂ : ℝ → ℂ} {C₁ C₂ : ℝ} {N₁ N₂ : ℕ} (hm₁ : Measurable f₁)
    (hm₂ : Measurable f₂) (hb₁ : ∀ t, ‖f₁ t‖ ≤ C₁ * (1 + |t|) ^ N₁)
    (hb₂ : ∀ t, ‖f₂ t‖ ≤ C₂ * (1 + |t|) ^ N₂) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (y : ℝ) :
    tentDefect (f₁ + f₂) h y ε = tentDefect f₁ h y ε + tentDefect f₂ h y ε := by
  unfold tentDefect
  rw [← intervalIntegral.integral_add
    ((continuous_tentDefectKernel_of_poly hm₁ hb₁ hh hε _).intervalIntegrable _ _)
    ((continuous_tentDefectKernel_of_poly hm₂ hb₂ hh hε _).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [tentDefectKernel]
  rw [show (h : ℂ) * ((ε : ℂ) + ((y / h + s : ℝ) : ℂ) * I) = tentPt h (y / h) ε s from rfl,
    defectLaplace_add hm₁ hm₂ hb₁ hb₂ (by rw [tentPt_re]; positivity), Complex.add_re]
  ring

/-! ## Pointwise bounds -/

theorem norm_defectLaplace_le_of_integrable {f : ℝ → ℂ} (hf : Integrable f) {τ : ℂ}
    (hτ : 0 < τ.re) :
    ‖defectLaplace f τ‖ ≤ 3 / (2 * Real.pi) * (∫ t, ‖f t‖) * ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  rw [← closedDefectLaplace_eq hτ]
  exact norm_closedDefectLaplace_le hf hτ.le hτ0

theorem norm_tentPt_le (h n ε s : ℝ) (hh : 0 < h) (hε : 0 < ε) :
    ‖tentPt h n ε s‖ ≤ h * ε + |h * (n + s)| := by
  calc ‖tentPt h n ε s‖ ≤ |(tentPt h n ε s).re| + |(tentPt h n ε s).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = h * ε + |h * (n + s)| := by rw [tentPt_re, tentPt_im, abs_of_pos (by positivity)]

/-- **Low-frequency bound**: `|T_ε(h, y)| ≤ 2h (3/2π) ‖f‖₁ (y - h)^{-1/2}` for `y > h`. -/
theorem abs_tentDefect_le_low {f : ℝ → ℂ} {Cf : ℝ} {N : ℕ} (hfm : Measurable f)
    (hfb : ∀ t, ‖f t‖ ≤ Cf * (1 + |t|) ^ N) (hfi : Integrable f) {h ε y : ℝ} (hh : 0 < h)
    (hε : 0 < ε) (hy : h < y) :
    |tentDefect f h y ε| ≤
      2 * h * (3 / (2 * Real.pi) * (∫ t, ‖f t‖) * (y - h) ^ (-(1 / 2 : ℝ))) := by
  set K := 3 / (2 * Real.pi) * (∫ t, ‖f t‖) * (y - h) ^ (-(1 / 2 : ℝ)) with hK
  have hK0 : 0 ≤ K := by
    have := integral_nonneg (μ := volume) (f := fun t => ‖f t‖) fun t => norm_nonneg _
    positivity
  have hpt : ∀ s ∈ Icc (-1 : ℝ) 1, |tentDefectKernel f h (y / h) ε s| ≤ h * K := by
    intro s hs
    have hτ : 0 < (tentPt h (y / h) ε s).re := by rw [tentPt_re]; positivity
    have him : y - h ≤ ‖tentPt h (y / h) ε s‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      rw [tentPt_im, mul_add, mul_div_cancel₀ _ hh.ne']
      rw [abs_of_pos (by nlinarith [hs.1])]
      nlinarith [hs.1]
    have hJ := norm_defectLaplace_le_of_integrable hfi hτ
    have hJ' : ‖defectLaplace f (tentPt h (y / h) ε s)‖ ≤ K := by
      refine hJ.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith) him (by norm_num)) ?_)
      have := integral_nonneg (μ := volume) (f := fun t => ‖f t‖) fun t => norm_nonneg _
      positivity
    have h1s : 0 ≤ 1 - |s| := by rw [sub_nonneg]; exact abs_le.mpr hs
    have h1s' : 1 - |s| ≤ 1 := by linarith [abs_nonneg s]
    rw [tentDefectKernel, show (h : ℂ) * ((ε : ℂ) + ((y / h + s : ℝ) : ℂ) * I) =
      tentPt h (y / h) ε s from rfl, abs_mul, abs_of_nonneg (by positivity)]
    calc h * (1 - |s|) * |(defectLaplace f (tentPt h (y / h) ε s)).re|
        ≤ h * 1 * K := by
          gcongr
          exact (Complex.abs_re_le_norm _).trans hJ'
      _ = h * K := by ring
  calc |tentDefect f h y ε| ≤ ∫ s in (-1 : ℝ)..1, |tentDefectKernel f h (y / h) ε s| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ s in (-1 : ℝ)..1, h * K := by
        refine intervalIntegral.integral_mono_on (by norm_num)
          ((continuous_tentDefectKernel_of_poly hfm hfb hh hε _).abs.intervalIntegrable _ _)
          intervalIntegrable_const fun s hs => hpt s hs
    _ = 2 * h * K := by simp; ring

/-- **High-frequency bound**: `|T_ε(h, y)| ≤ (4/h)(3/2π)‖G‖₁ (hε + |y| + h)^{3/2}`. -/
theorem abs_tentDefect_le_high {f : ℝ → ℂ} {Cf : ℝ} {N : ℕ} (hfm : Measurable f)
    (hfb : ∀ t, ‖f t‖ ≤ Cf * (1 + |t|) ^ N) (hGi : Integrable (tentPrimitive f)) {h ε : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (y : ℝ) :
    |tentDefect f h y ε| ≤ 4 / h * (3 / (2 * Real.pi) * (∫ t, ‖tentPrimitive f t‖) *
      (h * ε + |y| + h) ^ (3 / 2 : ℝ)) := by
  set K := 3 / (2 * Real.pi) * (∫ t, ‖tentPrimitive f t‖) with hK
  have hK0 : 0 ≤ K := by
    have := integral_nonneg (μ := volume) (f := fun t => ‖tentPrimitive f t‖) fun t => norm_nonneg _
    positivity
  set M := h * ε + |y| + h with hM
  have hM0 : 0 < M := by positivity
  have hterm : ∀ σ : ℝ, |σ| ≤ 1 → ‖tentPt h (y / h) ε σ ^ 2 *
      defectLaplace (tentPrimitive f) (tentPt h (y / h) ε σ)‖ ≤ K * M ^ (3 / 2 : ℝ) := by
    intro σ hσ
    set τ := tentPt h (y / h) ε σ
    have hτ : 0 < τ.re := by rw [tentPt_re]; positivity
    have hτ0 : 0 < ‖τ‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hτ; simp at hτ
    have hτM : ‖τ‖ ≤ M := by
      refine (norm_tentPt_le h (y / h) ε σ hh hε).trans ?_
      rw [mul_add, mul_div_cancel₀ _ hh.ne', hM]
      have := abs_add_le y (h * σ)
      rw [abs_mul, abs_of_pos hh] at this
      nlinarith
    rw [norm_mul, norm_pow]
    calc ‖τ‖ ^ 2 * ‖defectLaplace (tentPrimitive f) τ‖ ≤ ‖τ‖ ^ 2 * (K * ‖τ‖ ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (norm_defectLaplace_le_of_integrable hGi hτ) (by positivity)
      _ = K * ‖τ‖ ^ (3 / 2 : ℝ) := by
          rw [show ‖τ‖ ^ 2 = ‖τ‖ ^ (2 : ℝ) by norm_cast, mul_left_comm,
            ← Real.rpow_add hτ0]
          norm_num
      _ ≤ K * M ^ (3 / 2 : ℝ) := by gcongr
  rw [tentDefect_eq hfm hfb hh hε y, abs_mul, abs_neg, abs_of_pos (by positivity),
    show 4 / h * (K * M ^ (3 / 2 : ℝ)) = 1 / h * (4 * (K * M ^ (3 / 2 : ℝ))) by ring]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by positivity)
  have h1 := hterm 1 (by norm_num)
  have h0 := hterm 0 (by norm_num)
  have hm := hterm (-1) (by norm_num)
  set A := tentPt h (y / h) ε 1 ^ 2 * defectLaplace (tentPrimitive f) (tentPt h (y / h) ε 1)
  set B := tentPt h (y / h) ε 0 ^ 2 * defectLaplace (tentPrimitive f) (tentPt h (y / h) ε 0)
  set C := tentPt h (y / h) ε (-1) ^ 2 * defectLaplace (tentPrimitive f) (tentPt h (y / h) ε (-1))
  have hAB := norm_sub_le A (2 * B)
  have hABC := norm_add_le (A - 2 * B) C
  have h2B : ‖2 * B‖ = 2 * ‖B‖ := by rw [norm_mul]; norm_num
  linarith

/-! ## Mean squares -/

/-- **The vertical Hardy bound**: for `f ∈ L²` and `σ > 0`, `∫ ‖J_f(σ + iw)‖² dw ≤ π⁻¹ ‖f‖₂²`. -/
theorem integral_norm_sq_defectLaplace_vertical_le {f : ℝ → ℂ} (hf : MemLp f 2 volume) {σ : ℝ}
    (hσ : 0 < σ) :
    Integrable (fun w : ℝ => ‖defectLaplace f ((σ : ℂ) + (w : ℂ) * I)‖ ^ 2) ∧
      ∫ w : ℝ, ‖defectLaplace f ((σ : ℂ) + (w : ℂ) * I)‖ ^ 2 ≤
        Real.pi⁻¹ * ∫ t, ‖f t‖ ^ 2 := by
  have hH := isHalfPlaneHardy_defectLaplace (hf.toLp f)
  have hJ : ∀ z, defectLaplace ((hf.toLp f : DefectL2) : ℝ → ℂ) z = defectLaplace f z :=
    fun z => defectLaplace_congr_ae hf.coeFn_toLp z
  have hnorm : ‖hf.toLp f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
    rw [Lp_two_norm_sq_eq_integral]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun t ht => by simp only [ht])
  set φ : ℝ → ℝ := fun w => ‖defectLaplace f ((σ : ℂ) + (w : ℂ) * I)‖ ^ 2 with hφ
  have hray : ∀ ξ, ‖defectLaplace ((hf.toLp f : DefectL2) : ℝ → ℂ) (rayLine σ ξ)‖ ^ (2 : ℕ) =
      φ (2 * Real.pi * ξ) := by
    intro ξ
    rw [hJ]
    simp only [hφ, rayLine]
  have hmem := hH.memLp σ hσ
  have hint_ray : Integrable (fun ξ => φ (2 * Real.pi * ξ)) :=
    ((memLp_two_iff_integrable_sq_norm hmem.1).mp hmem).congr
      (Eventually.of_forall fun ξ => hray ξ)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hint : Integrable φ := (integrable_comp_mul_left_iff φ hpi).mp hint_ray
  refine ⟨hint, ?_⟩
  have hb := hH.bound σ hσ
  rw [integral_congr_ae (Eventually.of_forall hray), Measure.integral_comp_mul_left φ,
    smul_eq_mul, abs_of_pos (by positivity), hnorm] at hb
  have hpi0 := Real.pi_pos
  have e : ∫ w, φ w = 2 * Real.pi * ((2 * Real.pi)⁻¹ * ∫ w, φ w) := by field_simp
  rw [e]
  calc 2 * Real.pi * ((2 * Real.pi)⁻¹ * ∫ w, φ w)
      ≤ 2 * Real.pi * ((2 * Real.pi ^ 2)⁻¹ * ∫ t, ‖f t‖ ^ 2) := by gcongr
    _ = Real.pi⁻¹ * ∫ t, ‖f t‖ ^ 2 := by field_simp

theorem tentPt_div (h ε y s : ℝ) (hh : 0 < h) :
    tentPt h (y / h) ε s = ((h * ε : ℝ) : ℂ) + ((y + h * s : ℝ) : ℂ) * I := by
  rw [tentPt]
  have : h * (y / h + s) = y + h * s := by field_simp
  apply Complex.ext <;> simp [this]

theorem tentDefectKernel_div (f : ℝ → ℂ) (h ε y s : ℝ) (hh : 0 < h) :
    tentDefectKernel f h (y / h) ε s = h * (1 - |s|) *
      (defectLaplace f (((h * ε : ℝ) : ℂ) + ((y + h * s : ℝ) : ℂ) * I)).re := by
  change h * (1 - |s|) * (defectLaplace f (tentPt h (y / h) ε s)).re = _
  rw [tentPt_div h ε y s hh]

theorem continuous_tentDefect {f : ℝ → ℂ} {Cf : ℝ} {N : ℕ} (hfm : Measurable f)
    (hfb : ∀ t, ‖f t‖ ≤ Cf * (1 + |t|) ^ N) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    Continuous fun y => tentDefect f h y ε := by
  have hJ := (differentiableOn_defectLaplace hfm.aestronglyMeasurable hfb).continuousOn
  have hc : Continuous fun p : ℝ × ℝ => defectLaplace f
      (((h * ε : ℝ) : ℂ) + ((p.1 + h * p.2 : ℝ) : ℂ) * I) :=
    continuousOn_univ.mp <| hJ.comp (by fun_prop) fun p _ => by
      show 0 < (((h * ε : ℝ) : ℂ) + ((p.1 + h * p.2 : ℝ) : ℂ) * I).re
      simp; positivity
  have hk : Continuous (uncurry fun y s => tentDefectKernel f h (y / h) ε s) := by
    have e : (uncurry fun y s => tentDefectKernel f h (y / h) ε s) = fun p : ℝ × ℝ =>
        h * (1 - |p.2|) * (defectLaplace f
          (((h * ε : ℝ) : ℂ) + ((p.1 + h * p.2 : ℝ) : ℂ) * I)).re :=
      funext fun p => tentDefectKernel_div f h ε p.1 p.2 hh
    rw [e]
    exact (by fun_prop : Continuous fun p : ℝ × ℝ => h * (1 - |p.2|)).mul
      (Complex.continuous_re.comp hc)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hk (-1) 1

/-- **Low-frequency mean square**: `∫_W^{W'} T² ≤ 4h² π⁻¹ ‖f‖₂²`. -/
theorem integral_sq_tentDefect_le_low {f : ℝ → ℂ} {Cf : ℝ} {N : ℕ} (hfm : Measurable f)
    (hfb : ∀ t, ‖f t‖ ≤ Cf * (1 + |t|) ^ N) (hf2 : MemLp f 2 volume) {h ε : ℝ} (hh : 0 < h)
    (hε : 0 < ε) {W W' : ℝ} (hW : W ≤ W') :
    ∫ y in W..W', tentDefect f h y ε ^ 2 ≤ 4 * h ^ 2 * (Real.pi⁻¹ * ∫ t, ‖f t‖ ^ 2) := by
  obtain ⟨hVi, hV⟩ := integral_norm_sq_defectLaplace_vertical_le hf2 (mul_pos hh hε)
  set V := ∫ t, ‖f t‖ ^ 2 with hVdef
  have hJ := (differentiableOn_defectLaplace hfm.aestronglyMeasurable hfb).continuousOn
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ → ℝ, ψ = fun y s => ‖defectLaplace f
      (((h * ε : ℝ) : ℂ) + ((y + h * s : ℝ) : ℂ) * I)‖ := ⟨_, rfl⟩
  have hψc : Continuous (uncurry ψ) := by
    have : Continuous fun p : ℝ × ℝ => defectLaplace f
        (((h * ε : ℝ) : ℂ) + ((p.1 + h * p.2 : ℝ) : ℂ) * I) :=
      continuousOn_univ.mp <| hJ.comp (by fun_prop) fun p _ => by
        show 0 < (((h * ε : ℝ) : ℂ) + ((p.1 + h * p.2 : ℝ) : ℂ) * I).re
        simp; positivity
    rw [hψ]
    exact this.norm
  -- pointwise: `T(y)² ≤ 2h² ∫_{-1}^{1} ψ(y, s)² ds`
  have hpt : ∀ y, tentDefect f h y ε ^ 2 ≤ 2 * h ^ 2 * ∫ s in (-1 : ℝ)..1, ψ y s ^ 2 := by
    intro y
    have hc1 : Continuous fun s => ψ y s := hψc.comp (Continuous.prodMk_right y)
    have habs : |tentDefect f h y ε| ≤ ∫ s in (-1 : ℝ)..1, h * ψ y s := by
      refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans
        (intervalIntegral.integral_mono_on (by norm_num)
          ((continuous_tentDefectKernel_of_poly hfm hfb hh hε _).abs.intervalIntegrable _ _)
          ((continuous_const.mul hc1).intervalIntegrable _ _) fun s hs => ?_)
      have h1s : 0 ≤ 1 - |s| := by rw [sub_nonneg]; exact abs_le.mpr hs
      rw [tentDefectKernel_div f h ε y s hh, abs_mul, abs_of_nonneg (by positivity)]
      calc h * (1 - |s|) * |(defectLaplace f (((h * ε : ℝ) : ℂ) +
            ((y + h * s : ℝ) : ℂ) * I)).re| ≤ h * 1 * ψ y s := by
            rw [hψ]
            gcongr
            · linarith [abs_nonneg s]
            · exact Complex.abs_re_le_norm _
        _ = h * ψ y s := by ring
    have hc2 : Continuous fun s => h * ψ y s := continuous_const.mul hc1
    have hcs := sq_intervalIntegral_mul_le (g := fun _ => (1 : ℝ)) (h := fun s => h * ψ y s)
      (a := -1) (b := 1) (by norm_num) continuous_const hc2
    simp only [one_mul, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hcs
    have hsq : tentDefect f h y ε ^ 2 ≤ (∫ s in (-1 : ℝ)..1, h * ψ y s) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have e : ∫ s in (-1 : ℝ)..1, (h * ψ y s) ^ 2 = h ^ 2 * ∫ s in (-1 : ℝ)..1, ψ y s ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun s _ => by ring
    rw [e] at hcs
    norm_num at hcs
    rw [intervalIntegral.integral_const_mul] at hsq
    linarith
  -- each row has energy at most `V`
  have hrow : ∀ s, ∫ y in W..W', ψ y s ^ 2 ≤ Real.pi⁻¹ * V := by
    intro s
    have e := intervalIntegral.integral_comp_add_right
      (fun w : ℝ => ‖defectLaplace f (((h * ε : ℝ) : ℂ) + (w : ℂ) * I)‖ ^ 2) (h * s) (a := W)
      (b := W')
    rw [show (fun y => ψ y s ^ 2) = fun y : ℝ =>
      ‖defectLaplace f (((h * ε : ℝ) : ℂ) + ((y + h * s : ℝ) : ℂ) * I)‖ ^ 2 by
        rw [hψ], e, intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_le_integral hVi (Eventually.of_forall fun w => by positivity)).trans ?_
    exact hV
  have hcont2 : Continuous (uncurry fun y s => ψ y s ^ 2) := hψc.pow 2
  calc ∫ y in W..W', tentDefect f h y ε ^ 2
      ≤ ∫ y in W..W', 2 * h ^ 2 * ∫ s in (-1 : ℝ)..1, ψ y s ^ 2 :=
        intervalIntegral.integral_mono_on hW
          (((continuous_tentDefect hfm hfb hh hε).pow 2).intervalIntegrable _ _)
          ((continuous_const.mul
            (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont2 _ _))
            |>.intervalIntegrable _ _) fun y _ => hpt y
    _ = 2 * h ^ 2 * ∫ s in (-1 : ℝ)..1, ∫ y in W..W', ψ y s ^ 2 := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_integral_swap_of_continuous hcont2 hW (by norm_num)]
    _ ≤ 2 * h ^ 2 * ∫ s in (-1 : ℝ)..1, Real.pi⁻¹ * V := by
        gcongr
        refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const
          fun s _ => hrow s
        have hsw : Continuous (uncurry fun s y => ψ y s ^ 2) :=
          hcont2.comp continuous_swap
        exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hsw W W')
          |>.intervalIntegrable _ _
    _ = 4 * h ^ 2 * (Real.pi⁻¹ * V) := by simp; ring

end GaloisForLFunctions.EulerFETransportTheory
