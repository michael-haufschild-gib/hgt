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

/-- **High-frequency mean square**: for `0 ≤ W ≤ W'`,
`∫_W^{W'} T² ≤ 18 M⁴ h⁻² π⁻¹ ‖G‖₂²`, `M = hε + W' + h`, `G = tentPrimitive f`. -/
theorem integral_sq_tentDefect_le_high {f : ℝ → ℂ} {Cf : ℝ} {N : ℕ} (hfm : Measurable f)
    (hfb : ∀ t, ‖f t‖ ≤ Cf * (1 + |t|) ^ N) (hG2 : MemLp (tentPrimitive f) 2 volume) {h ε : ℝ}
    (hh : 0 < h) (hε : 0 < ε) {W W' : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ W') :
    ∫ y in W..W', tentDefect f h y ε ^ 2 ≤ 18 * (h * ε + W' + h) ^ 4 / h ^ 2 *
      (Real.pi⁻¹ * ∫ t, ‖tentPrimitive f t‖ ^ 2) := by
  obtain ⟨hVi, hV⟩ := integral_norm_sq_defectLaplace_vertical_le hG2 (mul_pos hh hε)
  set V := ∫ t, ‖tentPrimitive f t‖ ^ 2 with hVdef
  set M := h * ε + W' + h with hM
  have hM0 : 0 ≤ M := by have := hW0.trans hW; positivity
  have hGm := measurable_tentPrimitive hfm
  have hGb : ∀ t, ‖tentPrimitive f t‖ ≤ 4 / 3 * Cf * (1 + |t|) ^ N := fun t =>
    (norm_tentPrimitive_le f t).trans (by rw [mul_assoc]; gcongr; exact hfb t)
  have hJ := (differentiableOn_defectLaplace hGm.aestronglyMeasurable hGb).continuousOn
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ → ℝ, φ = fun σ y => ‖defectLaplace (tentPrimitive f)
      (((h * ε : ℝ) : ℂ) + ((y + h * σ : ℝ) : ℂ) * I)‖ := ⟨_, rfl⟩
  have hφc : ∀ σ, Continuous (φ σ) := by
    intro σ
    have : Continuous fun y : ℝ => defectLaplace (tentPrimitive f)
        (((h * ε : ℝ) : ℂ) + ((y + h * σ : ℝ) : ℂ) * I) :=
      continuousOn_univ.mp <| hJ.comp (by fun_prop) fun y _ => by
        show 0 < (((h * ε : ℝ) : ℂ) + ((y + h * σ : ℝ) : ℂ) * I).re
        simp; positivity
    rw [hφ]
    exact this.norm
  -- each shifted row has energy at most `π⁻¹ V`
  have hrow : ∀ σ, ∫ y in W..W', φ σ y ^ 2 ≤ Real.pi⁻¹ * V := by
    intro σ
    have e := intervalIntegral.integral_comp_add_right
      (fun w : ℝ => ‖defectLaplace (tentPrimitive f) (((h * ε : ℝ) : ℂ) + (w : ℂ) * I)‖ ^ 2)
      (h * σ) (a := W) (b := W')
    rw [show (fun y => φ σ y ^ 2) = fun y : ℝ => ‖defectLaplace (tentPrimitive f)
      (((h * ε : ℝ) : ℂ) + ((y + h * σ : ℝ) : ℂ) * I)‖ ^ 2 by rw [hφ], e,
      intervalIntegral.integral_of_le (by linarith)]
    exact (setIntegral_le_integral hVi (Eventually.of_forall fun w => by positivity)).trans hV
  -- pointwise: `T² ≤ (6 M⁴ / h²)(φ₁² + φ₀² + φ₋₁²)` on `[W, W']`
  have hpt : ∀ y ∈ Icc W W', tentDefect f h y ε ^ 2 ≤
      6 * M ^ 4 / h ^ 2 * (φ 1 y ^ 2 + φ 0 y ^ 2 + φ (-1) y ^ 2) := by
    intro y hy
    have hterm : ∀ σ : ℝ, |σ| ≤ 1 → ‖tentPt h (y / h) ε σ ^ 2 *
        defectLaplace (tentPrimitive f) (tentPt h (y / h) ε σ)‖ ≤ M ^ 2 * φ σ y := by
      intro σ hσ
      rw [norm_mul, norm_pow, tentPt_div h ε y σ hh, hφ]
      gcongr
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      rw [abs_of_pos (by positivity), hM]
      have := abs_add_le y (h * σ)
      rw [abs_of_nonneg (hW0.trans hy.1), abs_mul, abs_of_pos hh] at this
      nlinarith [hy.2]
    rw [tentDefect_eq hfm hfb hh hε y]
    have hA := hterm 1 (by norm_num)
    have hB := hterm 0 (by norm_num)
    have hC := hterm (-1) (by norm_num)
    set A := tentPt h (y / h) ε 1 ^ 2 * defectLaplace (tentPrimitive f) (tentPt h (y / h) ε 1)
    set B := tentPt h (y / h) ε 0 ^ 2 * defectLaplace (tentPrimitive f) (tentPt h (y / h) ε 0)
    set C := tentPt h (y / h) ε (-1) ^ 2 *
      defectLaplace (tentPrimitive f) (tentPt h (y / h) ε (-1))
    have hre : |(A - 2 * B + C).re| ≤ M ^ 2 * (φ 1 y + 2 * φ 0 y + φ (-1) y) := by
      refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
      have h1 := norm_sub_le A (2 * B)
      have h2 : ‖2 * B‖ = 2 * ‖B‖ := by rw [norm_mul]; norm_num
      linarith
    have hφ0 : ∀ σ, 0 ≤ φ σ y := fun σ => by rw [hφ]; positivity
    have hcs : (φ 1 y + 2 * φ 0 y + φ (-1) y) ^ 2 ≤ 6 * (φ 1 y ^ 2 + φ 0 y ^ 2 + φ (-1) y ^ 2) := by
      nlinarith [sq_nonneg (φ 0 y - 2 * φ 1 y), sq_nonneg (φ (-1) y - φ 1 y),
        sq_nonneg (2 * φ (-1) y - φ 0 y)]
    have hsq : (-(1 / h) * (A - 2 * B + C).re) ^ 2 ≤
        (1 / h) ^ 2 * (M ^ 2 * (φ 1 y + 2 * φ 0 y + φ (-1) y)) ^ 2 := by
      rw [show (-(1 / h) * (A - 2 * B + C).re) ^ 2 = (1 / h) ^ 2 * |(A - 2 * B + C).re| ^ 2 by
        rw [sq_abs]; ring]
      gcongr
    calc (-(1 / h) * (A - 2 * B + C).re) ^ 2
        ≤ (1 / h) ^ 2 * (M ^ 2 * (φ 1 y + 2 * φ 0 y + φ (-1) y)) ^ 2 := hsq
      _ = M ^ 4 / h ^ 2 * (φ 1 y + 2 * φ 0 y + φ (-1) y) ^ 2 := by ring
      _ ≤ M ^ 4 / h ^ 2 * (6 * (φ 1 y ^ 2 + φ 0 y ^ 2 + φ (-1) y ^ 2)) := by gcongr
      _ = _ := by ring
  have hc : ∀ σ, Continuous fun y => φ σ y ^ 2 := fun σ => (hφc σ).pow 2
  calc ∫ y in W..W', tentDefect f h y ε ^ 2
      ≤ ∫ y in W..W', 6 * M ^ 4 / h ^ 2 * (φ 1 y ^ 2 + φ 0 y ^ 2 + φ (-1) y ^ 2) :=
        intervalIntegral.integral_mono_on hW
          (((continuous_tentDefect hfm hfb hh hε).pow 2).intervalIntegrable _ _)
          ((continuous_const.mul (((hc 1).add (hc 0)).add (hc (-1)))).intervalIntegrable _ _) hpt
    _ = 6 * M ^ 4 / h ^ 2 * ((∫ y in W..W', φ 1 y ^ 2) + (∫ y in W..W', φ 0 y ^ 2) +
          ∫ y in W..W', φ (-1) y ^ 2) := by
        have i1 : IntervalIntegrable (fun y => φ 1 y ^ 2 + φ 0 y ^ 2) volume W W' :=
          ((hc 1).add (hc 0)).intervalIntegrable _ _
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add i1 ((hc (-1)).intervalIntegrable _ _),
          intervalIntegral.integral_add ((hc 1).intervalIntegrable _ _)
            ((hc 0).intervalIntegrable _ _)]
    _ ≤ 6 * M ^ 4 / h ^ 2 * (Real.pi⁻¹ * V + Real.pi⁻¹ * V + Real.pi⁻¹ * V) := by
        gcongr
        · exact hrow 1
        · exact hrow 0
        · exact hrow (-1)
    _ = 18 * M ^ 4 / h ^ 2 * (Real.pi⁻¹ * V) := by ring

/-! ## Decaying defects: the frequency split -/

theorem three_sixteenths_le_norm_tentFactor (t : ℝ) :
    3 / 16 * (1 + |t|) ^ 2 ≤ ‖tentFactor t‖ := by
  rw [tentFactor, norm_mul]
  have hre1 := Complex.abs_re_le_norm ((3 / 2 : ℂ) + 2 * t * I)
  have him1 := Complex.abs_im_le_norm ((3 / 2 : ℂ) + 2 * t * I)
  have hre2 := Complex.abs_re_le_norm ((1 / 2 : ℂ) + 2 * t * I)
  have him2 := Complex.abs_im_le_norm ((1 / 2 : ℂ) + 2 * t * I)
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, sub_zero, zero_add,
    add_zero] at hre1 him1 hre2 him2
  norm_num at hre1 him1 hre2 him2
  have h1 : 3 / 4 * (1 + |t|) ≤ ‖(3 / 2 : ℂ) + 2 * t * I‖ := by
    rcases le_or_gt |t| 1 with ht | ht
    · nlinarith
    · nlinarith
  have h2 : 1 / 4 * (1 + |t|) ≤ ‖(1 / 2 : ℂ) + 2 * t * I‖ := by
    rcases le_or_gt |t| 1 with ht | ht
    · nlinarith
    · nlinarith
  have h0 : 0 ≤ 1 + |t| := by positivity
  calc 3 / 16 * (1 + |t|) ^ 2 = (3 / 4 * (1 + |t|)) * (1 / 4 * (1 + |t|)) := by ring
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)

/-- The low-frequency part `1_{|t| ≤ R} g`. -/
def lowPart (R : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := {t : ℝ | |t| ≤ R}.indicator g

/-- The high-frequency part `1_{|t| > R} g`. -/
def highPart (R : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := {t : ℝ | |t| ≤ R}ᶜ.indicator g

theorem measurableSet_abs_le (R : ℝ) : MeasurableSet {t : ℝ | |t| ≤ R} :=
  measurableSet_le continuous_abs.measurable measurable_const

theorem lowPart_add_highPart (R : ℝ) (g : ℝ → ℂ) : lowPart R g + highPart R g = g :=
  Set.indicator_self_add_compl _ g

theorem measurable_lowPart {g : ℝ → ℂ} (hgm : Measurable g) (R : ℝ) :
    Measurable (lowPart R g) := hgm.indicator (measurableSet_abs_le R)

theorem measurable_highPart {g : ℝ → ℂ} (hgm : Measurable g) (R : ℝ) :
    Measurable (highPart R g) := hgm.indicator (measurableSet_abs_le R).compl

theorem norm_lowPart_le (R : ℝ) (g : ℝ → ℂ) (t : ℝ) : ‖lowPart R g t‖ ≤ ‖g t‖ :=
  norm_indicator_le_norm_self _ _

theorem norm_highPart_le (R : ℝ) (g : ℝ → ℂ) (t : ℝ) : ‖highPart R g t‖ ≤ ‖g t‖ :=
  norm_indicator_le_norm_self _ _

theorem nonneg_of_decay {g : ℝ → ℂ} {C a : ℝ} (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) :
    0 ≤ C := by
  have := hgd 0
  simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at this
  exact (norm_nonneg _).trans this

theorem norm_lowPart_le_indicator {g : ℝ → ℂ} {C a : ℝ} (ha : 0 ≤ a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) (R t : ℝ) :
    ‖lowPart R g t‖ ≤ {t : ℝ | |t| ≤ R}.indicator (fun _ => C) t := by
  unfold lowPart
  by_cases ht : t ∈ {t : ℝ | |t| ≤ R}
  · rw [indicator_of_mem ht, indicator_of_mem ht]
    refine (hgd t).trans (mul_le_of_le_one_right (nonneg_of_decay hgd) ?_)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by linarith)
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, norm_zero]

/-- The twice-integrated high part decays at rate `R^{-q}`:
`‖G_R(t)‖ ≤ (16/3) C R^{-q} (1 + |t|)^{-(2 + a - q)}` for `0 ≤ q`, `0 < R`. -/
theorem norm_tentPrimitive_highPart_le {g : ℝ → ℂ} {C a : ℝ}
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R) (t : ℝ) :
    ‖tentPrimitive (highPart R g) t‖ ≤ 16 / 3 * C * R ^ (-q) * (1 + |t|) ^ (-(2 + a - q)) := by
  have hC : 0 ≤ C * (1 + |t|) ^ (-a) := (norm_nonneg _).trans (hgd t)
  have hpos : 0 < 1 + |t| := by positivity
  have hF := three_sixteenths_le_norm_tentFactor t
  have hFpos : 0 < ‖tentFactor t‖ := norm_pos_iff.mpr (tentFactor_ne_zero t)
  unfold tentPrimitive highPart
  by_cases ht : t ∈ {t : ℝ | |t| ≤ R}ᶜ
  · rw [indicator_of_mem ht, norm_div, div_le_iff₀ hFpos]
    have htR : R < |t| := by simpa using ht
    have hRq : (1 + |t|) ^ (-q) ≤ R ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos hR (by linarith) (by linarith)
    have hsplit : (1 + |t|) ^ (-a) = (1 + |t|) ^ (-q) * (1 + |t|) ^ (-(2 + a - q)) *
        (1 + |t|) ^ (2 : ℝ) := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]; ring_nf
    have hsq : (1 + |t|) ^ (2 : ℝ) = (1 + |t|) ^ 2 := by norm_cast
    have hC0 : 0 ≤ C := by
      by_contra hneg
      push Not at hneg
      have : C * (1 + |t|) ^ (-a) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
      linarith
    calc ‖g t‖ ≤ C * (1 + |t|) ^ (-a) := hgd t
      _ = C * ((1 + |t|) ^ (-q) * (1 + |t|) ^ (-(2 + a - q)) * (1 + |t|) ^ 2) := by
          rw [hsplit, hsq]
      _ ≤ C * (R ^ (-q) * (1 + |t|) ^ (-(2 + a - q)) * (16 / 3 * ‖tentFactor t‖)) := by
          gcongr
          linarith
      _ = 16 / 3 * C * R ^ (-q) * (1 + |t|) ^ (-(2 + a - q)) * ‖tentFactor t‖ := by ring
  · rw [indicator_of_notMem ht, zero_div, norm_zero]
    have hC0 : 0 ≤ C := by
      by_contra hneg
      push Not at hneg
      have : C * (1 + |t|) ^ (-a) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
      linarith
    positivity

theorem integrable_one_add_abs_rpow_neg {r : ℝ} (hr : 1 < r) :
    Integrable fun t : ℝ => (1 + |t|) ^ (-r) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  simpa [Real.norm_eq_abs] using h

theorem poly_of_decay {g : ℝ → ℂ} {C a : ℝ} (ha : 0 ≤ a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) (t : ℝ) : ‖g t‖ ≤ C * (1 + |t|) ^ (0 : ℕ) := by
  rw [pow_zero, mul_one]
  exact (hgd t).trans (mul_le_of_le_one_right (nonneg_of_decay hgd)
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by linarith)))

theorem abs_le_eq_Icc (R : ℝ) : {t : ℝ | |t| ≤ R} = Icc (-R) R :=
  Set.ext fun t => by rw [mem_setOf_eq, mem_Icc, abs_le]

theorem integrable_indicator_abs_le (R C : ℝ) :
    Integrable ({t : ℝ | |t| ≤ R}.indicator fun _ => C) := by
  rw [abs_le_eq_Icc]
  exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc

theorem integral_indicator_abs_le {R : ℝ} (hR : 0 ≤ R) (C : ℝ) :
    ∫ t, {t : ℝ | |t| ≤ R}.indicator (fun _ => C) t = 2 * R * C := by
  rw [abs_le_eq_Icc, integral_indicator measurableSet_Icc, setIntegral_const, measureReal_def,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  ring

/-- `‖1_{|t| ≤ R} g‖₁ ≤ 2RC`. -/
theorem integral_norm_lowPart_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 ≤ a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {R : ℝ} (hR : 0 ≤ R) :
    Integrable (lowPart R g) ∧ ∫ t, ‖lowPart R g t‖ ≤ 2 * R * C := by
  have hb : ∀ t, ‖lowPart R g t‖ ≤ {t : ℝ | |t| ≤ R}.indicator (fun _ => C) t :=
    norm_lowPart_le_indicator ha hgd R
  have hi : Integrable (lowPart R g) := (integrable_indicator_abs_le R C).mono'
    (measurable_lowPart hgm R).aestronglyMeasurable (Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  rw [← integral_indicator_abs_le hR C]
  exact integral_mono hi.norm (integrable_indicator_abs_le R C) hb

/-- `‖1_{|t| ≤ R} g‖₂² ≤ 2RC²`. -/
theorem integral_norm_sq_lowPart_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 ≤ a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {R : ℝ} (hR : 0 ≤ R) :
    MemLp (lowPart R g) 2 volume ∧ ∫ t, ‖lowPart R g t‖ ^ 2 ≤ 2 * R * C ^ 2 := by
  have hC := nonneg_of_decay hgd
  have hb : ∀ t, ‖lowPart R g t‖ ^ 2 ≤ {t : ℝ | |t| ≤ R}.indicator (fun _ => C ^ 2) t := by
    intro t
    have h1 := norm_lowPart_le_indicator ha hgd R t
    by_cases ht : t ∈ {t : ℝ | |t| ≤ R}
    · rw [indicator_of_mem ht] at h1 ⊢
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [indicator_of_notMem ht] at h1 ⊢
      have : ‖lowPart R g t‖ = 0 := le_antisymm h1 (norm_nonneg _)
      rw [this]; norm_num
  have hi : Integrable fun t => ‖lowPart R g t‖ ^ 2 := (integrable_indicator_abs_le R (C ^ 2)).mono'
    ((measurable_lowPart hgm R).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb t)
  refine ⟨(memLp_two_iff_integrable_sq_norm (measurable_lowPart hgm R).aestronglyMeasurable).mpr hi,
    ?_⟩
  rw [← integral_indicator_abs_le hR (C ^ 2)]
  exact integral_mono hi (integrable_indicator_abs_le R _) hb

/-- `‖G_R‖₁ ≤ (16/3) C R^{-q} ∫ (1 + |t|)^{-(2 + a - q)}` when `2 + a - q > 1`. -/
theorem integral_norm_tentPrimitive_highPart_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ}
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hr : 1 < 2 + a - q) :
    Integrable (tentPrimitive (highPart R g)) ∧ ∫ t, ‖tentPrimitive (highPart R g) t‖ ≤
      16 / 3 * C * R ^ (-q) * ∫ t : ℝ, (1 + |t|) ^ (-(2 + a - q)) := by
  have hI := integrable_one_add_abs_rpow_neg hr
  have hb := norm_tentPrimitive_highPart_le hgd hq hR
  have hi : Integrable (tentPrimitive (highPart R g)) := (hI.const_mul (16 / 3 * C * R ^ (-q))).mono'
    (measurable_tentPrimitive (measurable_highPart hgm R)).aestronglyMeasurable
    (Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hi.norm (hI.const_mul _) hb

/-- `‖G_R‖₂² ≤ (256/9) C² R^{-2q} ∫ (1 + |t|)^{-2(2 + a - q)}` when `2(2 + a - q) > 1`. -/
theorem integral_norm_sq_tentPrimitive_highPart_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ}
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hr : 1 < 2 * (2 + a - q)) :
    MemLp (tentPrimitive (highPart R g)) 2 volume ∧ ∫ t, ‖tentPrimitive (highPart R g) t‖ ^ 2 ≤
      (16 / 3 * C * R ^ (-q)) ^ 2 * ∫ t : ℝ, (1 + |t|) ^ (-(2 * (2 + a - q))) := by
  have hC := nonneg_of_decay hgd
  have hI := integrable_one_add_abs_rpow_neg hr
  have hm := (measurable_tentPrimitive (measurable_highPart hgm R))
  have hb : ∀ t, ‖tentPrimitive (highPart R g) t‖ ^ 2 ≤
      (16 / 3 * C * R ^ (-q)) ^ 2 * (1 + |t|) ^ (-(2 * (2 + a - q))) := by
    intro t
    have h1 := norm_tentPrimitive_highPart_le hgd hq hR t
    have hpos : 0 < 1 + |t| := by positivity
    have e : (1 + |t|) ^ (-(2 * (2 + a - q))) = ((1 + |t|) ^ (-(2 + a - q))) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]; push_cast; ring_nf
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans_eq (by ring)) 2
  have hi : Integrable fun t => ‖tentPrimitive (highPart R g) t‖ ^ 2 := (hI.const_mul _).mono'
    (hm.norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb t)
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hi (hI.const_mul _) hb

/-- **The origin tent**: `|T_ε(b, 0)| ≤ K b^{1/2}` for `0 < ε ≤ 1`. -/
theorem exists_abs_tentDefect_origin_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ε : ℝ, 0 < b → 0 < ε → ε ≤ 1 →
      |tentDefect g b 0 ε| ≤ K * b ^ (1 / 2 : ℝ) := by
  have hC := nonneg_of_decay hgd
  -- `G = tentPrimitive g` is integrable (`highPart` at a negative cutoff is `g`)
  have hhigh : highPart (-1) g = g := by
    funext t
    unfold highPart
    rw [indicator_of_mem]
    simp only [mem_compl_iff, mem_setOf_eq, not_le]
    linarith [abs_nonneg t]
  have hGi : Integrable (tentPrimitive g) := by
    have hI := integrable_one_add_abs_rpow_neg (r := 2 + a) (by linarith)
    refine (hI.const_mul (16 / 3 * C)).mono' (measurable_tentPrimitive hgm).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hpos : 0 < 1 + |t| := by positivity
    have hF := three_sixteenths_le_norm_tentFactor t
    have hFpos : 0 < ‖tentFactor t‖ := norm_pos_iff.mpr (tentFactor_ne_zero t)
    rw [tentPrimitive, norm_div, div_le_iff₀ hFpos]
    have hsplit : (1 + |t|) ^ (-a) = (1 + |t|) ^ (-(2 + a)) * (1 + |t|) ^ (2 : ℝ) := by
      rw [← Real.rpow_add hpos]; ring_nf
    calc ‖g t‖ ≤ C * (1 + |t|) ^ (-a) := hgd t
      _ = C * ((1 + |t|) ^ (-(2 + a)) * (1 + |t|) ^ 2) := by
          rw [hsplit]; norm_cast
      _ ≤ C * ((1 + |t|) ^ (-(2 + a)) * (16 / 3 * ‖tentFactor t‖)) := by gcongr; linarith
      _ = 16 / 3 * C * (1 + |t|) ^ (-(2 + a)) * ‖tentFactor t‖ := by ring
  set K₀ := 3 / (2 * Real.pi) * ∫ t, ‖tentPrimitive g t‖ with hK₀
  have hK₀ : 0 ≤ K₀ := by
    have := integral_nonneg (μ := volume) (f := fun t => ‖tentPrimitive g t‖) fun t => norm_nonneg _
    positivity
  refine ⟨4 * K₀ * (2 : ℝ) ^ (3 / 2 : ℝ), by positivity, fun b ε hb hε hε1 => ?_⟩
  have h := abs_tentDefect_le_high hgm (poly_of_decay ha.le hgd) hGi hb hε 0
  rw [abs_zero, add_zero] at h
  refine h.trans ?_
  have hle : b * ε + b ≤ 2 * b := by nlinarith
  have hpow : (b * ε + b) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by norm_num) hb.le]
    exact Real.rpow_le_rpow (by positivity) hle (by norm_num)
  have hb32 : b ^ (3 / 2 : ℝ) = b * b ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb, Real.rpow_one]
  calc 4 / b * (K₀ * (b * ε + b) ^ (3 / 2 : ℝ))
      ≤ 4 / b * (K₀ * ((2 : ℝ) ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ))) := by gcongr
    _ = 4 * K₀ * (2 : ℝ) ^ (3 / 2 : ℝ) * b ^ (1 / 2 : ℝ) := by
        rw [hb32]; field_simp

/-- The low part above a tent away from the origin: for `R ≥ 0` and `2h ≤ η ≤ y`,
`|T_ε(1_{|t| ≤ R} g; h, y)| ≤ 2h (3/2π)(2RC) √2 η^{-1/2}`. -/
theorem abs_tentDefect_lowPart_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {R η h y ε : ℝ} (hR : 0 ≤ R) (hh : 0 < h)
    (hη : 2 * h ≤ η) (hy : η ≤ y) (hε : 0 < ε) :
    |tentDefect (lowPart R g) h y ε| ≤
      2 * h * (3 / (2 * Real.pi) * (2 * R * C) * ((2 : ℝ) ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ)))) := by
  have hη0 : 0 < η := by linarith
  obtain ⟨hi1, hn1⟩ := integral_norm_lowPart_le hgm ha.le hgd hR
  have hlow := abs_tentDefect_le_low (measurable_lowPart hgm R)
    (fun t => (norm_lowPart_le R g t).trans (poly_of_decay ha.le hgd t)) hi1 hh hε
    (show h < y by linarith)
  have hpow_y : (y - h) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ)) := by
    calc (y - h) ^ (-(1 / 2 : ℝ)) ≤ (η / 2) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ)) := by
          rw [Real.div_rpow hη0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            div_inv_eq_mul, mul_comm]
  have h3 : 0 ≤ 3 / (2 * Real.pi) := by positivity
  refine hlow.trans (mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hn1 h3)
    hpow_y (Real.rpow_nonneg (by linarith) _) ?_) (by positivity))
  have := nonneg_of_decay hgd
  positivity

/-- The high part above a tent of height at most `2`: for `R > 0`, `h ≤ 1` and `ε ≤ 1`,
`|T_ε(1_{|t| > R} g; h, y)| ≤ (4/h)(3/2π)((16/3) C R^{-q} I) 8`, `q = 1 + a/2`. -/
theorem abs_tentDefect_highPart_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {R h y ε : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hh1 : h ≤ 1) (hy0 : 0 ≤ y) (hy : y ≤ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |tentDefect (highPart R g) h y ε| ≤ 4 / h * (3 / (2 * Real.pi) *
      (16 / 3 * C * R ^ (-(1 + a / 2)) * ∫ t : ℝ, (1 + |t|) ^ (-(2 + a - (1 + a / 2)))) * 8) := by
  obtain ⟨hi2, hn2⟩ := integral_norm_tentPrimitive_highPart_le hgm hgd (q := 1 + a / 2)
    (by linarith) hR (by linarith)
  have hhigh := abs_tentDefect_le_high (measurable_highPart hgm R)
    (fun t => (norm_highPart_le R g t).trans (poly_of_decay ha.le hgd t)) hi2 hh hε y
  have hM : (h * ε + |y| + h) ^ (3 / 2 : ℝ) ≤ 8 := by
    have h4 : h * ε + |y| + h ≤ 4 := by
      rw [abs_of_nonneg hy0]; nlinarith
    calc (h * ε + |y| + h) ^ (3 / 2 : ℝ) ≤ (4 : ℝ) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h4 (by norm_num)
      _ = 8 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hint0 : 0 ≤ ∫ t, ‖tentPrimitive (highPart R g) t‖ :=
    integral_nonneg (μ := volume) (f := fun t => ‖tentPrimitive (highPart R g) t‖)
      fun t => norm_nonneg _
  refine hhigh.trans (mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hn2
    (by positivity)) hM (by positivity) ?_) (by positivity))
  have := nonneg_of_decay hgd
  have : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ (-(2 + a - (1 + a / 2))) := integral_nonneg fun t => by positivity
  positivity

/-- **Small widths**: for `2h ≤ η ≤ y ≤ 2`, `h ≤ 1` and `0 < ε ≤ 1`,
`|T_ε(h, y)| ≤ K (η^{-1/2} + 1) h^ρ` with `ρ > 0`.  Split at `|t| = h^{-κ}`: the low part costs
`h · h^{-κ} η^{-1/2}`, the twice-integrated high part `h⁻¹ h^{κq}`, `q = 1 + a/2`. -/
theorem exists_abs_tentDefect_le_smallWidth {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ}
    (ha : 0 < a) (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) :
    ∃ K ρ : ℝ, 0 ≤ K ∧ 0 < ρ ∧ ∀ η h y ε : ℝ, 0 < h → h ≤ 1 → 2 * h ≤ η → η ≤ y → y ≤ 2 →
      0 < ε → ε ≤ 1 → |tentDefect g h y ε| ≤ K * (η ^ (-(1 / 2 : ℝ)) + 1) * h ^ ρ := by
  have hC := nonneg_of_decay hgd
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 + a / 2 := ⟨_, rfl⟩
  have hq1 : 1 < q := by rw [hq]; linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 + 1 / q) / 2 := ⟨_, rfl⟩
  have hqinv : 1 / q < 1 := by rw [div_lt_one (by linarith)]; exact hq1
  have hκ1 : κ < 1 := by rw [hκ]; linarith
  have hκq : 1 < κ * q := by
    rw [hκ, div_mul_eq_mul_div, add_mul, one_div_mul_cancel (by linarith), one_mul, lt_div_iff₀
      (by norm_num)]
    linarith
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = min (1 - κ) (κ * q - 1) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; exact lt_min (by linarith) (by linarith)
  obtain ⟨I₁, hI₁⟩ : ∃ I₁ : ℝ, I₁ = ∫ t : ℝ, (1 + |t|) ^ (-(2 + a - (1 + a / 2))) := ⟨_, rfl⟩
  have hI₁0 : 0 ≤ I₁ := by rw [hI₁]; exact integral_nonneg fun t => by positivity
  obtain ⟨cL, hcL⟩ : ∃ cL : ℝ, cL = 2 * (3 / (2 * Real.pi)) * (2 * C) * (2 : ℝ) ^ (1 / 2 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨cH, hcH⟩ : ∃ cH : ℝ, cH = 4 * (3 / (2 * Real.pi)) * (16 / 3 * C * I₁) * 8 := ⟨_, rfl⟩
  have hcL0 : 0 ≤ cL := by rw [hcL]; positivity
  have hcH0 : 0 ≤ cH := by rw [hcH]; positivity
  refine ⟨cL + cH, ρ, by positivity, hρ0, fun η h y ε hh hh1 hη hy hy2 hε hε1 => ?_⟩
  have hη0 : 0 < η := by linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = h ^ (-κ) := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by
    rw [hRdef]; exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hh1 (by linarith)
  have hR0 : 0 < R := by linarith
  have hsplit := tentDefect_add (measurable_lowPart hgm R) (measurable_highPart hgm R)
    (fun t => (norm_lowPart_le R g t).trans (poly_of_decay ha.le hgd t))
    (fun t => (norm_highPart_le R g t).trans (poly_of_decay ha.le hgd t)) hh hε y
  rw [lowPart_add_highPart] at hsplit
  have hlow := abs_tentDefect_lowPart_le hgm ha hgd hR0.le hh hη hy hε
  have hhigh := abs_tentDefect_highPart_le hgm ha hgd hR0 hh hh1 (by linarith) hy2 hε hε1
  rw [← hI₁, ← hq] at hhigh
  -- exponent bookkeeping
  have hhR : h * R ≤ h ^ ρ := by
    rw [hRdef, ← Real.rpow_one_add' hh.le (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by rw [hρ]; linarith [min_le_left (1 - κ) (κ * q - 1)])
  have hRq : R ^ (-q) / h ≤ h ^ ρ := by
    rw [hRdef, ← Real.rpow_mul hh.le, ← Real.rpow_sub_one hh.ne']
    exact Real.rpow_le_rpow_of_exponent_ge hh hh1
      (by rw [hρ]; linarith [min_le_right (1 - κ) (κ * q - 1)])
  have hlow' : |tentDefect (lowPart R g) h y ε| ≤ cL * η ^ (-(1 / 2 : ℝ)) * h ^ ρ := by
    calc |tentDefect (lowPart R g) h y ε| ≤ _ := hlow
      _ = cL * η ^ (-(1 / 2 : ℝ)) * (h * R) := by rw [hcL]; ring
      _ ≤ cL * η ^ (-(1 / 2 : ℝ)) * h ^ ρ := mul_le_mul_of_nonneg_left hhR (by positivity)
  have hhigh' : |tentDefect (highPart R g) h y ε| ≤ cH * h ^ ρ := by
    calc |tentDefect (highPart R g) h y ε| ≤ _ := hhigh
      _ = cH * (R ^ (-q) / h) := by rw [hcH]; ring
      _ ≤ cH * h ^ ρ := mul_le_mul_of_nonneg_left hRq hcH0
  have hηpos : 0 ≤ η ^ (-(1 / 2 : ℝ)) := by positivity
  have hhρ : 0 ≤ h ^ ρ := by positivity
  rw [hsplit]
  refine (abs_add_le _ _).trans ((add_le_add hlow' hhigh').trans ?_)
  nlinarith [mul_nonneg hcL0 hhρ, mul_nonneg hcH0 hhρ, mul_nonneg (mul_nonneg hcH0 hηpos) hhρ]

theorem integral_sq_tentDefect_lowPart_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ}
    (ha : 0 < a) (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {R h ε W W' : ℝ} (hR : 0 ≤ R)
    (hh : 0 < h) (hε : 0 < ε) (hW : W ≤ W') :
    ∫ y in W..W', tentDefect (lowPart R g) h y ε ^ 2 ≤
      4 * h ^ 2 * (Real.pi⁻¹ * (2 * R * C ^ 2)) := by
  obtain ⟨hm, hn⟩ := integral_norm_sq_lowPart_le hgm ha.le hgd hR
  refine (integral_sq_tentDefect_le_low (measurable_lowPart hgm R)
    (fun t => (norm_lowPart_le R g t).trans (poly_of_decay ha.le hgd t)) hm hh hε hW).trans ?_
  gcongr

theorem integral_sq_tentDefect_highPart_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ}
    (ha : 0 < a) (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {R h ε W W' : ℝ} (hR : 0 < R)
    (hh : 0 < h) (hε : 0 < ε) (hW0 : 0 ≤ W) (hW : W ≤ W') :
    ∫ y in W..W', tentDefect (highPart R g) h y ε ^ 2 ≤
      18 * (h * ε + W' + h) ^ 4 / h ^ 2 * (Real.pi⁻¹ *
        ((16 / 3 * C * R ^ (-((3 + a) / 2))) ^ 2 * ∫ t : ℝ, (1 + |t|) ^ (-(1 + a)))) := by
  obtain ⟨hm, hn⟩ := integral_norm_sq_tentPrimitive_highPart_le hgm hgd (q := (3 + a) / 2)
    (by linarith) hR (by linarith)
  have he : 2 * (2 + a - (3 + a) / 2) = 1 + a := by ring
  rw [he] at hn
  refine (integral_sq_tentDefect_le_high (measurable_highPart hgm R)
    (fun t => (norm_highPart_le R g t).trans (poly_of_decay ha.le hgd t)) hm hh hε hW0 hW).trans ?_
  gcongr

/-- **Dyadic shells**: for a fixed width `h ≤ 1` there are `K` and `α < 1` with
`∫_W^{2W} T_ε(h, y)² dy ≤ K W^α` for all `W ≥ 1` and `0 < ε ≤ 1`.  Split at `|t| = (W/h)^κ`:
the low part costs `h² (W/h)^κ`, the high part `W⁴ h⁻² (W/h)^{-κ(3 + a)}`. -/
theorem exists_integral_sq_tentDefect_shell_le {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ}
    (ha : 0 < a) (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a)) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ∃ K α : ℝ, α < 1 ∧ ∀ W ε : ℝ, 1 ≤ W → 0 < ε → ε ≤ 1 →
      ∫ y in W..2 * W, tentDefect g h y ε ^ 2 ≤ K * W ^ α := by
  have hC := nonneg_of_decay hgd
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 + 3 / (3 + a)) / 2 := ⟨_, rfl⟩
  have h3a : 3 / (3 + a) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hκ1 : κ < 1 := by rw [hκ]; linarith
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hκa : 3 < κ * (3 + a) := by
    rw [hκ, div_mul_eq_mul_div, add_mul, div_mul_cancel₀ _ (by linarith), lt_div_iff₀
      (by norm_num)]
    linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = max κ (4 - κ * (3 + a)) := ⟨_, rfl⟩
  have hα1 : α < 1 := by rw [hα]; exact max_lt hκ1 (by linarith)
  obtain ⟨I₂, hI₂⟩ : ∃ I₂ : ℝ, I₂ = ∫ t : ℝ, (1 + |t|) ^ (-(1 + a)) := ⟨_, rfl⟩
  have hI₂0 : 0 ≤ I₂ := by rw [hI₂]; exact integral_nonneg fun t => by positivity
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = 2 * (4 * h ^ 2 * (Real.pi⁻¹ * (2 * C ^ 2))) * h ^ (-κ) :=
    ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = 2 * (18 * 4 ^ 4 / h ^ 2 * (Real.pi⁻¹ *
      ((16 / 3 * C) ^ 2 * I₂))) * h ^ (κ * (3 + a)) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  refine ⟨c₁ + c₂, α, hα1, fun W ε hW hε hε1 => ?_⟩
  have hW0 : 0 < W := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (W / h) ^ κ := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; positivity
  have hsplit := tentDefect_add (measurable_lowPart hgm R) (measurable_highPart hgm R)
    (fun t => (norm_lowPart_le R g t).trans (poly_of_decay ha.le hgd t))
    (fun t => (norm_highPart_le R g t).trans (poly_of_decay ha.le hgd t)) hh hε
  simp only [lowPart_add_highPart] at hsplit
  have hcL := continuous_tentDefect (measurable_lowPart hgm R)
    (fun t => (norm_lowPart_le R g t).trans (poly_of_decay ha.le hgd t)) hh hε
  have hcH := continuous_tentDefect (measurable_highPart hgm R)
    (fun t => (norm_highPart_le R g t).trans (poly_of_decay ha.le hgd t)) hh hε
  have hlow := integral_sq_tentDefect_lowPart_le hgm ha hgd hR0.le hh hε (W := W) (W' := 2 * W)
    (by linarith)
  have hhigh := integral_sq_tentDefect_highPart_le hgm ha hgd hR0 hh hε (W := W) (W' := 2 * W)
    hW0.le (by linarith)
  rw [← hI₂] at hhigh
  -- `(x + y)² ≤ 2x² + 2y²`
  have hsum : ∫ y in W..2 * W, tentDefect g h y ε ^ 2 ≤
      2 * (∫ y in W..2 * W, tentDefect (lowPart R g) h y ε ^ 2) +
        2 * ∫ y in W..2 * W, tentDefect (highPart R g) h y ε ^ 2 := by
    have i1 : IntervalIntegrable (fun y => 2 * tentDefect (lowPart R g) h y ε ^ 2) volume W
        (2 * W) := (continuous_const.mul (hcL.pow 2)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun y => 2 * tentDefect (highPart R g) h y ε ^ 2) volume W
        (2 * W) := (continuous_const.mul (hcH.pow 2)).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun y => 2 * tentDefect (lowPart R g) h y ε ^ 2 +
        2 * tentDefect (highPart R g) h y ε ^ 2) volume W (2 * W) := i1.add i2
    have i0 : IntervalIntegrable (fun y => tentDefect g h y ε ^ 2) volume W (2 * W) :=
      ((continuous_tentDefect hgm (poly_of_decay ha.le hgd) hh hε).pow 2).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add i1 i2]
    refine intervalIntegral.integral_mono_on (by linarith) i0 i3 fun y _ => ?_
    rw [hsplit y]
    nlinarith [sq_nonneg (tentDefect (lowPart R g) h y ε - tentDefect (highPart R g) h y ε)]
  -- exponent bookkeeping
  have hRW : R = W ^ κ * h ^ (-κ) := by
    rw [hR, Real.div_rpow hW0.le hh.le, Real.rpow_neg hh.le, div_eq_mul_inv]
  have hRq : (R ^ (-((3 + a) / 2))) ^ 2 = W ^ (-(κ * (3 + a))) * h ^ (κ * (3 + a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le, hR, ← Real.rpow_mul (by positivity),
      Real.div_rpow hW0.le hh.le, div_eq_mul_inv, ← Real.rpow_neg hh.le]
    push_cast
    ring_nf
  have hM : h * ε + 2 * W + h ≤ 4 * W := by nlinarith
  have hWk : W ^ κ ≤ W ^ α := Real.rpow_le_rpow_of_exponent_le hW (by rw [hα]; exact le_max_left _ _)
  have hW4 : W ^ 4 * W ^ (-(κ * (3 + a))) ≤ W ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW (by rw [hα]; push_cast; exact le_max_right _ _)
  have hlow' : 2 * ∫ y in W..2 * W, tentDefect (lowPart R g) h y ε ^ 2 ≤ c₁ * W ^ α := by
    calc 2 * ∫ y in W..2 * W, tentDefect (lowPart R g) h y ε ^ 2
        ≤ 2 * (4 * h ^ 2 * (Real.pi⁻¹ * (2 * R * C ^ 2))) := by gcongr
      _ = c₁ * W ^ κ := by rw [hc₁, hRW]; ring
      _ ≤ c₁ * W ^ α := mul_le_mul_of_nonneg_left hWk hc₁0
  have hhigh' : 2 * ∫ y in W..2 * W, tentDefect (highPart R g) h y ε ^ 2 ≤ c₂ * W ^ α := by
    calc 2 * ∫ y in W..2 * W, tentDefect (highPart R g) h y ε ^ 2
        ≤ 2 * (18 * (h * ε + 2 * W + h) ^ 4 / h ^ 2 * (Real.pi⁻¹ *
            ((16 / 3 * C * R ^ (-((3 + a) / 2))) ^ 2 * I₂))) := by gcongr
      _ ≤ 2 * (18 * (4 * W) ^ 4 / h ^ 2 * (Real.pi⁻¹ *
            ((16 / 3 * C * R ^ (-((3 + a) / 2))) ^ 2 * I₂))) := by gcongr
      _ = c₂ * (W ^ 4 * W ^ (-(κ * (3 + a)))) := by
          rw [hc₂, mul_pow (16 / 3 * C), hRq]; ring
      _ ≤ c₂ * W ^ α := mul_le_mul_of_nonneg_left hW4 hc₂0
  linarith

end GaloisForLFunctions.EulerFETransportTheory
