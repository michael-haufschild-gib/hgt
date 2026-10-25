import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A Gaussian-weighted Plancherel bound for Laplace transforms on a vertical line

For `h` integrable and square integrable on `(0, ∞)` put `M(t) = ∫_{v>0} h(v) e^{-itv} dv`, the
Laplace transform of `h` on the imaginary axis (`lapI`).  For every centre `a` and width `b > 0`

`∫ e^{-((t-a)/b)²} ‖M(t)‖² dt ≤ 2π ∫_{v>0} h(v)²`   (`integral_gaussW_mul_normSq_lapI_le`),

uniformly in `a` and `b`.  So the mean square of `M` over any window `[a - b/2, a + b/2]` is at
most `2π e^{1/4} ‖h‖₂²`, however long the window: the weighted form of Plancherel's theorem.

**Proof.**  `‖M(t)‖² = ∫∫ h(v)h(v') e^{-it(v-v')}`; integrating against the Gaussian first (Fubini)
replaces the phase by the Fourier transform `gaussFT`, of modulus `b√π e^{-b²y²/4}` (`norm_gaussFT`)
and total mass `2π` (`integral_gaussK`).  Then `|h(v)h(v')| ≤ (h(v)² + h(v')²)/2` and the symmetry of
the kernel give the bound (Schur's test).
-/

open MeasureTheory Set Complex
open scoped ComplexConjugate

noncomputable section

namespace HTGeometry.GaussianLaplace

/-- The Gaussian weight `e^{-((t-a)/b)²}`. -/
def gaussW (a b t : ℝ) : ℝ := Real.exp (-((t - a) / b) ^ 2)

/-- Its Fourier transform `∫ e^{-((t-a)/b)²} e^{-ity} dt`. -/
def gaussFT (a b y : ℝ) : ℂ := ∫ t : ℝ, (gaussW a b t : ℂ) * cexp (-(t * y * I))

/-- The modulus of the Gaussian Fourier transform, `b √π e^{-b²y²/4}`. -/
def gaussK (b y : ℝ) : ℝ := b * Real.sqrt Real.pi * Real.exp (-(b ^ 2 / 4) * y ^ 2)

theorem gaussFT_eq {a b : ℝ} (hb : 0 < b) (y : ℝ) :
    gaussFT a b y = ((Real.pi * b ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      cexp (-(a * y) * I - (b ^ 2 / 4 : ℝ) * y ^ 2) := by
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  set B : ℂ := -((b : ℂ)⁻¹) ^ 2 with hB
  have hBre : B.re < 0 := by
    have : B = ((-(b⁻¹) ^ 2 : ℝ) : ℂ) := by rw [hB]; push_cast; ring
    rw [this, Complex.ofReal_re]
    have : 0 < (b⁻¹) ^ 2 := by positivity
    linarith
  have hpt : ∀ t : ℝ, (gaussW a b t : ℂ) * cexp (-(t * y * I)) =
      cexp (B * t ^ 2 + (2 * a * ((b : ℂ)⁻¹) ^ 2 - y * I) * t + (-(a : ℂ) ^ 2 * ((b : ℂ)⁻¹) ^ 2)) := by
    intro t
    rw [gaussW, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [gaussFT]
  simp_rw [hpt]
  rw [integral_cexp_quadratic hBre]
  congr 1
  · congr 1
    rw [hB]
    push_cast
    field_simp
  · congr 1
    rw [hB]
    field_simp
    push_cast
    linear_combination ((b : ℂ) ^ 4 * (y : ℂ) ^ 2) * Complex.I_sq

theorem norm_gaussFT {a b : ℝ} (hb : 0 < b) (y : ℝ) : ‖gaussFT a b y‖ = gaussK b y := by
  have hpos : 0 < Real.pi * b ^ 2 := by positivity
  have h1 : ‖((Real.pi * b ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)‖ = b * Real.sqrt Real.pi := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    rw [hre, ← Real.sqrt_eq_rpow, Real.sqrt_mul' _ (sq_nonneg b), Real.sqrt_sq hb.le]
    ring
  have h2 : (-((a : ℂ) * y) * I - ((b ^ 2 / 4 : ℝ) : ℂ) * (y : ℂ) ^ 2).re = -(b ^ 2 / 4) * y ^ 2 := by
    have hy : ((y : ℂ) ^ 2) = ((y ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hy, Complex.sub_re]
    have e1 : (-((a : ℂ) * (y : ℂ)) * I).re = 0 := by simp
    have e2 : (((b ^ 2 / 4 : ℝ) : ℂ) * ((y ^ 2 : ℝ) : ℂ)).re = b ^ 2 / 4 * y ^ 2 := by
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    rw [e1, e2]
    ring
  rw [gaussFT_eq hb, norm_mul, Complex.norm_exp, h1, h2, gaussK]

theorem integral_gaussK {b : ℝ} (hb : 0 < b) : ∫ y : ℝ, gaussK b y = 2 * Real.pi := by
  unfold gaussK
  rw [integral_const_mul]
  have := integral_gaussian (b ^ 2 / 4)
  simp only [neg_mul] at this ⊢
  rw [this]
  have h4 : Real.pi / (b ^ 2 / 4) = (2 * Real.sqrt Real.pi / b) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
    field_simp
    ring
  rw [h4, Real.sqrt_sq (by positivity)]
  field_simp
  rw [Real.sq_sqrt Real.pi_pos.le]

theorem integrable_gaussK {b : ℝ} (hb : 0 < b) : Integrable (gaussK b) := by
  unfold gaussK
  exact (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < b ^ 2 / 4)).const_mul
    (b * Real.sqrt Real.pi)


theorem gaussK_nonneg (b y : ℝ) (hb : 0 ≤ b) : 0 ≤ gaussK b y := by
  unfold gaussK; positivity

theorem gaussK_sub_comm (b x y : ℝ) : gaussK b (x - y) = gaussK b (y - x) := by
  unfold gaussK; ring_nf

theorem integrable_gaussW (a : ℝ) {b : ℝ} (hb : 0 < b) : Integrable (gaussW a b) := by
  have h := (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < (b ^ 2)⁻¹)).comp_sub_right a
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [gaussW]
  congr 1
  rw [div_pow]
  field_simp

theorem continuous_gaussW (a b : ℝ) : Continuous (gaussW a b) := by
  unfold gaussW; fun_prop

theorem continuous_gaussK (b : ℝ) : Continuous (gaussK b) := by
  unfold gaussK; fun_prop

/-- Translated tails of `gaussK` integrate to at most `2π`. -/
theorem setIntegral_gaussK_sub_le {b : ℝ} (hb : 0 < b) (x : ℝ) :
    ∫ y in Ioi (0 : ℝ), gaussK b (x - y) ≤ 2 * Real.pi := by
  have hint : Integrable (fun y => gaussK b (x - y)) :=
    (integrable_gaussK hb).comp_sub_left x
  calc ∫ y in Ioi (0 : ℝ), gaussK b (x - y) ≤ ∫ y, gaussK b (x - y) :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun y => gaussK_nonneg b _ hb.le)
    _ = ∫ y, gaussK b y := integral_sub_left_eq_self (gaussK b) volume x
    _ = 2 * Real.pi := integral_gaussK hb

/-- The Fourier–Laplace transform of `h` on `(0, ∞)`. -/
def lapI (h : ℝ → ℝ) (t : ℝ) : ℂ := ∫ v in Ioi (0 : ℝ), (h v : ℂ) * cexp (-(t * v * I))

/-- `‖M(t)‖ ≤ ∫_{v>0} |h|`. -/
theorem norm_lapI_le (h : ℝ → ℝ) (t : ℝ) : ‖lapI h t‖ ≤ ∫ v in Ioi (0 : ℝ), |h v| := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext v
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simp

/-- `M` is continuous (dominated convergence). -/
theorem continuous_lapI {h : ℝ → ℝ} (hmeas : Measurable h) (hh : IntegrableOn h (Ioi 0)) :
    Continuous (lapI h) := by
  refine continuous_of_dominated (bound := fun v => |h v|) (fun t => ?_)
    (fun t => Filter.Eventually.of_forall fun v => ?_) hh.abs
    (Filter.Eventually.of_forall fun v => by fun_prop)
  · exact (by fun_prop : Measurable fun v : ℝ => (h v : ℂ) * cexp (-(t * v * I))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp

section Schur

variable {h : ℝ → ℝ}

local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

theorem normSq_lapI_eq (h : ℝ → ℝ) (t : ℝ) :
    ‖lapI h t‖ ^ 2 = (∫ z, ((h z.1 * h z.2 : ℝ) : ℂ) *
      cexp (-(t * ((z.1 - z.2 : ℝ) : ℂ) * I)) ∂(μ₊.prod μ₊)).re := by
  have hconj : conj (lapI h t) = ∫ v in Ioi (0 : ℝ), (h v : ℂ) * cexp (t * v * I) := by
    rw [lapI, ← integral_conj]
    congr 1
    funext v
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hprod : lapI h t * conj (lapI h t) = ∫ z, ((h z.1 * h z.2 : ℝ) : ℂ) *
      cexp (-(t * ((z.1 - z.2 : ℝ) : ℂ) * I)) ∂(μ₊.prod μ₊) := by
    rw [hconj, lapI, ← integral_prod_mul]
    congr 1
    funext z
    push_cast
    rw [show (h z.1 : ℂ) * cexp (-(t * z.1 * I)) * ((h z.2 : ℂ) * cexp (t * z.2 * I)) =
      (h z.1 : ℂ) * h z.2 * (cexp (-(t * z.1 * I)) * cexp (t * z.2 * I)) by ring,
      ← Complex.exp_add]
    congr 2
    ring
  rw [← hprod, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem integrable_abs_mul_prod (hh : IntegrableOn h (Ioi 0)) :
    Integrable (fun z : ℝ × ℝ => |h z.1 * h z.2|) (μ₊.prod μ₊) := by
  have := (hh.abs).mul_prod (hh.abs)
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp [abs_mul]

/-- **Weighted Plancherel bound.** For `h` integrable and square integrable on `(0, ∞)`,
`∫ e^{-((t-a)/b)²} ‖∫_{v>0} h(v) e^{-itv} dv‖² dt ≤ 2π ∫_{v>0} h(v)²`, uniformly in `a` and `b`. -/
theorem integral_gaussW_mul_normSq_lapI_le (hmeas : Measurable h) (hh : IntegrableOn h (Ioi 0))
    (hh2 : IntegrableOn (fun v => h v ^ 2) (Ioi 0)) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ t, gaussW a b t * ‖lapI h t‖ ^ 2 ≤ 2 * Real.pi * ∫ v in Ioi (0 : ℝ), h v ^ 2 := by
  set F : ℝ → ℝ × ℝ → ℂ := fun t z => (gaussW a b t : ℂ) * (((h z.1 * h z.2 : ℝ) : ℂ) *
    cexp (-(t * ((z.1 - z.2 : ℝ) : ℂ) * I))) with hF
  have hFmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod (μ₊.prod μ₊)) := by
    apply Measurable.aestronglyMeasurable
    simp only [hF, gaussW]
    fun_prop
  have hFint : Integrable (Function.uncurry F) (volume.prod (μ₊.prod μ₊)) := by
    have hmaj := (integrable_gaussW a hb).mul_prod (integrable_abs_mul_prod hh)
    refine hmaj.mono' hFmeas (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hF, norm_mul, Complex.norm_real, Complex.norm_exp]
    have hw : 0 ≤ gaussW a b p.1 := (Real.exp_pos _).le
    simp [abs_of_nonneg hw, Real.norm_eq_abs, abs_mul]
  -- the left side as the real part of an iterated integral
  have hleft : ∫ t, gaussW a b t * ‖lapI h t‖ ^ 2 = (∫ t, ∫ z, F t z ∂(μ₊.prod μ₊)).re := by
    have hre := integral_re hFint.integral_prod_left
    simp only [Function.uncurry_apply_pair, RCLike.re_to_complex] at hre
    rw [← hre]
    congr 1
    funext t
    rw [normSq_lapI_eq, hF]
    simp only
    rw [integral_const_mul, Complex.re_ofReal_mul]
  have hswap : (∫ t, ∫ z, F t z ∂(μ₊.prod μ₊)) = ∫ z, (∫ t, F t z) ∂(μ₊.prod μ₊) :=
    integral_integral_swap hFint
  have hinner : ∀ z : ℝ × ℝ, (∫ t, F t z) = ((h z.1 * h z.2 : ℝ) : ℂ) * gaussFT a b (z.1 - z.2) := by
    intro z
    simp only [hF, gaussFT]
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  -- measurability and integrability of the Schur majorants
  have hKmeas : Measurable fun z : ℝ × ℝ => gaussK b (z.1 - z.2) :=
    (continuous_gaussK b).measurable.comp (measurable_fst.sub measurable_snd)
  have hf1meas : AEStronglyMeasurable (fun z : ℝ × ℝ => h z.1 ^ 2 * gaussK b (z.1 - z.2))
      (μ₊.prod μ₊) :=
    ((hmeas.comp measurable_fst).pow_const 2 |>.mul hKmeas).aestronglyMeasurable
  have hf1 : Integrable (fun z : ℝ × ℝ => h z.1 ^ 2 * gaussK b (z.1 - z.2)) (μ₊.prod μ₊) := by
    rw [integrable_prod_iff hf1meas]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · exact (((integrable_gaussK hb).comp_sub_left x).const_mul (h x ^ 2)).integrableOn
    · refine (hh2.mul_const (2 * Real.pi)).mono' hf1meas.norm.integral_prod_right'
        (Filter.Eventually.of_forall fun x => ?_)
      have hn : ∀ y, ‖h x ^ 2 * gaussK b (x - y)‖ = h x ^ 2 * gaussK b (x - y) := fun y =>
        by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
          (gaussK_nonneg b _ hb.le))]
      simp_rw [hn]
      rw [integral_const_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Ioi fun y _ => gaussK_nonneg b _ hb.le))]
      exact mul_le_mul_of_nonneg_left (setIntegral_gaussK_sub_le hb x) (sq_nonneg _)
  have hf2 : Integrable (fun z : ℝ × ℝ => h z.2 ^ 2 * gaussK b (z.1 - z.2)) (μ₊.prod μ₊) := by
    refine hf1.swap.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp, Prod.fst_swap, Prod.snd_swap]
    rw [gaussK_sub_comm]
  have hK_le : ∀ y, gaussK b y ≤ b * Real.sqrt Real.pi := fun y => by
    unfold gaussK
    have : Real.exp (-(b ^ 2 / 4) * y ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := sq_nonneg y; have := sq_nonneg b; nlinarith)
    have h0 : 0 ≤ b * Real.sqrt Real.pi := by positivity
    nlinarith
  have hg : Integrable (fun z : ℝ × ℝ => |h z.1 * h z.2| * gaussK b (z.1 - z.2)) (μ₊.prod μ₊) := by
    refine ((integrable_abs_mul_prod hh).mul_const (b * Real.sqrt Real.pi)).mono'
      ((continuous_abs.measurable.comp ((hmeas.comp measurable_fst).mul
        (hmeas.comp measurable_snd))).mul hKmeas).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (gaussK_nonneg b _ hb.le))]
    exact mul_le_mul_of_nonneg_left (hK_le _) (abs_nonneg _)
  rw [hleft, hswap]
  have hcongr : (∫ z, (∫ t, F t z) ∂(μ₊.prod μ₊)) =
      ∫ z, ((h z.1 * h z.2 : ℝ) : ℂ) * gaussFT a b (z.1 - z.2) ∂(μ₊.prod μ₊) :=
    integral_congr_ae (Filter.Eventually.of_forall hinner)
  rw [hcongr]
  calc (∫ z, ((h z.1 * h z.2 : ℝ) : ℂ) * gaussFT a b (z.1 - z.2) ∂(μ₊.prod μ₊)).re
      ≤ ‖∫ z, ((h z.1 * h z.2 : ℝ) : ℂ) * gaussFT a b (z.1 - z.2) ∂(μ₊.prod μ₊)‖ :=
        Complex.re_le_norm _
    _ ≤ ∫ z, ‖((h z.1 * h z.2 : ℝ) : ℂ) * gaussFT a b (z.1 - z.2)‖ ∂(μ₊.prod μ₊) :=
        norm_integral_le_integral_norm _
    _ = ∫ z, |h z.1 * h z.2| * gaussK b (z.1 - z.2) ∂(μ₊.prod μ₊) := by
        congr 1
        funext z
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gaussFT hb]
    _ ≤ ∫ z, (h z.1 ^ 2 * gaussK b (z.1 - z.2) + h z.2 ^ 2 * gaussK b (z.1 - z.2)) / 2
          ∂(μ₊.prod μ₊) := by
        refine integral_mono hg ((hf1.add hf2).div_const 2) fun z => ?_
        have hK := gaussK_nonneg b (z.1 - z.2) hb.le
        have hab : |h z.1 * h z.2| ≤ (h z.1 ^ 2 + h z.2 ^ 2) / 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|h z.1| - |h z.2|), sq_abs (h z.1), sq_abs (h z.2)]
        have := mul_le_mul_of_nonneg_right hab hK
        linarith
    _ = ∫ z, h z.1 ^ 2 * gaussK b (z.1 - z.2) ∂(μ₊.prod μ₊) := by
        rw [integral_div, integral_add hf1 hf2]
        have hsym : ∫ z, h z.2 ^ 2 * gaussK b (z.1 - z.2) ∂(μ₊.prod μ₊) =
            ∫ z, h z.1 ^ 2 * gaussK b (z.1 - z.2) ∂(μ₊.prod μ₊) := by
          rw [← integral_prod_swap]
          congr 1
          funext z
          simp only [Prod.fst_swap, Prod.snd_swap]
          rw [gaussK_sub_comm]
        rw [hsym]
        ring
    _ = ∫ x in Ioi (0 : ℝ), h x ^ 2 * ∫ y in Ioi (0 : ℝ), gaussK b (x - y) := by
        rw [integral_prod _ hf1]
        congr 1
        funext x
        simp only
        rw [integral_const_mul]
    _ ≤ ∫ x in Ioi (0 : ℝ), h x ^ 2 * (2 * Real.pi) := by
        refine integral_mono ?_ (hh2.mul_const _) fun x => ?_
        · refine (hf1.integral_prod_left).congr (Filter.Eventually.of_forall fun x => ?_)
          simp only
          rw [integral_const_mul]
        · exact mul_le_mul_of_nonneg_left (setIntegral_gaussK_sub_le hb x) (sq_nonneg _)
    _ = 2 * Real.pi * ∫ v in Ioi (0 : ℝ), h v ^ 2 := by
        rw [integral_mul_const]
        ring

end Schur

end HTGeometry.GaussianLaplace
