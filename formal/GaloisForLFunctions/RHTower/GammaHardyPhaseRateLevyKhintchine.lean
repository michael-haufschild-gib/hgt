import GaloisForLFunctions.RHTower.HardyZ
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianDigammaGauss
import GaloisForLFunctions.RHTower.RiemannKernelStripHomogeneous

/-!
# The Lévy–Khintchine form of the archimedean Weil symbol

Let `θ'(τ) = gammaHardyPhaseRate τ = ½ Re ψ(¼ + iτ/2) − ½ log π` and
`ω(x) = e^{−x/2}/(1 − e^{−2x})` (`archLevyDensity`), a positive density on `(0, ∞)` with
`ω(x) ~ 1/(2x)` at `0`.

**Symbol** (`gammaHardyPhaseRate_sub_zero_eq_integral`).
`θ'(τ) − θ'(0) = ∫_0^∞ ω(x)(1 − cos τx) dx`. This is the Gauss integral for the vertical digamma
difference at `¼` after the substitution `t = 2x`. The kernel is integrable for every `τ`
(`integrableOn_archLevyDensity_mul_one_sub_cos`): its Lebesgue integral is the convergent
series `Σ_j (1/(¼+j) − (¼+j)/((¼+j)² + τ²/4))` (`lintegral_gaussDigammaKernel`).

**Dirichlet form** (`lintegral_archSymbol_mul_normSq_fourier`). For `g ∈ L¹ ∩ L²`,
`∫ 2(θ'(2πξ) − θ'(0)) |𝓕g(ξ)|² dξ = ∫_0^∞ ω(x) ‖g − g(· + x)‖₂² dx` in `[0, ∞]`.
Since `|𝓕(g − g(· + x))(ξ)|² = 2(1 − cos 2πξx)|𝓕g(ξ)|²`, this is Tonelli plus Plancherel.
Whenever `θ'(2πξ)|𝓕g(ξ)|²` is integrable, the archimedean form splits as
`∫ 2θ'(2πξ)|𝓕g|² = 2θ'(0)‖g‖² + ∫_0^∞ ω(x)‖g − g(· + x)‖² dx`
(`integral_archSymbol_mul_normSq_fourier_eq`). The second term equals
`½∫∫ |g(u) − g(v)|² ω(|u − v|) du dv`, so the archimedean form is a negative constant
(`θ'(0) < 0`) plus a jump-type Dirichlet form with jump density `ω`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform
open Zeta23

namespace RHTower

noncomputable section

/-- The Lévy density `ω(x) = e^{−x/2}/(1 − e^{−2x})` of the archimedean symbol. -/
def archLevyDensity (x : ℝ) : ℝ := Real.exp (-x / 2) / (1 - Real.exp (-2 * x))

theorem archLevyDensity_pos {x : ℝ} (hx : 0 < x) : 0 < archLevyDensity x := by
  unfold archLevyDensity
  have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact div_pos (Real.exp_pos _) (by linarith)

theorem measurable_archLevyDensity : Measurable archLevyDensity := by
  unfold archLevyDensity; fun_prop

/-- The Gauss kernel `e^{−at}(1 − e^{−t})^{−1}(1 − cos bt)` as a geometric series. -/
theorem hasSum_gaussDigammaKernel (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun j : ℕ => Real.exp (-(a + j) * t) * (1 - Real.cos (b * t)))
      (Real.exp (-a * t) / (1 - Real.exp (-t)) * (1 - Real.cos (b * t))) := by
  have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo := (hasSum_geometric_of_lt_one (Real.exp_pos (-t)).le hq1).mul_left
    (Real.exp (-a * t) * (1 - Real.cos (b * t)))
  have hval : Real.exp (-a * t) / (1 - Real.exp (-t)) * (1 - Real.cos (b * t)) =
      Real.exp (-a * t) * (1 - Real.cos (b * t)) * (1 - Real.exp (-t))⁻¹ := by
    rw [div_eq_mul_inv]; ring
  rw [hval]
  refine HasSum.congr_fun hgeo fun j => ?_
  rw [show -(a + j) * t = -a * t + j * (-t) by ring, Real.exp_add, Real.exp_nat_mul]
  ring

theorem gaussDigammaKernel_term_nonneg (a b : ℝ) (j : ℕ) (t : ℝ) :
    0 ≤ Real.exp (-(a + j) * t) * (1 - Real.cos (b * t)) :=
  mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.cos_le_one _))

/-- **The Gauss integral as a Lebesgue integral.** For `a > 0`,
`∫_0^∞ e^{−at}(1 − e^{−t})^{−1}(1 − cos bt) dt = Re ψ(a + ib) − ψ(a)` in `[0, ∞]`. -/
theorem lintegral_gaussDigammaKernel {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
        (Real.exp (-a * t) / (1 - Real.exp (-t)) * (1 - Real.cos (b * t))) =
      ENNReal.ofReal ((digamma ((a : ℂ) + (b : ℂ) * I)).re - (digamma (a : ℂ)).re) := by
  have hterms := Complex.hasSum_digammaRealDifferenceTerm ha b
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
        (Real.exp (-a * t) / (1 - Real.exp (-t)) * (1 - Real.cos (b * t)))
      = ∫⁻ t in Ioi (0 : ℝ), ∑' j : ℕ,
          ENNReal.ofReal (Real.exp (-(a + j) * t) * (1 - Real.cos (b * t))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => gaussDigammaKernel_term_nonneg a b j t)
          (hasSum_gaussDigammaKernel a b ht).summable, (hasSum_gaussDigammaKernel a b ht).tsum_eq]
    _ = ∑' j : ℕ, ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(a + j) * t) * (1 - Real.cos (b * t))) :=
        lintegral_tsum fun j => (by fun_prop : Measurable fun t : ℝ =>
          ENNReal.ofReal (Real.exp (-(a + j) * t) * (1 - Real.cos (b * t)))).aemeasurable
    _ = ∑' j : ℕ, ENNReal.ofReal (Complex.digammaRealDifferenceTerm a b j) := by
        refine tsum_congr fun j => ?_
        rw [Complex.digammaRealDifferenceTerm_eq_integral ha b j,
          ofReal_integral_eq_lintegral_ofReal
            (Complex.integrableOn_exp_neg_mul_one_sub_cos
              (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)) b)
            (Eventually.of_forall (gaussDigammaKernel_term_nonneg a b j))]
    _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (Complex.digammaRealDifferenceTerm_nonneg ha b)
          hterms.summable, hterms.tsum_eq]

theorem integrableOn_gaussDigammaKernel {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) / (1 - Real.exp (-t)) * (1 - Real.cos (b * t)))
      (Ioi 0) := by
  refine ⟨(by fun_prop : Measurable fun t : ℝ =>
    Real.exp (-a * t) / (1 - Real.exp (-t)) * (1 - Real.cos (b * t))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal, lintegral_gaussDigammaKernel ha b]
  · exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith [mem_Ioi.mp ht])
    exact mul_nonneg (div_nonneg (Real.exp_pos _).le (by linarith))
      (sub_nonneg.mpr (Real.cos_le_one _))

theorem archLevyDensity_mul_one_sub_cos_eq (τ x : ℝ) :
    archLevyDensity x * (1 - Real.cos (τ * x)) =
      Real.exp (-(1 / 4) * (2 * x)) / (1 - Real.exp (-(2 * x))) *
        (1 - Real.cos (τ / 2 * (2 * x))) := by
  rw [archLevyDensity, show -(1 / 4 : ℝ) * (2 * x) = -x / 2 by ring,
    show -(2 * x) = -2 * x by ring, show τ / 2 * (2 * x) = τ * x by ring]

theorem integrableOn_archLevyDensity_mul_one_sub_cos (τ : ℝ) :
    IntegrableOn (fun x => archLevyDensity x * (1 - Real.cos (τ * x))) (Ioi 0) := by
  have h := integrableOn_gaussDigammaKernel (a := 1 / 4) (by norm_num) (τ / 2)
  rw [← integrable_indicator_iff measurableSet_Ioi] at h ⊢
  refine (h.comp_mul_left' (R := 2) two_ne_zero).congr (Eventually.of_forall fun x => ?_)
  simp only [Set.indicator_apply, mem_Ioi]
  split_ifs with h1 h2 h2
  · exact (archLevyDensity_mul_one_sub_cos_eq τ x).symm
  · exact absurd (by linarith : (0 : ℝ) < x) h2
  · exact absurd (by linarith : (0 : ℝ) < 2 * x) h1
  · rfl

theorem linePt_div_two (τ : ℝ) :
    linePt τ / 2 = ((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
  rw [linePt]; push_cast; ring

/-- **The Lévy–Khintchine form of the archimedean symbol.**
`θ'(τ) − θ'(0) = ∫_0^∞ ω(x)(1 − cos τx) dx`. -/
theorem gammaHardyPhaseRate_sub_zero_eq_integral (τ : ℝ) :
    gammaHardyPhaseRate τ - gammaHardyPhaseRate 0 =
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * (1 - Real.cos (τ * x)) := by
  have h := Complex.digamma_real_vertical_difference_eq_gauss_integral
    (a := 1 / 4) (by norm_num) (τ / 2)
  have e0 : linePt 0 / 2 = ((1 / 4 : ℝ) : ℂ) := by rw [linePt_div_two]; simp
  have hdiff : gammaHardyPhaseRate τ - gammaHardyPhaseRate 0 =
      ((Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re -
        (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re) / 2 := by
    rw [gammaHardyPhaseRate, gammaHardyPhaseRate, linePt_div_two, e0]
    ring
  rw [hdiff, h]
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi
    (fun t : ℝ => Real.exp (-(1 / 4 : ℝ) * t) / (1 - Real.exp (-t)) *
      (1 - Real.cos (τ / 2 * t))) 0 (b := 2) two_pos
  simp only [mul_zero, smul_eq_mul, ← archLevyDensity_mul_one_sub_cos_eq] at hsub
  rw [hsub]
  ring

theorem ofReal_gammaHardyPhaseRate_sub_zero (τ : ℝ) :
    ENNReal.ofReal (gammaHardyPhaseRate τ - gammaHardyPhaseRate 0) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x * (1 - Real.cos (τ * x))) := by
  rw [gammaHardyPhaseRate_sub_zero_eq_integral,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_archLevyDensity_mul_one_sub_cos τ)]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (archLevyDensity_pos hx).le (sub_nonneg.mpr (Real.cos_le_one _))

/-- The symbol is nondecreasing away from its minimum at `0`. -/
theorem gammaHardyPhaseRate_zero_le_levy (τ : ℝ) : gammaHardyPhaseRate 0 ≤ gammaHardyPhaseRate τ := by
  have := gammaHardyPhaseRate_sub_zero_eq_integral τ
  have h0 : 0 ≤ ∫ x in Ioi (0 : ℝ), archLevyDensity x * (1 - Real.cos (τ * x)) :=
    setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (archLevyDensity_pos hx).le (sub_nonneg.mpr (Real.cos_le_one _))
  linarith


theorem norm_one_sub_cexp_ofReal_mul_I_sq (θ : ℝ) :
    ‖1 - cexp ((θ : ℂ) * I)‖ ^ 2 = 2 * (1 - Real.cos θ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  linear_combination Real.sin_sq_add_cos_sq θ

/-- The paper transform of a difference with a translate. -/
theorem paperFT_sub_comp_add_right {g : ℝ → ℂ} (hg : Integrable g) (x ξ : ℝ) :
    paperFT (fun u => g u - g (u + x)) ξ = (1 - cexp (((-(ξ * x) : ℝ) : ℂ) * I)) * paperFT g ξ := by
  have h1 := KernelStrip.integrable_mul_cexp_I_mul hg ξ
  have h2 := KernelStrip.integrable_mul_cexp_I_mul (hg.comp_add_right x) ξ
  have htr : ∫ u : ℝ, g (u + x) * cexp (I * ξ * u) =
      cexp (((-(ξ * x) : ℝ) : ℂ) * I) * paperFT g ξ := by
    have := integral_add_right_eq_self (μ := volume)
      (fun v : ℝ => g v * cexp (I * ξ * ((v - x : ℝ) : ℂ))) x
    simp only [add_sub_cancel_right] at this
    rw [this]
    show _ = _ * ∫ u : ℝ, g u * cexp (I * (ξ : ℂ) * u)
    rw [← integral_const_mul]
    congr 1 with v
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  show ∫ u : ℝ, (g u - g (u + x)) * cexp (I * (ξ : ℂ) * u) = _
  simp only [sub_mul]
  rw [integral_sub h1 h2, htr]
  rw [one_mul]
  rfl

theorem fourier_eq_paperFT_neg_two_pi_mul (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = paperFT f ((-(2 * Real.pi * ξ) : ℝ) : ℂ) := by
  rw [paperFT_ofReal_eq_fourier]
  field_simp

/-- `|𝓕(g − g(· + x))(ξ)|² = 2(1 − cos 2πξx)|𝓕g(ξ)|²`. -/
theorem norm_sq_fourier_sub_comp_add_right {g : ℝ → ℂ} (hg : Integrable g) (x ξ : ℝ) :
    ‖𝓕 (fun u => g u - g (u + x)) ξ‖ ^ 2 =
      2 * (1 - Real.cos (2 * Real.pi * ξ * x)) * ‖𝓕 g ξ‖ ^ 2 := by
  rw [fourier_eq_paperFT_neg_two_pi_mul, fourier_eq_paperFT_neg_two_pi_mul g, paperFT_sub_comp_add_right hg, norm_mul, mul_pow,
    norm_one_sub_cexp_ofReal_mul_I_sq, show -(-(2 * Real.pi * ξ) * x) = 2 * Real.pi * ξ * x by ring]

/-- **The archimedean form as a Dirichlet form.** For `g ∈ L¹ ∩ L²`,
`∫ 2(θ'(2πξ) − θ'(0))|𝓕g(ξ)|² dξ = ∫_0^∞ ω(x)‖g − g(· + x)‖₂² dx` in `[0, ∞]`. -/
theorem lintegral_archSymbol_mul_normSq_fourier {g : ℝ → ℂ} (hg1 : Integrable g)
    (hg2 : MemLp g 2) :
    ∫⁻ ξ : ℝ, ENNReal.ofReal
        (2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) * ‖𝓕 g ξ‖ ^ 2) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖g u - g (u + x)‖ ^ 2) := by
  have hcont : Continuous (𝓕 g) := GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hg1
  have step1 : ∀ ξ : ℝ, ENNReal.ofReal
      (2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) * ‖𝓕 g ξ‖ ^ 2) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
        (archLevyDensity x * (2 * (1 - Real.cos (2 * Real.pi * ξ * x)) * ‖𝓕 g ξ‖ ^ 2)) := by
    intro ξ
    rw [show 2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) * ‖𝓕 g ξ‖ ^ 2 =
        (2 * ‖𝓕 g ξ‖ ^ 2) * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) by ring,
      ENNReal.ofReal_mul (by positivity), ofReal_gammaHardyPhaseRate_sub_zero,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hmeas : AEMeasurable (Function.uncurry fun (ξ x : ℝ) => ENNReal.ofReal
      (archLevyDensity x * (2 * (1 - Real.cos (2 * Real.pi * ξ * x)) * ‖𝓕 g ξ‖ ^ 2)))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aemeasurable ?_
    show Measurable fun p : ℝ × ℝ => ENNReal.ofReal
      (archLevyDensity p.2 * (2 * (1 - Real.cos (2 * Real.pi * p.1 * p.2)) * ‖𝓕 g p.1‖ ^ 2))
    refine Measurable.ennreal_ofReal ((measurable_archLevyDensity.comp measurable_snd).mul ?_)
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
      2 * (1 - Real.cos (2 * Real.pi * p.1 * p.2))).mul
        ((hcont.norm.pow 2).comp continuous_fst)).measurable
  rw [lintegral_congr step1, lintegral_lintegral_swap hmeas]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hω := (archLevyDensity_pos (mem_Ioi.mp hx)).le
  have hD1 : Integrable (fun u => g u - g (u + x)) := hg1.sub (hg1.comp_add_right x)
  have hD2 : MemLp (fun u => g u - g (u + x)) 2 :=
    hg2.sub (hg2.comp_measurePreserving (measurePreserving_add_right volume x))
  calc ∫⁻ ξ : ℝ, ENNReal.ofReal
        (archLevyDensity x * (2 * (1 - Real.cos (2 * Real.pi * ξ * x)) * ‖𝓕 g ξ‖ ^ 2))
      = ∫⁻ ξ : ℝ, ENNReal.ofReal (archLevyDensity x) *
          ENNReal.ofReal (‖𝓕 (fun u => g u - g (u + x)) ξ‖ ^ 2) := by
        refine lintegral_congr fun ξ => ?_
        rw [← ENNReal.ofReal_mul hω, norm_sq_fourier_sub_comp_add_right hg1]
    _ = ENNReal.ofReal (archLevyDensity x) *
          ENNReal.ofReal (∫ ξ : ℝ, ‖𝓕 (fun u => g u - g (u + x)) ξ‖ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ofReal_integral_eq_lintegral_ofReal
          (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hD1 hD2)
          (Eventually.of_forall fun _ => by positivity)]
    _ = _ := by
        rw [GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hD1 hD2,
          ← ENNReal.ofReal_mul hω]


theorem integrable_archSymbol_sub_zero_mul_normSq_fourier {g : ℝ → ℂ} (hg1 : Integrable g)
    (hg2 : MemLp g 2)
    (hint : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 g ξ‖ ^ 2) :
    Integrable fun ξ : ℝ =>
      2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) * ‖𝓕 g ξ‖ ^ 2 :=
  ((hint.sub ((GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hg1 hg2).const_mul
    (gammaHardyPhaseRate 0))).const_mul 2).congr (Eventually.of_forall fun ξ => by
      simp only [Pi.sub_apply]; ring)

/-- The jump energy `∫_0^∞ ω(x)‖g − g(· + x)‖² dx` is finite as soon as the archimedean
form of `g` converges absolutely. -/
theorem lintegral_archLevyDirichlet_ne_top {g : ℝ → ℂ} (hg1 : Integrable g) (hg2 : MemLp g 2)
    (hint : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 g ξ‖ ^ 2) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖g u - g (u + x)‖ ^ 2) ≠
      ⊤ := by
  rw [← lintegral_archSymbol_mul_normSq_fourier hg1 hg2, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_archSymbol_sub_zero_mul_normSq_fourier hg1 hg2 hint)
    (Eventually.of_forall fun ξ => mul_nonneg (mul_nonneg two_pos.le
      (sub_nonneg.mpr (gammaHardyPhaseRate_zero_le_levy _))) (sq_nonneg _))]
  exact ENNReal.ofReal_ne_top

/-- **Splitting of the archimedean form.** If `θ'(2πξ)|𝓕g(ξ)|²` is integrable, then
`∫ 2θ'(2πξ)|𝓕g(ξ)|² dξ = 2θ'(0)‖g‖₂² + ∫_0^∞ ω(x)‖g − g(· + x)‖₂² dx`. -/
theorem integral_archSymbol_mul_normSq_fourier_eq {g : ℝ → ℂ} (hg1 : Integrable g)
    (hg2 : MemLp g 2)
    (hint : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 g ξ‖ ^ 2) :
    ∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 g ξ‖ ^ 2 =
      2 * gammaHardyPhaseRate 0 * (∫ u : ℝ, ‖g u‖ ^ 2) +
        (∫⁻ x in Ioi (0 : ℝ),
          ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖g u - g (u + x)‖ ^ 2)).toReal := by
  have hF := GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hg1 hg2
  have hd := integrable_archSymbol_sub_zero_mul_normSq_fourier hg1 hg2 hint
  have hnn : ∀ ξ : ℝ, 0 ≤
      2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) - gammaHardyPhaseRate 0) * ‖𝓕 g ξ‖ ^ 2 :=
    fun ξ => mul_nonneg (mul_nonneg two_pos.le
      (sub_nonneg.mpr (gammaHardyPhaseRate_zero_le_levy _))) (sq_nonneg _)
  have hL := lintegral_archSymbol_mul_normSq_fourier hg1 hg2
  rw [← ofReal_integral_eq_lintegral_ofReal hd (Eventually.of_forall hnn)] at hL
  rw [← hL, ENNReal.toReal_ofReal (integral_nonneg hnn),
    ← GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hg1 hg2, ← integral_const_mul,
    ← integral_add (hF.const_mul _) hd]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  ring

end

end RHTower
