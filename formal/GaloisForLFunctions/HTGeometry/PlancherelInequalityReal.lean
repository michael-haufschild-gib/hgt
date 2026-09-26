import Mathlib

/-!
# The Plancherel inequality on the real line

For continuous `g : ℝ → ℂ` with `g` and `|g|²` integrable, the angular Fourier transform
`Ĝ(t) = ∫ e^{its} g(s) ds` satisfies

  `∫ |Ĝ(t)|² dt ≤ 2π ∫ |g|²`.

Gaussian regularization: `∫ |Ĝ(t)|² e^{-εt²} dt = ∫∫ g(x) ḡ(y) K_ε(x - y) dx dy` with the positive kernel
`K_ε(u) = √(π/ε) e^{-u²/(4ε)}` of mass `2π`; the bound `|g(x)||g(y)| ≤ (|g(x)|² + |g(y)|²)/2` gives
`≤ 2π ∫|g|²` for every `ε`, and monotone convergence lets `ε → 0`.
-/

open Complex Real MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The angular Fourier transform `Ĝ(t) = ∫ e^{its} g(s) ds`. -/
def angularFourier (g : ℝ → ℂ) (t : ℝ) : ℂ := ∫ s : ℝ, Complex.exp (I * t * s) * g s

/-- The Gaussian kernel `K_ε(u) = √(π/ε) e^{-u²/(4ε)}`. -/
def gaussKernel (ε u : ℝ) : ℝ := Real.sqrt (π / ε) * Real.exp (-(1 / (4 * ε)) * u ^ 2)

theorem gaussKernel_nonneg (ε u : ℝ) : 0 ≤ gaussKernel ε u := by unfold gaussKernel; positivity

theorem integrable_gaussKernel {ε : ℝ} (hε : 0 < ε) : Integrable (gaussKernel ε) :=
  (integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * ε))).const_mul _

theorem integral_gaussKernel {ε : ℝ} (hε : 0 < ε) : ∫ u, gaussKernel ε u = 2 * π := by
  unfold gaussKernel
  rw [integral_const_mul, integral_gaussian, ← Real.sqrt_mul (by positivity)]
  have : π / ε * (π / (1 / (4 * ε))) = (2 * π) ^ 2 := by field_simp; ring
  rw [this, Real.sqrt_sq (by positivity)]

/-- The Gaussian Fourier integral. -/
theorem integral_exp_I_mul_gauss {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    ∫ t : ℝ, Complex.exp (I * t * u) * ((Real.exp (-ε * t ^ 2) : ℝ) : ℂ) = (gaussKernel ε u : ℂ) := by
  have h := integral_cexp_quadratic (b := -(ε : ℂ)) (by simp [hε]) (I * u) 0
  have hcongr : ∀ t : ℝ, Complex.exp (I * t * u) * ((Real.exp (-ε * t ^ 2) : ℝ) : ℂ) =
      Complex.exp (-(ε : ℂ) * (t : ℂ) ^ 2 + I * u * t + 0) := by
    intro t; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [hcongr]
  rw [h]
  unfold gaussKernel
  have hsq : (↑π / -(-(ε : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt (π / ε) : ℝ) : ℂ) := by
    rw [neg_neg, Real.sqrt_eq_rpow, ← Complex.ofReal_div, Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [hsq]
  push_cast
  congr 1
  congr 1
  rw [mul_pow, Complex.I_sq]
  field_simp
  ring

theorem norm_angularFourier_le (g : ℝ → ℂ) (t : ℝ) : ‖angularFourier g t‖ ≤ ∫ s, ‖g s‖ := by
  unfold angularFourier
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext s
  rw [norm_mul, Complex.norm_exp]; simp

theorem continuous_angularFourier {g : ℝ → ℂ} (hc : Continuous g) (hg : Integrable g) :
    Continuous (angularFourier g) := by
  unfold angularFourier
  refine continuous_of_dominated (bound := fun s => ‖g s‖) (fun t => ?_) (fun t => ?_) hg.norm ?_
  · exact ((by fun_prop : Continuous fun s : ℝ => Complex.exp (I * t * s)).mul hc).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s => by rw [norm_mul, Complex.norm_exp]; simp
  · exact Filter.Eventually.of_forall fun s => by fun_prop

/-- `∫∫ |g(x)|² K(x-y) dx dy = 2π ∫ |g|²`, and its integrability. -/
theorem integrable_sq_mul_gaussKernel {g : ℝ → ℂ} (hc : Continuous g)
    (hg2 : Integrable fun x => ‖g x‖ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℝ × ℝ => ‖g p.1‖ ^ 2 * gaussKernel ε (p.1 - p.2)) (volume.prod volume) := by
  have hKc : Continuous (gaussKernel ε) := by unfold gaussKernel; fun_prop
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖g p.1‖ ^ 2 * gaussKernel ε (p.1 - p.2))
      (volume.prod volume) := by
    exact ((hc.comp continuous_fst).norm.pow 2 |>.mul (hKc.comp (continuous_fst.sub continuous_snd)))
      |>.aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · refine Filter.Eventually.of_forall fun x => ?_
    simpa using ((integrable_gaussKernel hε).comp_sub_left x).const_mul (‖g x‖ ^ 2)
  · have heq : (fun x : ℝ => ∫ y, ‖‖g x‖ ^ 2 * gaussKernel ε (x - y)‖) = fun x => ‖g x‖ ^ 2 * (2 * π) := by
      funext x
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gaussKernel_nonneg _ _))]
      rw [integral_const_mul, integral_sub_left_eq_self (gaussKernel ε) (μ := volume) x,
        integral_gaussKernel hε]
    rw [heq]; exact hg2.mul_const _

theorem integral_sq_mul_gaussKernel {g : ℝ → ℂ} (hc : Continuous g)
    (hg2 : Integrable fun x => ‖g x‖ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, ‖g p.1‖ ^ 2 * gaussKernel ε (p.1 - p.2) = 2 * π * ∫ x, ‖g x‖ ^ 2 := by
  rw [MeasureTheory.Measure.volume_eq_prod, integral_prod _ (integrable_sq_mul_gaussKernel hc hg2 hε)]
  simp_rw [integral_const_mul]
  have : ∀ x : ℝ, ∫ y, gaussKernel ε (x - y) = 2 * π := fun x => by
    rw [integral_sub_left_eq_self (gaussKernel ε) (μ := volume) x, integral_gaussKernel hε]
  simp_rw [this]
  rw [integral_mul_const]; ring

theorem integral_sq_mul_gaussKernel_swap {g : ℝ → ℂ} (hc : Continuous g)
    (hg2 : Integrable fun x => ‖g x‖ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℝ × ℝ, ‖g p.2‖ ^ 2 * gaussKernel ε (p.1 - p.2) = 2 * π * ∫ x, ‖g x‖ ^ 2 := by
  have hsym : ∀ u, gaussKernel ε (-u) = gaussKernel ε u := fun u => by unfold gaussKernel; ring_nf
  rw [MeasureTheory.Measure.volume_eq_prod, ← integral_prod_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  simp_rw [show ∀ p : ℝ × ℝ, gaussKernel ε (p.2 - p.1) = gaussKernel ε (p.1 - p.2) from
    fun p => by rw [← hsym, neg_sub]]
  rw [← MeasureTheory.Measure.volume_eq_prod]
  exact integral_sq_mul_gaussKernel hc hg2 hε

/-- **Regularized Plancherel bound.** -/
theorem integral_norm_sq_angularFourier_gauss_le {g : ℝ → ℂ} (hc : Continuous g) (hg : Integrable g)
    (hg2 : Integrable fun x => ‖g x‖ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∫ t, ‖angularFourier g t‖ ^ 2 * Real.exp (-ε * t ^ 2) ≤ 2 * π * ∫ x, ‖g x‖ ^ 2 := by
  have hGint : Integrable fun t : ℝ => Real.exp (-ε * t ^ 2) := integrable_exp_neg_mul_sq hε
  have hgc : Integrable fun y => (starRingEnd ℂ) (g y) :=
    hg.norm.mono' (Complex.continuous_conj.comp hc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simp)
  set P : ℝ × ℝ → ℂ := fun p => g p.1 * (starRingEnd ℂ) (g p.2) with hP
  have hPint : Integrable P (volume.prod volume) := hg.mul_prod hgc
  have hPc : Continuous P := (hc.comp continuous_fst).mul (Complex.continuous_conj.comp (hc.comp continuous_snd))
  -- `|Ĝ(t)|²` as a double integral
  have hsqrepr : ∀ t : ℝ, ((‖angularFourier g t‖ ^ 2 : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, Complex.exp (I * t * (p.1 - p.2)) * P p := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    unfold angularFourier
    rw [← integral_conj, ← integral_prod_mul]
    congr 1; funext p
    simp only [hP, map_mul, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal]
    have he : Complex.exp (I * t * (p.1 - p.2)) =
        Complex.exp (I * t * p.1) * Complex.exp (-I * t * p.2) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [he]; ring
  -- Fubini in `(t, p)`
  set Q : ℝ × (ℝ × ℝ) → ℂ := fun z =>
    ((Real.exp (-ε * z.1 ^ 2) : ℝ) : ℂ) * (Complex.exp (I * z.1 * (z.2.1 - z.2.2)) * P z.2) with hQ
  have hPint' : Integrable P volume := by rw [MeasureTheory.Measure.volume_eq_prod]; exact hPint
  have hQint : Integrable Q (volume.prod volume) := by
    have hbase : Integrable (fun z : ℝ × (ℝ × ℝ) => ((Real.exp (-ε * z.1 ^ 2) : ℝ) : ℂ) * P z.2)
        (volume.prod volume) := (hGint.ofReal).mul_prod hPint'
    refine hbase.norm.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hQ]
      exact (by fun_prop : Continuous fun z : ℝ × (ℝ × ℝ) => ((Real.exp (-ε * z.1 ^ 2) : ℝ) : ℂ)).mul
        ((by fun_prop : Continuous fun z : ℝ × (ℝ × ℝ) => Complex.exp (I * z.1 * (z.2.1 - z.2.2))).mul
          (hPc.comp continuous_snd))
    · simp only [hQ, norm_mul, Complex.norm_exp]
      simp
  have hlhs : ((∫ t, ‖angularFourier g t‖ ^ 2 * Real.exp (-ε * t ^ 2) : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, (gaussKernel ε (p.1 - p.2) : ℂ) * P p := by
    rw [← integral_complex_ofReal]
    have h1 : ∀ t : ℝ, (((‖angularFourier g t‖ ^ 2 * Real.exp (-ε * t ^ 2)) : ℝ) : ℂ) =
        ∫ p : ℝ × ℝ, Q (t, p) := by
      intro t
      rw [Complex.ofReal_mul, hsqrepr, mul_comm, ← integral_const_mul]
    simp_rw [h1]
    rw [integral_integral_swap (f := fun x p => Q (x, p)) hQint]
    congr 1; funext p
    simp only [hQ]
    have h2 : ∀ t : ℝ, ((Real.exp (-ε * t ^ 2) : ℝ) : ℂ) * (Complex.exp (I * t * (p.1 - p.2)) * P p) =
        (Complex.exp (I * t * ((p.1 - p.2 : ℝ) : ℂ)) * ((Real.exp (-ε * t ^ 2) : ℝ) : ℂ)) * P p := by
      intro t; push_cast; ring
    simp_rw [h2]
    rw [integral_mul_const, integral_exp_I_mul_gauss hε]
  -- bound
  have hbound : ‖∫ p : ℝ × ℝ, (gaussKernel ε (p.1 - p.2) : ℂ) * P p‖ ≤ 2 * π * ∫ x, ‖g x‖ ^ 2 := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ p : ℝ × ℝ, ‖(gaussKernel ε (p.1 - p.2) : ℂ) * P p‖ ≤
        (1 / 2) * (‖g p.1‖ ^ 2 * gaussKernel ε (p.1 - p.2)) +
          (1 / 2) * (‖g p.2‖ ^ 2 * gaussKernel ε (p.1 - p.2)) := by
      intro p
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gaussKernel_nonneg _ _)]
      simp only [hP, norm_mul, RCLike.norm_conj]
      have hK := gaussKernel_nonneg ε (p.1 - p.2)
      nlinarith [sq_nonneg (‖g p.1‖ - ‖g p.2‖), mul_nonneg hK (sq_nonneg (‖g p.1‖ - ‖g p.2‖))]
    have hi1 : Integrable (fun p : ℝ × ℝ => ‖g p.1‖ ^ 2 * gaussKernel ε (p.1 - p.2)) volume := by
      rw [MeasureTheory.Measure.volume_eq_prod]; exact integrable_sq_mul_gaussKernel hc hg2 hε
    have hi2 : Integrable (fun p : ℝ × ℝ => ‖g p.2‖ ^ 2 * gaussKernel ε (p.1 - p.2)) volume := by
      rw [MeasureTheory.Measure.volume_eq_prod]
      have := (integrable_sq_mul_gaussKernel hc hg2 hε).swap
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp, Prod.fst_swap, Prod.snd_swap]
      congr 1; unfold gaussKernel; ring_nf
    calc ∫ p : ℝ × ℝ, ‖(gaussKernel ε (p.1 - p.2) : ℂ) * P p‖
        ≤ ∫ p : ℝ × ℝ, ((1 / 2) * (‖g p.1‖ ^ 2 * gaussKernel ε (p.1 - p.2)) +
          (1 / 2) * (‖g p.2‖ ^ 2 * gaussKernel ε (p.1 - p.2))) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _)
            ((hi1.const_mul _).add (hi2.const_mul _)) (Filter.Eventually.of_forall hpt)
      _ = 2 * π * ∫ x, ‖g x‖ ^ 2 := by
          rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
            integral_sq_mul_gaussKernel hc hg2 hε, integral_sq_mul_gaussKernel_swap hc hg2 hε]
          ring
  have hreal : ∫ t, ‖angularFourier g t‖ ^ 2 * Real.exp (-ε * t ^ 2) =
      ‖((∫ t, ‖angularFourier g t‖ ^ 2 * Real.exp (-ε * t ^ 2) : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => by positivity)]
  rw [hreal, hlhs]
  exact hbound

/-- **Plancherel inequality.** `∫ |Ĝ|² ≤ 2π ∫ |g|²`, in lower-integral form. -/
theorem lintegral_norm_sq_angularFourier_le {g : ℝ → ℂ} (hc : Continuous g) (hg : Integrable g)
    (hg2 : Integrable fun x => ‖g x‖ ^ 2) :
    ∫⁻ t, ENNReal.ofReal (‖angularFourier g t‖ ^ 2) ≤ ENNReal.ofReal (2 * π * ∫ x, ‖g x‖ ^ 2) := by
  set f : ℕ → ℝ → ENNReal := fun n t =>
    ENNReal.ofReal (‖angularFourier g t‖ ^ 2 * Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2)) with hf
  have hcont := continuous_angularFourier hc hg
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := volume) (f := f)
    (F := fun t => ENNReal.ofReal (‖angularFourier g t‖ ^ 2))
    (fun n => (by fun_prop : Continuous fun t : ℝ =>
      ‖angularFourier g t‖ ^ 2 * Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2)).measurable.ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall fun t => by
      intro m n hmn
      simp only [hf]
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Real.exp_le_exp.mpr
      have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      nlinarith [sq_nonneg t])
    (Filter.Eventually.of_forall fun t => by
      simp only [hf]
      refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
      have h0 : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1)) * t ^ 2) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 := h1.neg.mul_const (t ^ 2)
        simpa using h2
      have := (Real.continuous_exp.tendsto 0).comp h0
      rw [Real.exp_zero] at this
      simpa using this.const_mul (‖angularFourier g t‖ ^ 2))
  refine le_of_tendsto' hlim fun n => ?_
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hbound := integral_norm_sq_angularFourier_gauss_le hc hg hg2 hε
  have hint : Integrable fun t : ℝ => ‖angularFourier g t‖ ^ 2 * Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2) := by
    refine ((integrable_exp_neg_mul_sq hε).const_mul ((∫ s, ‖g s‖) ^ 2)).mono'
      (by fun_prop : Continuous fun t : ℝ =>
        ‖angularFourier g t‖ ^ 2 * Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact norm_angularFourier_le g t
  simp only [hf]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => by positivity)]
  exact ENNReal.ofReal_le_ofReal hbound

end

end GaloisForLFunctions.HTGeometry
