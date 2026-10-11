import GaloisForLFunctions.RHTower.XiSliceHeatMomentConcentration
import GaloisForLFunctions.RHTower.XiSliceHeatPerPairPositivity
import GaloisForLFunctions.RHTower.RiemannHeatSliceEvolution
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCriterion

/-!
# Heated slice positivity at all large heights

**Theorem** (`exists_xiSliceHeatTransfer_nonneg_large_height`).  For every `λ > 0` there is `T`
such that `T_n(λ, 0, t) ≥ 0` for every order `n` and every height `|t| ≥ T`: the heated slice
`e^{(λ/2)∂_x²} S_0(t, ·)` has nonnegative Taylor coefficients at all large heights.

This is the slice analogue of the Ki–Kim–Lee theorem.  Proof:

* `T_n(λ, 0, t) = ∫ G_λ(t − t') M_n(t') dt'`, where `M_n(t')` are the slice moments of `H_λ` and `G_λ`
  is the Gaussian of variance `λ` (transfer identity).
* `M_n(t') ≥ 0` for `|t'| ≥ X₀` (Ki–Kim–Lee: the zeros of `H_λ` of large real part are real, and the
  cone criterion applies).
* `|M_{2l}(t')| ≤ M_{2l}(0)` and `Re M_{2l}(t') ≥ M_{2l}(0) − (t'²/2) Q_{2l}`, where `Q_{2l}` is the
  `(u+v)²`-moment of the weight `g_λ(u) g_λ(v) (u−v)^{2l}/(2l)!`.  By concentration
  (`exists_heatKernel_moment_concentration`), `Q_{2l} ≤ M_{2l}(0)/(X₀+1)²` for large `l`, so
  `Re M_{2l} ≥ M_{2l}(0)/2` on the window `[X₀ + ½, X₀ + 1]`.
* Laplace domination: the Gaussian weight of the window beats that of `(−X₀, X₀)` by the factor
  `e^{σ²(t − X₀ − ¼)}`, uniformly in large `l`.  The finitely many small `l` are handled one by one:
  `M_{2l}` is the restriction of an entire function with `M_{2l}(0) > 0`, so it does not vanish on
  the window (`exists_mem_Ioo_kernelSliceMoment_ne_zero`).

**Corollary** (`wdHeatThreshold_lt_twelfth`).  `λ_WD < 1/12`.  Above the height `T` of the theorem
for `λ = 1/24` the heated slices are positive; below it only the finitely many zeros with
`|Re z| ≤ T + ½` can violate the heated cone condition, each with `(Im z)² < 1/4`, so the per-pair law
applies at some `λ < 1/12`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

/-- The weight of the even slice moments of `H_λ`: `g_λ(u) g_λ(v) (u − v)^{2l}/(2l)!`. -/
def momentWeight (lam : ℝ) (l : ℕ) (p : ℝ × ℝ) : ℝ :=
  heatKernel lam p.1 * heatKernel lam p.2 * ((p.1 - p.2) ^ (2 * l) / (2 * l).factorial)

theorem momentWeight_nonneg (lam : ℝ) (l : ℕ) (p : ℝ × ℝ) : 0 ≤ momentWeight lam l p := by
  unfold momentWeight
  have h1 := heatKernel_pos lam p.1
  have h2 := heatKernel_pos lam p.2
  have : 0 ≤ (p.1 - p.2) ^ (2 * l) := by rw [pow_mul]; positivity
  positivity

theorem continuous_momentWeight (lam : ℝ) (l : ℕ) : Continuous (momentWeight lam l) := by
  unfold momentWeight
  have := continuous_heatKernel lam
  fun_prop

theorem integrable_momentWeight {lam : ℝ} (hlam : 0 ≤ lam) (l : ℕ) :
    Integrable (momentWeight lam l) ∧
      Integrable (fun p : ℝ × ℝ => momentWeight lam l p * (p.1 + p.2) ^ 2) := by
  obtain ⟨h1, h2⟩ := integrable_heatKernel_moment hlam l
  refine ⟨(h1.div_const ((2 * l).factorial : ℝ)).congr (Eventually.of_forall fun p => ?_),
    (h2.div_const ((2 * l).factorial : ℝ)).congr (Eventually.of_forall fun p => ?_)⟩
  · simp only [momentWeight]; ring
  · simp only [momentWeight]; ring

theorem kernelSliceMoment_heatKernel_eq (lam t' : ℝ) (l : ℕ) :
    kernelSliceMoment (heatKernel lam) 0 t' (2 * l) =
      ∫ p : ℝ × ℝ, ((momentWeight lam l p : ℝ) : ℂ) * cexp (I * t' * (p.1 + p.2)) := by
  unfold kernelSliceMoment momentWeight
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [zero_mul, Real.exp_zero, mul_one]

theorem integrable_momentWeight_cexp {lam : ℝ} (hlam : 0 ≤ lam) (l : ℕ) (t' : ℝ) :
    Integrable (fun p : ℝ × ℝ => ((momentWeight lam l p : ℝ) : ℂ) * cexp (I * t' * (p.1 + p.2))) := by
  refine (integrable_momentWeight hlam l).1.ofReal.mul_bdd (c := 1) (by fun_prop)
    (Eventually.of_forall fun p => ?_)
  exact le_of_eq (norm_cexp_I_mul_ofReal_add t' p.1 p.2)

/-- `Re M_{2l}(t') = ∫ w cos(t'(u+v))`. -/
theorem re_kernelSliceMoment_heatKernel {lam : ℝ} (hlam : 0 ≤ lam) (t' : ℝ) (l : ℕ) :
    (kernelSliceMoment (heatKernel lam) 0 t' (2 * l)).re =
      ∫ p : ℝ × ℝ, momentWeight lam l p * Real.cos (t' * (p.1 + p.2)) := by
  rw [kernelSliceMoment_heatKernel_eq, ← RCLike.re_to_complex,
    ← integral_re (integrable_momentWeight_cexp hlam l t')]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [RCLike.re_to_complex]
  rw [show I * (t' : ℂ) * ((p.1 : ℂ) + p.2) = ((t' * (p.1 + p.2) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem re_kernelSliceMoment_heatKernel_neg {lam : ℝ} (hlam : 0 ≤ lam) (t' : ℝ) (l : ℕ) :
    (kernelSliceMoment (heatKernel lam) 0 (-t') (2 * l)).re =
      (kernelSliceMoment (heatKernel lam) 0 t' (2 * l)).re := by
  rw [re_kernelSliceMoment_heatKernel hlam, re_kernelSliceMoment_heatKernel hlam]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [neg_mul, Real.cos_neg]

/-- `‖M_{2l}(t')‖ ≤ M_{2l}(0) = ∫ w`. -/
theorem norm_kernelSliceMoment_heatKernel_le {lam : ℝ} (t' : ℝ) (l : ℕ) :
    ‖kernelSliceMoment (heatKernel lam) 0 t' (2 * l)‖ ≤ ∫ p : ℝ × ℝ, momentWeight lam l p := by
  rw [kernelSliceMoment_heatKernel_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add, mul_one,
    abs_of_nonneg (momentWeight_nonneg lam l p)]

/-- `Re M_{2l}(t') ≥ M_{2l}(0) − (t'²/2) Q_{2l}`. -/
theorem re_kernelSliceMoment_heatKernel_ge {lam : ℝ} (hlam : 0 ≤ lam) (t' : ℝ) (l : ℕ) :
    (∫ p : ℝ × ℝ, momentWeight lam l p) -
        t' ^ 2 / 2 * ∫ p : ℝ × ℝ, momentWeight lam l p * (p.1 + p.2) ^ 2 ≤
      (kernelSliceMoment (heatKernel lam) 0 t' (2 * l)).re := by
  obtain ⟨hI, hI2⟩ := integrable_momentWeight hlam l
  rw [re_kernelSliceMoment_heatKernel hlam, ← integral_const_mul, ← integral_sub hI
    (hI2.const_mul _)]
  refine integral_mono (hI.sub (hI2.const_mul _))
    (hI.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)) fun p => ?_
  have hc := Real.one_sub_sq_div_two_le_cos (x := t' * (p.1 + p.2))
  have hw := momentWeight_nonneg lam l p
  have := mul_le_mul_of_nonneg_left hc hw
  nlinarith

theorem continuous_kernelSliceMoment_heatKernel {lam : ℝ} (hlam : 0 ≤ lam) (l : ℕ) :
    Continuous fun t' : ℝ => kernelSliceMoment (heatKernel lam) 0 t' (2 * l) := by
  simp_rw [kernelSliceMoment_heatKernel_eq]
  refine continuous_of_dominated (bound := momentWeight lam l)
    (fun t' => (integrable_momentWeight_cexp hlam l t').aestronglyMeasurable)
    (fun t' => Eventually.of_forall fun p => ?_) (integrable_momentWeight hlam l).1
    (Eventually.of_forall fun p => by fun_prop)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add, mul_one,
    abs_of_nonneg (momentWeight_nonneg lam l p)]

/-- `M_{2l}(0) = ∫ w > 0`. -/
theorem integral_momentWeight_pos {lam : ℝ} (hlam : 0 ≤ lam) (l : ℕ) :
    0 < ∫ p : ℝ × ℝ, momentWeight lam l p := by
  obtain ⟨hI, -⟩ := integrable_momentWeight hlam l
  set B : Set (ℝ × ℝ) := Set.Icc (2 : ℝ) 3 ×ˢ Set.Icc (0 : ℝ) 1 with hB
  obtain ⟨m, hm, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    (show B.Nonempty from ⟨(2, 0), by
      rw [hB]; exact ⟨⟨le_refl _, by norm_num⟩, ⟨le_refl _, by norm_num⟩⟩⟩)
    (continuous_momentWeight lam l).continuousOn
  have hmpos : 0 < momentWeight lam l m := by
    obtain ⟨h1, h2⟩ := Set.mem_prod.mp hm
    unfold momentWeight
    have : 1 ≤ m.1 - m.2 := by linarith [h1.1, h2.2]
    have hp : 0 < (m.1 - m.2) ^ (2 * l) := pow_pos (by linarith) _
    have := heatKernel_pos lam m.1
    have := heatKernel_pos lam m.2
    positivity
  have hvol : volume B = 1 := by
    rw [hB, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    norm_num
  have hset := setIntegral_ge_of_const_le (μ := volume) (s := B)
    (measurableSet_Icc.prod measurableSet_Icc) (by rw [hvol]; exact ENNReal.one_ne_top)
    (fun p hp => hmin hp) hI.integrableOn
  rw [measureReal_def, hvol, ENNReal.toReal_one, one_smul] at hset
  exact lt_of_lt_of_le hmpos (hset.trans (setIntegral_le_integral hI
    (Eventually.of_forall fun p => momentWeight_nonneg lam l p)))

/-- **Large-height positivity of the slice moments of `H_λ`** (Ki–Kim–Lee + cone criterion). -/
theorem exists_kernelSliceMoment_heatKernel_nonneg {lam : ℝ} (hlam : 0 < lam) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ t' : ℝ, X₀ ≤ |t'| → ∀ n : ℕ,
      0 ≤ kernelSliceMoment (heatKernel lam) 0 t' n := by
  obtain ⟨X₁, hX₁⟩ := exists_nonnegTaylorAtZero_riemannHeat_slice hlam
  refine ⟨max X₁ 1, le_max_right _ _, fun t' ht' n => ?_⟩
  have hNT := hX₁ t' (le_trans (le_max_left _ _) ht')
  have e := kernelSliceMoment_heat_eq hlam.le 0 t' n
  have hk : (fun u => riemannKernelReal u * Real.exp (lam * u ^ 2)) = heatKernel lam := rfl
  rw [hk] at e
  rw [e, Complex.ofReal_zero, div_eq_mul_inv,
    show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl]
  exact mul_nonneg (hNT.2 n) (Complex.zero_le_real.mpr (by positivity))

/-- **The slice moments do not vanish on intervals.** -/
theorem exists_mem_Ioo_kernelSliceMoment_ne_zero {lam : ℝ} (hlam : 0 ≤ lam) (l : ℕ) {a b : ℝ}
    (hab : a < b) : ∃ t₀ ∈ Set.Ioo a b, kernelSliceMoment (heatKernel lam) 0 t₀ (2 * l) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set H := riemannHeat lam with hH
  have hHd : Differentiable ℂ H := differentiable_riemannHeat hlam
  have hHc : ContDiff ℂ ⊤ H := hHd.contDiff
  set n := 2 * l with hn
  set F : ℂ → ℂ := fun τ => ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
    ((-I) ^ k * iteratedDeriv k H τ) * (I ^ (n - k) * iteratedDeriv (n - k) H τ) with hF
  have hFd : Differentiable ℂ F := by
    have hk : ∀ k : ℕ, Differentiable ℂ (iteratedDeriv k H) := fun k =>
      hHc.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)
    simp only [hF]
    exact Differentiable.fun_sum fun k _ => ((((hk k).const_mul _).const_mul _)).mul
      ((hk (n - k)).const_mul _)
  have hFM : ∀ t' : ℝ, F t' = (n.factorial : ℂ) * kernelSliceMoment (heatKernel lam) 0 t' n := by
    intro t'
    have e := kernelSliceMoment_heat_eq hlam 0 t' n
    have hk : (fun u => riemannKernelReal u * Real.exp (lam * u ^ 2)) = heatKernel lam := rfl
    rw [hk, Complex.ofReal_zero] at e
    have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    rw [e, mul_div_cancel₀ _ hfac, iteratedDeriv_slicePair hHd hHd]
  have hzero : ∀ t' ∈ Set.Ioo a b, F t' = 0 := fun t' ht' => by rw [hFM, hcon t' ht', mul_zero]
  set m : ℝ := (a + b) / 2 with hm
  have hmI : m ∈ Set.Ioo a b := ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] (m : ℂ), F z = 0 := by
    have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] m) (𝓝[≠] (m : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.tendsto m).mono_left
        nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
      exact fun h' => hx (Complex.ofReal_injective h')
    refine hmap.frequently (Eventually.frequently ?_)
    have : ∀ᶠ x in 𝓝 m, x ∈ Set.Ioo a b := isOpen_Ioo.mem_nhds hmI
    exact (this.filter_mono nhdsWithin_le_nhds).mono fun x hx => hzero x hx
  have hAn : AnalyticOnNhd ℂ F Set.univ := fun z _ => hFd.analyticAt z
  have hEq := hAn.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ _) hfreq
  have h0 := hEq (Set.mem_univ ((0 : ℝ) : ℂ))
  simp only [Pi.zero_apply] at h0
  rw [hFM] at h0
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hM0 : kernelSliceMoment (heatKernel lam) 0 0 n = 0 :=
    (mul_eq_zero.mp h0).resolve_left hfac
  have hpos := integral_momentWeight_pos hlam l
  rw [hn, kernelSliceMoment_heatKernel_eq] at hM0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at hM0
  rw [integral_complex_ofReal] at hM0
  exact hpos.ne' (Complex.ofReal_eq_zero.mp hM0)

/-! ## Laplace domination -/

/-- A pointwise splitting of `∫ G f` into a window, a contamination interval and a nonnegative
rest. -/
theorem integral_mul_ge_of_window {G f : ℝ → ℝ} (hG : Integrable G) (hG0 : ∀ x, 0 ≤ G x)
    (hf : Continuous f) {B X₀ a b γ₁ γ₂ : ℝ} (hX₀ : 0 ≤ X₀) (hXa : X₀ ≤ a)
    (hfB : ∀ x, |f x| ≤ B) (hfpos : ∀ x, X₀ ≤ |x| → 0 ≤ f x)
    (hγ₁ : ∀ x ∈ Set.Icc a b, γ₁ ≤ G x) (hγ₂ : ∀ x ∈ Set.Ioo (-X₀) X₀, G x ≤ γ₂) :
    γ₁ * (∫ x in Set.Icc a b, f x) - γ₂ * B * (2 * X₀) ≤ ∫ x, G x * f x := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hfB 0)
  have hGf : Integrable (fun x => G x * f x) :=
    hG.mul_bdd hf.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hfB x)
  have hW : Integrable (fun x => γ₁ * (Set.Icc a b).indicator f x) :=
    ((hf.integrableOn_Icc).integrable_indicator measurableSet_Icc).const_mul _
  have hC : Integrable (fun x => (Set.Ioo (-X₀) X₀).indicator (fun _ => γ₂ * B) x) :=
    (continuous_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).integrable_indicator
      measurableSet_Ioo
  have hpt : ∀ x, γ₁ * (Set.Icc a b).indicator f x -
      (Set.Ioo (-X₀) X₀).indicator (fun _ => γ₂ * B) x ≤ G x * f x := by
    intro x
    by_cases hxW : x ∈ Set.Icc a b
    · have hxC : x ∉ Set.Ioo (-X₀) X₀ := fun h => by linarith [h.2, hxW.1]
      rw [Set.indicator_of_mem hxW, Set.indicator_of_notMem hxC, sub_zero]
      have hfx : 0 ≤ f x := hfpos x (by rw [abs_of_nonneg (by linarith [hxW.1])]; linarith [hxW.1])
      exact mul_le_mul_of_nonneg_right (hγ₁ x hxW) hfx
    · rw [Set.indicator_of_notMem hxW, mul_zero, zero_sub]
      by_cases hxC : x ∈ Set.Ioo (-X₀) X₀
      · rw [Set.indicator_of_mem hxC]
        have h1 := hγ₂ x hxC
        have h2 := hfB x
        have h3 := hG0 x
        have : -(G x * |f x|) ≤ G x * f x := by
          have := neg_abs_le (f x); nlinarith
        have : G x * |f x| ≤ γ₂ * B := mul_le_mul h1 h2 (abs_nonneg _) (le_trans h3 h1)
        linarith
      · rw [Set.indicator_of_notMem hxC, neg_zero]
        have hx : X₀ ≤ |x| := by
          by_contra h; push Not at h
          exact hxC ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
        exact mul_nonneg (hG0 x) (hfpos x hx)
  have hint := integral_mono (hW.sub hC) hGf hpt
  simp only [Pi.sub_apply] at hint
  rw [integral_sub hW hC, integral_const_mul, integral_indicator measurableSet_Icc,
    integral_indicator_const _ measurableSet_Ioo, Real.volume_real_Ioo_of_le (by linarith),
    smul_eq_mul] at hint
  linarith

/-! ## Assembly -/

theorem xiSliceHeatTransfer_im_eq_zero {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    (xiSliceHeatTransfer lam 0 t n).im = 0 := by
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam 0 t n
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have h := Complex.hasSum_im hT
  have e : (fun k : ℕ => ((((lam / 2) ^ k / k.factorial *
      ((n + 2 * k).factorial / n.factorial) : ℝ) : ℂ) * xiSliceCoeff t (n + 2 * k)).im) =
      fun _ => 0 := by
    funext k
    rw [Complex.im_ofReal_mul, xiSliceCoeff_im_eq_zero, mul_zero]
  rw [e] at h
  exact h.unique hasSum_zero

theorem integrable_heightGaussian_mul_kernelSliceMoment {lam : ℝ} (hlam : 0 ≤ lam) {σ : ℝ}
    (hσ : 0 < σ) (t : ℝ) (l : ℕ) :
    Integrable (fun t' : ℝ => (heightGaussian σ t t' : ℂ) *
      kernelSliceMoment (heatKernel lam) 0 t' (2 * l)) :=
  (integrable_heightGaussian hσ t).ofReal.mul_bdd
    (continuous_kernelSliceMoment_heatKernel hlam l).aestronglyMeasurable
    (Eventually.of_forall fun t' => norm_kernelSliceMoment_heatKernel_le t' l)

/-- `Re T_{2l}(λ, 0, t) = ∫ G_λ(t − t') Re M_{2l}(t') dt'`. -/
theorem re_xiSliceHeatTransfer_eq {lam : ℝ} (hlam : 0 < lam) (t : ℝ) (l : ℕ) :
    (xiSliceHeatTransfer lam 0 t (2 * l)).re = ∫ t' : ℝ,
      heightGaussian (Real.sqrt (1 / (2 * lam))) t t' *
        (kernelSliceMoment (heatKernel lam) 0 t' (2 * l)).re := by
  have hσ : 0 < Real.sqrt (1 / (2 * lam)) := Real.sqrt_pos.mpr (by positivity)
  rw [← integral_heightGaussian_mul_kernelSliceMoment_heat hlam 0 t (2 * l)]
  change (∫ t' : ℝ, (heightGaussian (Real.sqrt (1 / (2 * lam))) t t' : ℂ) *
    kernelSliceMoment (heatKernel lam) 0 t' (2 * l)).re = _
  rw [← RCLike.re_to_complex, ← integral_re
    (integrable_heightGaussian_mul_kernelSliceMoment hlam.le hσ t l)]
  refine integral_congr_ae (Eventually.of_forall fun t' => ?_)
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]

theorem heightGaussian_neg (σ t t' : ℝ) : heightGaussian σ (-t) t' = heightGaussian σ t (-t') := by
  unfold heightGaussian
  congr 2
  ring

theorem re_xiSliceHeatTransfer_neg {lam : ℝ} (hlam : 0 < lam) (t : ℝ) (l : ℕ) :
    (xiSliceHeatTransfer lam 0 (-t) (2 * l)).re = (xiSliceHeatTransfer lam 0 t (2 * l)).re := by
  rw [re_xiSliceHeatTransfer_eq hlam, re_xiSliceHeatTransfer_eq hlam]
  simp_rw [heightGaussian_neg]
  have := integral_neg_eq_self (μ := (volume : Measure ℝ)) (fun t' : ℝ =>
    heightGaussian (Real.sqrt (1 / (2 * lam))) t t' *
      (kernelSliceMoment (heatKernel lam) 0 t' (2 * l)).re)
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun t' => ?_)
  simp only
  rw [re_kernelSliceMoment_heatKernel_neg hlam.le]

/-- A continuous function, nonnegative on `[a, b]` and nonzero at an interior point, has positive
integral over `[a, b]`. -/
theorem setIntegral_Icc_pos_of_ne_zero {f : ℝ → ℝ} (hf : Continuous f) {a b t₀ : ℝ}
    (hpos : ∀ x ∈ Set.Icc a b, 0 ≤ f x) (ht₀ : t₀ ∈ Set.Ioo a b) (hne : f t₀ ≠ 0) :
    0 < ∫ x in Set.Icc a b, f x := by
  have hft₀ : 0 < f t₀ := lt_of_le_of_ne (hpos t₀ (Set.Ioo_subset_Icc_self ht₀)) (Ne.symm hne)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hf t₀ (f t₀ / 2) (by positivity)
  set c := max a (t₀ - δ / 2) with hc
  set d := min b (t₀ + δ / 2) with hd
  have hcd : c < d := by
    rw [hc, hd]
    refine max_lt (lt_min (ht₀.1.trans ht₀.2) (by linarith [ht₀.1])) (lt_min (by linarith [ht₀.2])
      (by linarith))
  have hsub : Set.Icc c d ⊆ Set.Icc a b := Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hlow : ∀ x ∈ Set.Icc c d, f t₀ / 2 ≤ f x := by
    intro x hx
    have hxδ : dist x t₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [hx.1, le_max_right a (t₀ - δ / 2)]
      · linarith [hx.2, min_le_right b (t₀ + δ / 2)]
    have := hball x hxδ
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hI := hf.integrableOn_Icc (a := a) (b := b) (μ := volume)
  have h1 := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hlow (hI.mono_set hsub)
  rw [Real.volume_real_Icc_of_le hcd.le, smul_eq_mul] at h1
  have h2 := setIntegral_mono_set (s := Set.Icc c d) (t := Set.Icc a b) hI
    (ae_restrict_of_forall_mem measurableSet_Icc hpos) (Eventually.of_forall hsub)
  have : 0 < (d - c) * (f t₀ / 2) := by
    have : 0 < d - c := by linarith
    positivity
  linarith

/-- **Heated slice positivity at all large heights.**  For every `λ > 0` there is `T` with
`T_n(λ, 0, t) ≥ 0` for every `n` and every `|t| ≥ T`. -/
theorem exists_xiSliceHeatTransfer_nonneg_large_height {lam : ℝ} (hlam : 0 < lam) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ |t| → ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t n := by
  obtain ⟨X₀, hX₀1, hpos⟩ := exists_kernelSliceMoment_heatKernel_nonneg hlam
  have hX₀ : 0 ≤ X₀ := by linarith
  set σ : ℝ := Real.sqrt (1 / (2 * lam)) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hσ2 : 0 < σ ^ 2 := by positivity
  set a : ℝ := X₀ + 1 / 2 with ha
  set b : ℝ := X₀ + 1 with hb
  obtain ⟨l₁, hconc⟩ := exists_heatKernel_moment_concentration hlam.le
    (ε := 1 / (X₀ + 1) ^ 2) (by positivity)
  -- notation
  set W : ℕ → ℝ := fun l => ∫ p : ℝ × ℝ, momentWeight lam l p with hW
  set f : ℕ → ℝ → ℝ := fun l t' => (kernelSliceMoment (heatKernel lam) 0 t' (2 * l)).re with hf
  set J : ℕ → ℝ := fun l => ∫ x in Set.Icc a b, f l x with hJ
  have hWpos : ∀ l, 0 < W l := fun l => integral_momentWeight_pos hlam.le l
  have hfc : ∀ l, Continuous (f l) := fun l =>
    Complex.continuous_re.comp (continuous_kernelSliceMoment_heatKernel hlam.le l)
  have hfB : ∀ l x, |f l x| ≤ W l := fun l x =>
    (Complex.abs_re_le_norm _).trans (norm_kernelSliceMoment_heatKernel_le x l)
  have hfpos : ∀ l x, X₀ ≤ |x| → 0 ≤ f l x := fun l x hx =>
    (Complex.nonneg_iff.mp (hpos x hx (2 * l))).1
  have hwin : ∀ x ∈ Set.Icc a b, X₀ ≤ |x| := fun x hx => by
    rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1]
  -- the window integrals are positive
  have hJpos : ∀ l, 0 < J l := by
    intro l
    obtain ⟨t₀, ht₀, hne⟩ := exists_mem_Ioo_kernelSliceMoment_ne_zero hlam.le l
      (show a < b by rw [ha, hb]; linarith)
    have hM0 := hpos t₀ (hwin t₀ (Set.Ioo_subset_Icc_self ht₀)) (2 * l)
    have hre : f l t₀ ≠ 0 := by
      intro h0
      apply hne
      obtain ⟨-, him⟩ := Complex.nonneg_iff.mp hM0
      exact Complex.ext (by simpa [hf] using h0) (by simpa using him.symm)
    exact setIntegral_Icc_pos_of_ne_zero (hfc l) (fun x hx => hfpos l x (hwin x hx)) ht₀ hre
  -- concentration gives `J_l ≥ W_l/4` for large `l`
  have hJlarge : ∀ l, l₁ ≤ l → W l / 4 ≤ J l := by
    intro l hl
    obtain ⟨hI, hI2⟩ := integrable_momentWeight hlam.le l
    have hc := hconc l hl
    have hfac : (0 : ℝ) < (2 * l).factorial := by exact_mod_cast Nat.factorial_pos _
    have hQ : ∫ p : ℝ × ℝ, momentWeight lam l p * (p.1 + p.2) ^ 2 ≤ 1 / (X₀ + 1) ^ 2 * W l := by
      have e1 : ∫ p : ℝ × ℝ, momentWeight lam l p * (p.1 + p.2) ^ 2 =
          (∫ p : ℝ × ℝ, heatKernel lam p.1 * heatKernel lam p.2 * (p.1 - p.2) ^ (2 * l) *
            (p.1 + p.2) ^ 2) / (2 * l).factorial := by
        rw [← integral_div]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [momentWeight]; ring
      have e2 : W l = (∫ p : ℝ × ℝ, heatKernel lam p.1 * heatKernel lam p.2 *
          (p.1 - p.2) ^ (2 * l)) / (2 * l).factorial := by
        simp only [hW]
        rw [← integral_div]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [momentWeight]; ring
      rw [e1, e2, mul_div_assoc', div_le_div_iff_of_pos_right hfac]
      exact hc
    have hlow : ∀ x ∈ Set.Icc a b, W l / 2 ≤ f l x := by
      intro x hx
      have h := re_kernelSliceMoment_heatKernel_ge hlam.le x l
      have hx2 : x ^ 2 ≤ (X₀ + 1) ^ 2 := by
        have : |x| ≤ X₀ + 1 := by rw [abs_of_nonneg (by linarith [hx.1])]; exact hx.2
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      have hQ0 : 0 ≤ ∫ p : ℝ × ℝ, momentWeight lam l p * (p.1 + p.2) ^ 2 :=
        integral_nonneg fun p => mul_nonneg (momentWeight_nonneg _ _ _) (sq_nonneg _)
      have hX1 : 0 < (X₀ + 1) ^ 2 := by positivity
      have h3 : x ^ 2 / 2 * ∫ p : ℝ × ℝ, momentWeight lam l p * (p.1 + p.2) ^ 2 ≤ W l / 2 := by
        calc x ^ 2 / 2 * ∫ p : ℝ × ℝ, momentWeight lam l p * (p.1 + p.2) ^ 2
            ≤ (X₀ + 1) ^ 2 / 2 * (1 / (X₀ + 1) ^ 2 * W l) := by gcongr
          _ = W l / 2 := by field_simp
      simp only [hf]
      linarith
    have h1 := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hlow ((hfc l).integrableOn_Icc)
    rw [Real.volume_real_Icc_of_le (by rw [ha, hb]; linarith), smul_eq_mul] at h1
    simp only [hJ]
    rw [show b - a = 1 / 2 by rw [ha, hb]; ring] at h1
    linarith
  -- the height threshold
  have hterm0 : ∀ i, 0 ≤ Real.log (2 * X₀ * W i / J i + 1) / σ ^ 2 := by
    intro i
    have := hWpos i
    have := hJpos i
    have h0 : 0 ≤ 2 * X₀ * W i / J i := by positivity
    exact div_nonneg (Real.log_nonneg (by linarith)) hσ2.le
  set S : ℝ := ∑ l ∈ Finset.range l₁, Real.log (2 * X₀ * W l / J l + 1) / σ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun l _ => hterm0 l
  set T₀ : ℝ := b + Real.log (8 * X₀ + 1) / σ ^ 2 + S with hT₀
  refine ⟨T₀, fun t ht n => ?_⟩
  obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' n
  swap
  · rw [xiSliceHeatTransfer_odd_eq_zero hlam.le]
  have hlog8 : 0 ≤ Real.log (8 * X₀ + 1) / σ ^ 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hσ2.le
  -- reduce to `t ≥ T₀`
  suffices key : ∀ t : ℝ, T₀ ≤ t → 0 ≤ (xiSliceHeatTransfer lam 0 t (2 * l)).re by
    refine Complex.nonneg_iff.mpr ⟨?_, (xiSliceHeatTransfer_im_eq_zero hlam.le t _).symm⟩
    rcases le_total 0 t with h | h
    · exact key t (by rwa [abs_of_nonneg h] at ht)
    · rw [← neg_neg t, re_xiSliceHeatTransfer_neg hlam]
      exact key (-t) (by rwa [abs_of_nonpos h] at ht)
  intro t ht
  have htb : b ≤ t := by linarith
  set γ₂ : ℝ := heightGaussian σ t X₀ with hγ₂
  set E : ℝ := Real.exp (σ ^ 2 * (t - X₀ - 1 / 4)) with hE
  have hγ₁ : heightGaussian σ t a = E * γ₂ := by
    simp only [hγ₂, hE, heightGaussian]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    rw [ha]; ring
  have hγ₂0 : 0 ≤ γ₂ := by simp only [hγ₂, heightGaussian]; positivity
  have hG0 : ∀ x, 0 ≤ heightGaussian σ t x := fun x => by unfold heightGaussian; positivity
  have hwinG : ∀ x ∈ Set.Icc a b, heightGaussian σ t a ≤ heightGaussian σ t x := by
    intro x hx
    unfold heightGaussian
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h1 : 0 ≤ t - x := by linarith [hx.2]
    have h2 : t - x ≤ t - a := by linarith [hx.1]
    have : (t - x) ^ 2 ≤ (t - a) ^ 2 := pow_le_pow_left₀ h1 h2 2
    nlinarith
  have hconG : ∀ x ∈ Set.Ioo (-X₀) X₀, heightGaussian σ t x ≤ γ₂ := by
    intro x hx
    simp only [hγ₂]
    unfold heightGaussian
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h1 : 0 ≤ t - X₀ := by linarith
    have h2 : t - X₀ ≤ t - x := by linarith [hx.2]
    have : (t - X₀) ^ 2 ≤ (t - x) ^ 2 := pow_le_pow_left₀ h1 h2 2
    nlinarith
  have hcore := integral_mul_ge_of_window (integrable_heightGaussian hσ t) hG0 (hfc l) hX₀
    (show X₀ ≤ a by rw [ha]; linarith) (hfB l) (hfpos l) hwinG hconG
  rw [re_xiSliceHeatTransfer_eq hlam]
  refine le_trans ?_ hcore
  rw [hγ₁]
  -- `E J ≥ 2 X₀ W`
  have hEJ : 2 * X₀ * W l ≤ E * J l := by
    have hJ := hJpos l
    have hWl := hWpos l
    rcases lt_or_ge l l₁ with hl | hl
    · have hterm : Real.log (2 * X₀ * W l / J l + 1) / σ ^ 2 ≤ S :=
        Finset.single_le_sum (f := fun l => Real.log (2 * X₀ * W l / J l + 1) / σ ^ 2)
          (fun i _ => hterm0 i) (Finset.mem_range.mpr hl)
      have hexp : 2 * X₀ * W l / J l + 1 ≤ E := by
        rw [hE, ← Real.exp_log (show 0 < 2 * X₀ * W l / J l + 1 by positivity)]
        refine Real.exp_le_exp.mpr ?_
        rw [div_le_iff₀ hσ2] at hterm
        have : Real.log (2 * X₀ * W l / J l + 1) ≤ σ ^ 2 * (t - X₀ - 1 / 4) := by
          nlinarith
        linarith
      have : 2 * X₀ * W l / J l ≤ E := by linarith
      rw [div_le_iff₀ hJ] at this
      linarith
    · have hJl := hJlarge l hl
      have hexp : 8 * X₀ + 1 ≤ E := by
        rw [hE, ← Real.exp_log (show 0 < 8 * X₀ + 1 by linarith)]
        refine Real.exp_le_exp.mpr ?_
        have h1 : Real.log (8 * X₀ + 1) / σ ^ 2 ≤ t - X₀ - 1 / 4 := by
          rw [hT₀, hb] at ht; linarith
        rw [div_le_iff₀ hσ2] at h1
        linarith
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      nlinarith
  have := mul_le_mul_of_nonneg_left hEJ hγ₂0
  nlinarith

/-! ## The WD heat threshold lies strictly below `1/12` -/

/-- Heated positivity at a height propagates to larger heats. -/
theorem xiSliceHeatTransfer_nonneg_of_le_of_forall {lam lam' t : ℝ} (hll : lam ≤ lam')
    (h : ∀ m : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t m) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam' 0 t n := by
  refine (hasSum_xiSliceHeatTransfer_shift hll 0 t n).nonneg fun k => ?_
  refine mul_nonneg (Complex.zero_le_real.mpr ?_) (h _)
  have : 0 ≤ (lam' - lam) / 2 := by linarith
  positivity

/-- **`λ_WD < 1/12`.**  Above a height `T` the heated slices are positive for `λ = 1/24`
(`exists_xiSliceHeatTransfer_nonneg_large_height`).  Below `T` only the finitely many zeros with
`|Re z| ≤ T + ½` can violate the heated cone condition, and each has `(Im z)² < 1/4`. -/
theorem wdHeatThreshold_lt_twelfth : wdHeatThreshold < 1 / 12 := by
  obtain ⟨T, hT⟩ := exists_xiSliceHeatTransfer_nonneg_large_height (lam := 1 / 24) (by norm_num)
  set T' : ℝ := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  have hfin := finite_xiZeroCopy_norm_le (T' + 2)
  -- the largest `(Im z)²` among the zeros with `‖z‖ ≤ T' + 2`
  obtain ⟨m, hm4, hmax⟩ : ∃ m : ℝ, m < 1 / 4 ∧ ∀ q : XiZeroCopy,
      ‖xiSpectralPoint q‖ ≤ T' + 2 → (xiSpectralPoint q).im ^ 2 ≤ m := by
    by_cases hne : hfin.toFinset.Nonempty
    · refine ⟨hfin.toFinset.sup' hne fun q => (xiSpectralPoint q).im ^ 2, ?_, fun q hq => ?_⟩
      · obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup' hne fun q => (xiSpectralPoint q).im ^ 2
        rw [hq]
        exact xiSpectralPoint_im_sq_lt_quarter q
      · exact Finset.le_sup' (fun q => (xiSpectralPoint q).im ^ 2)
          (hfin.mem_toFinset.mpr hq)
    · refine ⟨0, by norm_num, fun q hq => ?_⟩
      exact absurd ⟨q, hfin.mem_toFinset.mpr hq⟩ hne
  set lam : ℝ := max (1 / 24) (m / 3) with hlam
  have hlam12 : lam < 1 / 12 := max_lt (by norm_num) (by linarith)
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) (le_max_left _ _)
  -- the heated cone condition at every height `|t| < T' + 1`
  have hcone : ∀ t : ℝ, |t| < T' + 1 → ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 ≤ ((xiSpectralPoint q).re - t) ^ 2 + 3 * lam := by
    intro t ht q
    have h4 := xiSpectralPoint_im_sq_lt_quarter q
    by_cases hnear : |(xiSpectralPoint q).re - t| < 1 / 2
    · have hnorm : ‖xiSpectralPoint q‖ ≤ T' + 2 := by
        have h1 : |(xiSpectralPoint q).re| ≤ T' + 3 / 2 := by
          have := abs_sub_abs_le_abs_sub (xiSpectralPoint q).re t
          linarith [abs_sub_comm (xiSpectralPoint q).re t]
        have h2 : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
          have hsq : |(xiSpectralPoint q).im| ^ 2 < 1 / 4 := by rw [sq_abs]; exact h4
          nlinarith [abs_nonneg (xiSpectralPoint q).im]
        calc ‖xiSpectralPoint q‖ ≤ |(xiSpectralPoint q).re| + |(xiSpectralPoint q).im| :=
              Complex.norm_le_abs_re_add_abs_im _
          _ ≤ T' + 2 := by linarith
      have := hmax q hnorm
      have : m ≤ 3 * lam := by have := le_max_right (1 / 24) (m / 3); linarith
      nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]
    · push Not at hnear
      have : 1 / 4 ≤ ((xiSpectralPoint q).re - t) ^ 2 := by
        rw [← sq_abs]; nlinarith
      linarith
  refine lt_of_le_of_lt (csInf_le wdHeatAdmissible_bddBelow fun t n => ?_) hlam12
  rcases le_or_gt T' |t| with hbig | hsmall
  · exact xiSliceHeatTransfer_nonneg_of_le_of_forall (le_max_left _ _)
      (hT t (le_trans (le_max_left _ _) hbig)) n
  · -- below `T'`: the per-pair law, with continuity at real zeros of `Ξ`
    have hgood : ∀ t' : ℝ, |t'| < T' + 1 → XiC (t' : ℂ) ≠ 0 →
        0 ≤ xiSliceHeatTransfer lam 0 t' n := fun t' ht' hX =>
      xiSliceHeatTransfer_nonneg_of_heatedCone hlam0 hX (hcone t' ht') n
    by_cases hX : XiC (t : ℂ) ≠ 0
    · exact hgood t (by linarith) hX
    · have hc := ((continuous_xiSliceHeatTransfer hlam0 0 n).tendsto t).mono_left
        (nhdsWithin_le_nhds (s := {t}ᶜ))
      have hnear : ∀ᶠ t' in 𝓝[≠] t, |t'| < T' + 1 := by
        have : ∀ᶠ t' in 𝓝 t, |t'| < T' + 1 :=
          (continuous_abs.tendsto t).eventually (gt_mem_nhds (by linarith))
        exact this.filter_mono nhdsWithin_le_nhds
      exact ge_of_tendsto hc ((hnear.and (eventually_XiC_ofReal_ne_zero t)).mono
        fun t' h => hgood t' h.1 h.2)

end

end RHTower.DeBruijn
