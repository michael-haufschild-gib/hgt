import GaloisForLFunctions.RHTower.XiCosineShiftPoissonFlow
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.LaguerreInequality
import GaloisForLFunctions.RHTower.XiExceptionalPointFoldLaw
import GaloisForLFunctions.RHTower.PhotonicIntegerClockHalfRate

/-!
# A pointwise strict Laguerre criterion on the open strip

**Theorem** (`riemannHypothesis_iff_strict_laguerre_strip`). RH holds iff

  `(Im ξ'(s))² + Re ξ(s) · Re ξ''(s) > 0`   for every `s` with `½ < Re s < 1`.

At `s = ½ + h + ix` the left side is the first Laguerre expression `A'² − A A''` of the producer
`A_h = cos(hD)Ξ` at the real point `x`. So RH is the strict first Laguerre inequality for every
producer of the open depth band.

* (⇐) At an exceptional point (`Re ξ = 0`, `Im ξ' = 0`) the expression vanishes. With no exceptional
  point, RH follows (`riemannHypothesis_of_cosProducer_no_exceptionalPoint`).
* (⇒) Under RH, `A_h` is Laguerre–Pólya with simple real zeros. Every producer has a real zero
  (`exists_foldF_eq_zero`): `Ξ = P_{0,h} ∗ A_h` with a positive kernel, and `Ξ` has a real zero
  (Hardy), so `A_h` cannot keep one sign. The approximating real-rooted polynomials then have a root
  near that zero, and the peel identity `L₁[(X − r)q] = q² + (X − r)² L₁[q]` gives
  `L₁[p](x) ≥ p(x)²/(x − r)²` (`laguerreL1_eval_ge_of_root`). In the limit `L₁[A_h](x) > 0` off the
  zeros; at a zero it is `A_h'(x)² > 0` by simplicity.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Every producer has a real zero -/

theorem cosProducer_zero_depth (z : ℂ) : cosProducer 0 z = XiC z := by
  simp [cosProducer]

theorem continuous_foldF (h : ℝ) : Continuous (foldF h) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_foldF_x h x).continuousAt

theorem abs_foldF_le (h x : ℝ) :
    |foldF h x| ≤ ∫ u : ℝ, riemannKernelReal u * Real.cosh (h * u) := by
  have hk := DeBruijn.riemannKernel_mul_cosh_superExp h
  have e := cosProducer_eq_foldF h x
  rw [cosProducer, ← DeBruijn.cosTransform_riemannKernel_mul_cosh] at e
  have hn : ‖(foldF h x : ℂ)‖ ≤ ∫ u : ℝ, riemannKernelReal u * Real.cosh (h * u) := by
    rw [← e]
    unfold DeBruijn.cosTransform
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk.nonneg u)]
    have : ‖Complex.exp (I * (x : ℂ) * u)‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [this, mul_one]
  rwa [Complex.norm_real, Real.norm_eq_abs] at hn

/-- **Every producer has a real zero.** For `h > 0` there is a real `x` with `A_h(x) = 0`. -/
theorem exists_foldF_eq_zero {h : ℝ} (hh : 0 < h) : ∃ x : ℝ, foldF h x = 0 := by
  obtain ⟨a, -, -, -, -, hza, -⟩ := exists_two_distinct_positive_real_XiC_zeros
  by_contra hno
  push Not at hno
  have hc := continuous_foldF h
  have hsign : (∀ x, 0 < foldF h x) ∨ (∀ x, foldF h x < 0) := by
    rcases lt_or_gt_of_ne (hno 0) with h0 | h0
    · right; intro x; by_contra hx; push Not at hx
      obtain ⟨y, -, hy⟩ := intermediate_value_uIcc (a := (0 : ℝ)) (b := x) hc.continuousOn
        (Set.mem_uIcc.mpr (Or.inl ⟨h0.le, hx⟩))
      exact hno y hy
    · left; intro x; by_contra hx; push Not at hx
      obtain ⟨y, -, hy⟩ := intermediate_value_uIcc (a := (0 : ℝ)) (b := x) hc.continuousOn
        (Set.mem_uIcc.mpr (Or.inr ⟨hx, h0.le⟩))
      exact hno y hy
  have hflow := cosProducer_eq_integral_poissonPort_mul (h := 0) (H := h) le_rfl hh a
  rw [cosProducer_zero_depth, hza] at hflow
  have hcongr : ∫ v : ℝ, (poissonPort 0 h (a - v) : ℂ) * cosProducer h v =
      ((∫ v : ℝ, poissonPort 0 h (a - v) * foldF h v : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [cosProducer_eq_foldF]; push_cast; ring
  rw [hcongr] at hflow
  have hzero : ∫ v : ℝ, poissonPort 0 h (a - v) * foldF h v = 0 := by exact_mod_cast hflow.symm
  -- integrability
  have hPi : Integrable (fun v : ℝ => poissonPort 0 h (a - v)) :=
    (integrable_poissonPort le_rfl hh).comp_sub_left a
  have hint : Integrable (fun v : ℝ => poissonPort 0 h (a - v) * foldF h v) := by
    have := hPi.bdd_mul (f := foldF h) (c := ∫ u : ℝ, riemannKernelReal u * Real.cosh (h * u))
      hc.aestronglyMeasurable (Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs]; exact abs_foldF_le h v)
    simpa [mul_comm] using this
  rcases hsign with hpos | hneg
  · have hnn : 0 ≤ fun v : ℝ => poissonPort 0 h (a - v) * foldF h v := fun v =>
      (mul_pos (poissonPort_pos le_rfl hh _) (hpos v)).le
    have hsupp : Function.support (fun v : ℝ => poissonPort 0 h (a - v) * foldF h v) = univ := by
      ext v
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (mul_pos (poissonPort_pos le_rfl hh _) (hpos v)).ne'
    have := (integral_pos_iff_support_of_nonneg hnn hint).mpr (by
      rw [hsupp, Real.volume_univ]; exact ENNReal.zero_lt_top)
    linarith
  · have hnn : 0 ≤ fun v : ℝ => -(poissonPort 0 h (a - v) * foldF h v) := fun v => by
      have := mul_neg_of_pos_of_neg (poissonPort_pos le_rfl hh (a - v)) (hneg v)
      simp only [Pi.zero_apply]; linarith
    have hsupp : Function.support (fun v : ℝ => -(poissonPort 0 h (a - v) * foldF h v)) = univ := by
      ext v
      simp only [Function.mem_support, mem_univ, iff_true, neg_ne_zero]
      exact (mul_neg_of_pos_of_neg (poissonPort_pos le_rfl hh (a - v)) (hneg v)).ne
    have := (integral_pos_iff_support_of_nonneg hnn hint.neg).mpr (by
      rw [hsupp, Real.volume_univ]; exact ENNReal.zero_lt_top)
    rw [integral_neg] at this
    linarith

/-! ## The strict polynomial bound -/

/-- If `p` splits over `ℝ` and `p(r) = 0`, then `L₁[p](x) ≥ p(x)²/(x − r)²`. -/
theorem laguerreL1_eval_ge_of_root {p : ℝ[X]} (hsp : p.Splits) {r : ℝ} (hr : p.IsRoot r) (x : ℝ) :
    (p.eval x) ^ 2 / (x - r) ^ 2 ≤ (laguerreL1 p).eval x := by
  by_cases hp0 : p = 0
  · subst hp0; simp [laguerreL1]
  set q := p /ₘ (X - C r) with hq
  have hfac : (X - C r) * q = p := mul_divByMonic_eq_iff_isRoot.mpr hr
  have hqs : q.Splits := Splits.of_dvd hsp hp0 ⟨X - C r, by rw [← hfac, mul_comm]⟩
  have hL := laguerreL1_linear_mul r q
  rw [hfac] at hL
  rw [hL, eval_add, eval_mul, eval_pow, eval_pow, eval_sub, eval_X, eval_C]
  have hnn := laguerreL1_eval_nonneg hqs x
  have hpx : p.eval x = (x - r) * q.eval x := by
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C]
  rw [hpx]
  by_cases hxr : x = r
  · subst hxr; simp; positivity
  · have hne : (x - r) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hxr)
    rw [mul_pow, mul_div_cancel_left₀ _ hne]
    nlinarith [sq_nonneg (x - r)]

/-! ## Derivatives of the producer on the real line -/

theorem deriv_cosProducer_real (h x : ℝ) : deriv (cosProducer h) x = (foldFx h x : ℂ) := by
  have e : ((1 / 2 + h : ℝ) : ℂ) + x * I = 1 / 2 + h + x * I := by push_cast; ring
  rw [deriv_cosProducer_ofReal, foldFx, e]
  push_cast; ring

theorem deriv_deriv_cosProducer_real (h x : ℝ) :
    deriv (deriv (cosProducer h)) x = (foldFxx h x : ℂ) := by
  have hd : Differentiable ℂ (deriv (cosProducer h)) := by
    rw [← differentiableOn_univ]
    exact (differentiable_cosProducer h).differentiableOn.deriv isOpen_univ
  have h1 : HasDerivAt (fun t : ℝ => deriv (cosProducer h) (t : ℂ))
      (deriv (deriv (cosProducer h)) x) x := (hd x).hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun t : ℝ => deriv (cosProducer h) (t : ℂ)) (foldFxx h x : ℂ) x := by
    have := (hasDerivAt_foldFx_x h x).ofReal_comp
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    exact deriv_cosProducer_real h t
  exact h1.unique h2

theorem laguerreL1_eval (p : ℝ[X]) (x : ℝ) :
    (laguerreL1 p).eval x =
      (derivative p).eval x ^ 2 - p.eval x * (derivative (derivative p)).eval x := by
  simp [laguerreL1, eval_sub, eval_pow, eval_mul]

/-! ## Under RH: the strict Laguerre inequality for every producer -/

/-- **Strict first Laguerre inequality under RH.** For every `h > 0` and real `x`,
`A_h'(x)² − A_h(x) A_h''(x) > 0`. -/
theorem laguerre_pos_of_laguerrePolya {h : ℝ} (hh : 0 < h)
    (hLP : GaloisForLFunctions.HTGeometry.LaguerrePolya (cosProducer h))
    (hsimple : ∀ y : ℝ, foldF h y = 0 → foldFx h y ≠ 0) (x : ℝ) :
    0 < foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  obtain ⟨p, hsp, hconv⟩ := hLP
  have hconvA : TendstoLocallyUniformly (fun m => polyEvalC (p m)) (cosProducer h) atTop := hconv
  have hd := tendstoLocallyUniformly_iterate_deriv hconvA (fun m => differentiable_polyEvalC _)
  have hreal : ∀ j : ℕ, ∀ y : ℝ, Tendsto (fun m => ((⇑derivative)^[j] (p m)).eval y) atTop
      (𝓝 ((deriv^[j] (cosProducer h) (y : ℂ)).re)) := by
    intro j y
    have ht := (tendstoLocallyUniformlyOn_univ.mpr (hd j)).tendsto_at (mem_univ (y : ℂ))
    simp_rw [iterate_deriv_polyEvalC, polyEvalC_ofReal] at ht
    have := (Complex.continuous_re.tendsto _).comp ht
    simpa [Function.comp_def] using this
  have h0 : ∀ y : ℝ, Tendsto (fun m => (p m).eval y) atTop (𝓝 (foldF h y)) := by
    intro y
    have := hreal 0 y
    simpa [cosProducer_eq_foldF] using this
  have h1 : Tendsto (fun m => (derivative (p m)).eval x) atTop (𝓝 (foldFx h x)) := by
    have := hreal 1 x
    simpa [deriv_cosProducer_real] using this
  have h2 : Tendsto (fun m => (derivative (derivative (p m))).eval x) atTop (𝓝 (foldFxx h x)) := by
    have := hreal 2 x
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at this
    simpa [deriv_deriv_cosProducer_real] using this
  by_cases hx0 : foldF h x = 0
  · rw [hx0, zero_mul, sub_zero]
    have hne := hsimple x hx0
    positivity
  -- a real zero `x₀ ≠ x` with a sign change
  obtain ⟨x₀, hx₀⟩ := exists_foldF_eq_zero hh
  have hxx₀ : x ≠ x₀ := fun e => hx0 (e ▸ hx₀)
  have hd₀ := hsimple x₀ hx₀
  have hslope := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_foldF_x h x₀))
  have hev : ∀ᶠ t in 𝓝[≠] x₀, 0 < foldFx h x₀ * slope (foldF h) x₀ t := by
    have : Tendsto (fun t => foldFx h x₀ * slope (foldF h) x₀ t) (𝓝[≠] x₀)
        (𝓝 (foldFx h x₀ * foldFx h x₀)) := hslope.const_mul _
    exact this.eventually (lt_mem_nhds (mul_self_pos.mpr hd₀))
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  set δ : ℝ := min ε (|x - x₀| / 2) / 2 with hδ
  have hxpos : 0 < |x - x₀| := abs_pos.mpr (sub_ne_zero.mpr hxx₀)
  have hδpos : 0 < δ := by positivity
  have hδε : δ < ε := by
    have : min ε (|x - x₀| / 2) ≤ ε := min_le_left _ _
    rw [hδ]; linarith
  have hδx : δ < |x - x₀| / 2 := by
    have : min ε (|x - x₀| / 2) ≤ |x - x₀| / 2 := min_le_right _ _
    rw [hδ]; linarith [half_pos hxpos]
  have hsa := hall (y := x₀ - δ) (by rw [Real.dist_eq]; simp [abs_of_pos hδpos, hδε])
    (by simp [hδpos.ne'])
  have hsb := hall (y := x₀ + δ) (by rw [Real.dist_eq]; simp [abs_of_pos hδpos, hδε])
    (by simp [hδpos.ne'])
  simp only [slope_def_field, hx₀, sub_zero] at hsa hsb
  have hab : foldF h (x₀ - δ) * foldF h (x₀ + δ) < 0 := by
    have ea : (x₀ - δ - x₀) = -δ := by ring
    have eb : (x₀ + δ - x₀) = δ := by ring
    rw [ea] at hsa; rw [eb] at hsb
    have hsa' : 0 < foldFx h x₀ * (-foldF h (x₀ - δ)) / δ := by
      have : foldFx h x₀ * (foldF h (x₀ - δ) / -δ) = foldFx h x₀ * (-foldF h (x₀ - δ)) / δ := by
        field_simp
      rw [← this]; exact hsa
    have hsb' : 0 < foldFx h x₀ * foldF h (x₀ + δ) / δ := by
      have : foldFx h x₀ * (foldF h (x₀ + δ) / δ) = foldFx h x₀ * foldF h (x₀ + δ) / δ := by ring
      rw [← this]; exact hsb
    have ha := (div_pos_iff_of_pos_right hδpos).mp hsa'
    have hb := (div_pos_iff_of_pos_right hδpos).mp hsb'
    have := mul_pos ha hb
    nlinarith [sq_nonneg (foldFx h x₀), mul_self_pos.mpr hd₀]
  -- eventually the approximants change sign on `[x₀ − δ, x₀ + δ]`
  have hprod : Tendsto (fun m => (p m).eval (x₀ - δ) * (p m).eval (x₀ + δ)) atTop
      (𝓝 (foldF h (x₀ - δ) * foldF h (x₀ + δ))) := (h0 _).mul (h0 _)
  have hevm : ∀ᶠ m in atTop, (p m).eval (x₀ - δ) * (p m).eval (x₀ + δ) < 0 :=
    hprod.eventually (gt_mem_nhds hab)
  set D : ℝ := |x - x₀| + δ with hD
  have hDpos : 0 < D := by positivity
  have hbound : ∀ᶠ m in atTop, ((p m).eval x) ^ 2 / D ^ 2 ≤ (laguerreL1 (p m)).eval x := by
    filter_upwards [hevm] with m hm
    obtain ⟨r, hr, hroot⟩ : ∃ r ∈ Icc (x₀ - δ) (x₀ + δ), (p m).eval r = 0 := by
      have hcont : ContinuousOn (fun y => (p m).eval y) (Icc (x₀ - δ) (x₀ + δ)) :=
        (Polynomial.continuous _).continuousOn
      rcases lt_or_gt_of_ne (show (p m).eval (x₀ - δ) ≠ 0 from fun e => by
        rw [e, zero_mul] at hm; exact lt_irrefl _ hm) with hneg | hpos
      · have hpb : 0 < (p m).eval (x₀ + δ) := by
          by_contra hc; push Not at hc; nlinarith
        obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc (by linarith) hcont ⟨hneg.le, hpb.le⟩
        exact ⟨r, hr, hr0⟩
      · have hpb : (p m).eval (x₀ + δ) < 0 := by
          by_contra hc; push Not at hc; nlinarith
        obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' (by linarith) hcont ⟨hpb.le, hpos.le⟩
        exact ⟨r, hr, hr0⟩
    have hge := laguerreL1_eval_ge_of_root (hsp m) (r := r) hroot x
    have hxr : 0 < (x - r) ^ 2 := by
      have : |x - x₀| - δ ≤ |x - r| := by
        have := abs_sub_abs_le_abs_sub (x - x₀) (r - x₀)
        have hr' : |r - x₀| ≤ δ := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
        rw [show x - x₀ - (r - x₀) = x - r by ring] at this
        linarith
      have : 0 < |x - r| := by linarith
      rw [← sq_abs]; positivity
    have hle : (x - r) ^ 2 ≤ D ^ 2 := by
      have : |x - r| ≤ D := by
        have hr' : |r - x₀| ≤ δ := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
        calc |x - r| = |(x - x₀) - (r - x₀)| := by ring_nf
          _ ≤ |x - x₀| + |r - x₀| := abs_sub _ _
          _ ≤ D := by rw [hD]; linarith
      have h0' : 0 ≤ |x - r| := abs_nonneg _
      nlinarith [sq_abs (x - r)]
    calc ((p m).eval x) ^ 2 / D ^ 2 ≤ ((p m).eval x) ^ 2 / (x - r) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) hxr hle
      _ ≤ _ := hge
  have hL : Tendsto (fun m => (laguerreL1 (p m)).eval x) atTop
      (𝓝 (foldFx h x ^ 2 - foldF h x * foldFxx h x)) := by
    simp_rw [laguerreL1_eval]
    exact (h1.pow 2).sub ((h0 x).mul h2)
  have hR : Tendsto (fun m => ((p m).eval x) ^ 2 / D ^ 2) atTop (𝓝 (foldF h x ^ 2 / D ^ 2)) :=
    ((h0 x).pow 2).div_const _
  have := le_of_tendsto_of_tendsto hR hL hbound
  have hpos : 0 < foldF h x ^ 2 / D ^ 2 := by
    have := pow_pos (abs_pos.mpr hx0) 2
    rw [sq_abs] at this
    positivity
  linarith

/-- Real zeros of `A_h` are simple when every zero of `Ξ` lies inside the defect-free cone. -/
theorem foldFx_ne_zero_of_zeros {h : ℝ} (hh : 0 < h)
    (hloc : ∀ w : ℂ, XiC w = 0 → w.im ^ 2 < h ^ 2) (y : ℝ) (hy : foldF h y = 0) :
    foldFx h y ≠ 0 := by
  have hz : (XiC ((y : ℂ) + h * I) + XiC ((y : ℂ) - h * I)) / 2 = 0 := by
    have := cosProducer_eq_foldF h y
    rw [hy, Complex.ofReal_zero] at this
    exact this
  have hne := deriv_cosineShiftXi_ne_zero_of_local hh
    (fun w hw => by nlinarith [hloc w hw, sq_nonneg (y - w.re)]) hz
  change deriv (cosProducer h) y ≠ 0 at hne
  rw [deriv_cosProducer_real] at hne
  exact_mod_cast hne

/-- **Strict first Laguerre inequality under RH.** For every `h > 0` and real `x`,
`A_h'(x)² − A_h(x) A_h''(x) > 0`. -/
theorem laguerre_pos_of_rh (hRH : RiemannHypothesis) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    0 < foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  refine laguerre_pos_of_laguerrePolya hh (laguerrePolya_cosineShiftXi_of_rh hRH hh) (fun y hy => ?_) x
  have hz : (XiC ((y : ℂ) + h * I) + XiC ((y : ℂ) - h * I)) / 2 = 0 := by
    have := cosProducer_eq_foldF h y
    rw [hy, Complex.ofReal_zero] at this
    exact this
  have hne := deriv_cosineShiftXi_ne_zero_of_rh hRH hh hz
  change deriv (cosProducer h) y ≠ 0 at hne
  rw [deriv_cosProducer_real] at hne
  exact_mod_cast hne

/-- **The Laguerre abscissa law.** If every zero `ρ` of `ξ` has `|Re ρ − ½| < h` (spectral points
`|Im γ| < h`), the strict first Laguerre inequality holds for `A_h` at every real point. -/
theorem laguerre_pos_of_zeros_im_sq_lt {h : ℝ} (hh : 0 < h)
    (hz : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 < h ^ 2) (x : ℝ) :
    0 < foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  refine laguerre_pos_of_laguerrePolya hh ?_ (foldFx_ne_zero_of_zeros hh (fun w hw => ?_)) x
  · refine laguerrePolya_cosineShiftXi_of_im_gt fun q => ?_
    have := abs_lt.mp (abs_lt_of_sq_lt_sq (hz q) hh.le)
    exact this.1
  · obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_XiC_eq_zero hw
    exact hz q

/-- **Unconditional strict Laguerre beyond the horizon.** Every producer `A_h`, `h ≥ ½`, satisfies
the strict first Laguerre inequality: `Q(s) > 0` for `Re s ≥ 1`. -/
theorem laguerre_pos_of_half_le {h : ℝ} (hh : 1 / 2 ≤ h) (x : ℝ) :
    0 < foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  refine laguerre_pos_of_zeros_im_sq_lt (by linarith) (fun q => ?_) x
  have := xiSpectralPoint_im_sq_lt_quarter q
  nlinarith

/-! ## The criterion -/

/-- **RH as the strict first Laguerre inequality for every producer of the open depth band.** -/
theorem riemannHypothesis_iff_strict_laguerre_producer :
    RiemannHypothesis ↔ ∀ h : ℝ, 0 < h → h < 1 / 2 → ∀ x : ℝ,
      0 < foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  refine ⟨fun hRH h hh _ x => laguerre_pos_of_rh hRH hh x, fun hall => ?_⟩
  refine riemannHypothesis_of_cosProducer_no_exceptionalPoint fun h hh hh2 x hx => ?_
  have hF : foldF h x = 0 := by
    have := cosProducer_eq_foldF h x
    rw [hx] at this
    exact_mod_cast this.symm
  have hpos := hall h hh hh2 x
  rw [hF, zero_mul, sub_zero] at hpos
  rw [deriv_cosProducer_real]
  intro h0
  have : foldFx h x = 0 := by exact_mod_cast h0
  rw [this] at hpos
  simp at hpos

/-- **A pointwise strict criterion on the open strip.** RH holds iff
`(Im ξ'(s))² + Re ξ(s) · Re ξ''(s) > 0` for every `s` with `½ < Re s < 1`. -/
theorem riemannHypothesis_iff_strict_laguerre_strip :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      0 < (deriv xi s).im ^ 2 + (xi s).re * (deriv (deriv xi) s).re := by
  rw [riemannHypothesis_iff_strict_laguerre_producer]
  have key : ∀ h x : ℝ, foldFx h x ^ 2 - foldF h x * foldFxx h x =
      (deriv xi (((1 / 2 + h : ℝ) : ℂ) + x * I)).im ^ 2 +
        (xi (((1 / 2 + h : ℝ) : ℂ) + x * I)).re *
          (deriv (deriv xi) (((1 / 2 + h : ℝ) : ℂ) + x * I)).re := by
    intro h x; simp only [foldF, foldFx, foldFxx]; ring
  constructor
  · intro hall s hs1 hs2
    have hs : (((1 / 2 + (s.re - 1 / 2) : ℝ) : ℂ) + (s.im : ℂ) * I) = s := by
      apply Complex.ext <;> simp
    have := hall (s.re - 1 / 2) (by linarith) (by linarith) s.im
    rw [key, hs] at this
    exact this
  · intro hall h hh hh2 x
    rw [key]
    apply hall
    · simp; linarith
    · simp; linarith

/-- **Unconditional half of the criterion.** `(Im ξ'(s))² + Re ξ(s)·Re ξ''(s) > 0` for every `s`
with `Re s ≥ 1`. RH is the extension of this inequality to `½ < Re s < 1`. -/
theorem strict_laguerre_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    0 < (deriv xi s).im ^ 2 + (xi s).re * (deriv (deriv xi) s).re := by
  have hs' : (((1 / 2 + (s.re - 1 / 2) : ℝ) : ℂ) + (s.im : ℂ) * I) = s := by
    apply Complex.ext <;> simp
  have := laguerre_pos_of_half_le (h := s.re - 1 / 2) (by linarith) s.im
  simp only [foldF, foldFx, foldFxx, hs'] at this
  linarith

end

end RHTower
