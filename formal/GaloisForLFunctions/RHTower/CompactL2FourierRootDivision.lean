import GaloisForLFunctions.RHTower.RealL2LipschitzWeakDerivative

/-!
# Compact L² Fourier root division

Route U needs division by selected symmetric real zeros without enlarging Fourier aperture.
This file supplies a time-side construction valid for arbitrary integrable compactly supported
complex data.  Modulate at a zero, integrate once from the left support endpoint, and demodulate.
The zero-mean condition makes the primitive compactly supported, while integration by parts gives
the exact real-frequency factorization.  Iterating at `c` and `-c` produces the odd two-root
descendant at the same compact support and proves the division-free identity

`(w² - c²) * Fourier(hOdd)(w) = w * Fourier(h)(w)`.

No Paley–Wiener converse or pointwise quotient at the roots is used.
-/

open Set MeasureTheory Filter intervalIntegral
open scoped ENNReal SchwartzMap LineDeriv FourierTransform

noncomputable section

namespace RHTower

def routeUCompactPrimitive (b : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in b..x, h t

theorem continuous_routeUCompactPrimitive (b : ℝ) {h : ℝ → ℂ}
    (hh : Integrable h) : Continuous (routeUCompactPrimitive b h) := by
  exact intervalIntegral.continuous_primitive (fun _ _ => hh.intervalIntegrable) b

theorem routeUCompactPrimitive_eq_zero_of_le
    {b d x : ℝ} {h : ℝ → ℂ}
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0) (hx : x ≤ b) :
    routeUCompactPrimitive b h x = 0 := by
  rw [routeUCompactPrimitive]
  calc
    (∫ t in b..x, h t) = ∫ t in b..x, 0 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [hsupp t]
      rw [uIcc_of_ge hx] at ht
      exact Or.inl ht.2
    _ = 0 := by simp

theorem routeUCompactPrimitive_eq_zero_of_ge
    {b d x : ℝ} {h : ℝ → ℂ} (_hbd : b ≤ d)
    (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : ∫ y in b..d, h y = 0) (hx : d ≤ x) :
    routeUCompactPrimitive b h x = 0 := by
  rw [routeUCompactPrimitive]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hh.intervalIntegrable hh.intervalIntegrable, hzero, zero_add]
  calc
    (∫ t in d..x, h t) = ∫ t in d..x, 0 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [hsupp t]
      rw [uIcc_of_le hx] at ht
      exact Or.inr ht.1
    _ = 0 := by simp

theorem hasCompactSupport_routeUCompactPrimitive
    {b d : ℝ} {h : ℝ → ℂ} (hh : Integrable h) (hbd : b ≤ d)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : ∫ y in b..d, h y = 0) :
    HasCompactSupport (routeUCompactPrimitive b h) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact routeUCompactPrimitive_eq_zero_of_le hsupp hx.le
  · exact routeUCompactPrimitive_eq_zero_of_ge hbd hh hsupp hzero hx.le

theorem memLp_routeUCompactPrimitive
    {b d : ℝ} {h : ℝ → ℂ} (hh : Integrable h) (hbd : b ≤ d)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : ∫ y in b..d, h y = 0) :
    MemLp (routeUCompactPrimitive b h) 2 (volume : Measure ℝ) :=
  (continuous_routeUCompactPrimitive b hh).memLp_of_hasCompactSupport
    (hasCompactSupport_routeUCompactPrimitive hh hbd hsupp hzero)

private theorem deriv_re_schwartz_cp (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (fun y : ℝ => (φ y).re) x = (deriv (φ : ℝ → ℂ) x).re := by
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (φ.hasDerivAt x)).deriv

private theorem deriv_im_schwartz_cp (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (fun y : ℝ => (φ y).im) x = (deriv (φ : ℝ → ℂ) x).im := by
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (φ.hasDerivAt x)).deriv

private theorem routeUCompactPrimitive_re
    {b : ℝ} {h : ℝ → ℂ} (hh : Integrable h) (x : ℝ) :
    (routeUCompactPrimitive b h x).re =
      ∫ t in b..x, (h t).re := by
  rw [routeUCompactPrimitive]
  exact (Complex.reCLM.intervalIntegral_comp_comm hh.intervalIntegrable).symm

private theorem routeUCompactPrimitive_im
    {b : ℝ} {h : ℝ → ℂ} (hh : Integrable h) (x : ℝ) :
    (routeUCompactPrimitive b h x).im =
      ∫ t in b..x, (h t).im := by
  rw [routeUCompactPrimitive]
  exact (Complex.imCLM.intervalIntegral_comp_comm hh.intervalIntegrable).symm

private theorem integral_schwartz_coord_mul_compactPrimitive
    {b d : ℝ} (hbd : b ≤ d) {k : ℝ → ℝ} (hk : Integrable k)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → k y = 0)
    (hzero : ∫ y in b..d, k y = 0)
    (q : ℝ → ℝ) (q' : ℝ → ℝ)
    (hqdiff : ContDiff ℝ (⊤ : ℕ∞) q)
    (hq' : ∀ x, deriv q x = q' x) :
    (∫ x : ℝ, q x * k x) =
      -∫ x : ℝ, q' x * (∫ t in b..x, k t) := by
  let p : ℝ → ℝ := fun x => ∫ t in b..x, k t
  have hpAC : AbsolutelyContinuousOnInterval p b d :=
    hk.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hqAC : AbsolutelyContinuousOnInterval q b d :=
    ContDiffOn.absolutelyContinuousOnInterval (hqdiff.contDiffOn.of_le (by simp))
  have hderiv : ∀ᵐ x : ℝ, x ∈ uIoc b d → deriv p x = k x := by
    filter_upwards [hk.intervalIntegrable.ae_hasDerivAt_integral] with x hx hmem
    exact (hx (uIoc_subset_uIcc hmem) b left_mem_uIcc).deriv
  have hibp := hqAC.integral_mul_deriv_eq_deriv_mul hpAC
  have hleft : (∫ x in b..d, q x * k x) =
      ∫ x in b..d, q x * deriv p x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with x hx hmem
    rw [hx hmem]
  have hpB : p b = 0 := by simp [p]
  have hpD : p d = 0 := by simpa [p] using hzero
  have hfinite : (∫ x in b..d, q x * k x) =
      -∫ x in b..d, q' x * p x := by
    rw [hleft, hibp, hpB, hpD, mul_zero, mul_zero, sub_self, zero_sub]
    apply congrArg Neg.neg
    apply intervalIntegral.integral_congr
    intro x hx
    simp only
    rw [hq' x]
  have hkfull : (∫ x : ℝ, q x * k x) = ∫ x in b..d, q x * k x := by
    rw [intervalIntegral.integral_of_le hbd]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [mul_eq_zero]
    right
    apply hsupp x
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx.le
  have hpzero : ∀ x, x ≤ b ∨ d ≤ x → p x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · calc
        p x = ∫ t in b..x, 0 := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_ge hx] at ht
          rw [hsupp t (Or.inl ht.2)]
        _ = 0 := by simp
    · rw [show p x = ∫ t in b..x, k t by rfl,
        ← intervalIntegral.integral_add_adjacent_intervals
          hk.intervalIntegrable hk.intervalIntegrable, hzero, zero_add]
      calc
        (∫ t in d..x, k t) = ∫ t in d..x, 0 := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hx] at ht
          rw [hsupp t (Or.inr ht.1)]
        _ = 0 := by simp
  have hpfull : (∫ x : ℝ, q' x * p x) = ∫ x in b..d, q' x * p x := by
    rw [intervalIntegral.integral_of_le hbd]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [mul_eq_zero]
    right
    apply hpzero x
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx.le
  rw [hkfull, hpfull]
  exact hfinite

theorem routeUCompactPrimitive_weakDerivative
    {b d : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ}
    (hh : Integrable h) (hh2 : MemLp h 2 (volume : Measure ℝ))
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : ∫ y in b..d, h y = 0) :
    ∂_{(1 : ℝ)}
        ((memLp_routeUCompactPrimitive hh hbd hsupp hzero).toLp
          (routeUCompactPrimitive b h) : 𝓢'(ℝ, ℂ)) =
      (hh2.toLp h : 𝓢'(ℝ, ℂ)) := by
  let P : Lp ℂ 2 (volume : Measure ℝ) :=
    (memLp_routeUCompactPrimitive hh hbd hsupp hzero).toLp
      (routeUCompactPrimitive b h)
  let H : Lp ℂ 2 (volume : Measure ℝ) := hh2.toLp h
  ext φ
  rw [TemperedDistribution.lineDerivOp_apply_apply]
  simp only [MeasureTheory.Lp.toTemperedDistribution_apply]
  have hPae : (P : ℝ → ℂ) =ᵐ[volume] routeUCompactPrimitive b h :=
    (memLp_routeUCompactPrimitive hh hbd hsupp hzero).coeFn_toLp
  have hHae : (H : ℝ → ℂ) =ᵐ[volume] h := hh2.coeFn_toLp
  have hhRe : Integrable fun x => (h x).re := hh.re
  have hhIm : Integrable fun x => (h x).im := hh.im
  have hsuppRe : ∀ y, y ≤ b ∨ d ≤ y → (h y).re = 0 := by
    intro y hy; rw [hsupp y hy]; simp
  have hsuppIm : ∀ y, y ≤ b ∨ d ≤ y → (h y).im = 0 := by
    intro y hy; rw [hsupp y hy]; simp
  have hzeroRe : ∫ y in b..d, (h y).re = 0 := by
    rw [← routeUCompactPrimitive_re hh d, routeUCompactPrimitive, hzero]
    simp
  have hzeroIm : ∫ y in b..d, (h y).im = 0 := by
    rw [← routeUCompactPrimitive_im hh d, routeUCompactPrimitive, hzero]
    simp
  have hre := integral_schwartz_coord_mul_compactPrimitive hbd hhRe hsuppRe hzeroRe
    (fun x => (φ x).re) (fun x => (deriv (φ : ℝ → ℂ) x).re)
    (Complex.reCLM.contDiff.comp (φ.smooth ⊤)) (deriv_re_schwartz_cp φ)
  have him := integral_schwartz_coord_mul_compactPrimitive hbd hhIm hsuppIm hzeroIm
    (fun x => (φ x).im) (fun x => (deriv (φ : ℝ → ℂ) x).im)
    (Complex.imCLM.contDiff.comp (φ.smooth ⊤)) (deriv_im_schwartz_cp φ)
  have hreCross := integral_schwartz_coord_mul_compactPrimitive hbd hhIm hsuppIm hzeroIm
    (fun x => (φ x).re) (fun x => (deriv (φ : ℝ → ℂ) x).re)
    (Complex.reCLM.contDiff.comp (φ.smooth ⊤)) (deriv_re_schwartz_cp φ)
  have himCross := integral_schwartz_coord_mul_compactPrimitive hbd hhRe hsuppRe hzeroRe
    (fun x => (φ x).im) (fun x => (deriv (φ : ℝ → ℂ) x).im)
    (Complex.imCLM.contDiff.comp (φ.smooth ⊤)) (deriv_im_schwartz_cp φ)
  have hreP : (∫ x : ℝ, (φ x).re * (h x).re) =
      -∫ x : ℝ, (deriv (φ : ℝ → ℂ) x).re *
        (routeUCompactPrimitive b h x).re := by
    simpa only [routeUCompactPrimitive_re hh] using hre
  have himP : (∫ x : ℝ, (φ x).im * (h x).im) =
      -∫ x : ℝ, (deriv (φ : ℝ → ℂ) x).im *
        (routeUCompactPrimitive b h x).im := by
    simpa only [routeUCompactPrimitive_im hh] using him
  have hreCrossP : (∫ x : ℝ, (φ x).re * (h x).im) =
      -∫ x : ℝ, (deriv (φ : ℝ → ℂ) x).re *
        (routeUCompactPrimitive b h x).im := by
    simpa only [routeUCompactPrimitive_im hh] using hreCross
  have himCrossP : (∫ x : ℝ, (φ x).im * (h x).re) =
      -∫ x : ℝ, (deriv (φ : ℝ → ℂ) x).im *
        (routeUCompactPrimitive b h x).re := by
    simpa only [routeUCompactPrimitive_re hh] using himCross
  calc
    ∫ x : ℝ, (-∂_{(1 : ℝ)} φ) x • (P : ℝ → ℂ) x =
        -∫ x : ℝ, deriv (φ : ℝ → ℂ) x * routeUCompactPrimitive b h x := by
      rw [← MeasureTheory.integral_neg]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hPae] with x hx
      rw [hx]
      change (-((∂_{(1 : ℝ)} φ) x)) * routeUCompactPrimitive b h x =
        -(deriv (φ : ℝ → ℂ) x * routeUCompactPrimitive b h x)
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv]
      ring
    _ = ∫ x : ℝ, φ x * h x := by
      have hDP : Integrable (fun x : ℝ =>
          deriv (φ : ℝ → ℂ) x * routeUCompactPrimitive b h x) := by
        let dφ : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ φ
        have hdφ2 : MemLp (dφ : ℝ → ℂ) 2 (volume : Measure ℝ) :=
          dφ.memLp 2 (volume : Measure ℝ)
        have hp2 := memLp_routeUCompactPrimitive hh hbd hsupp hzero
        apply (MemLp.integrable_mul hdφ2 hp2).congr
        filter_upwards with x
        change ((SchwartzMap.derivCLM ℂ ℂ) φ) x * routeUCompactPrimitive b h x = _
        rw [SchwartzMap.derivCLM_apply]
      have hφh : Integrable (fun x : ℝ => φ x * h x) :=
        MemLp.integrable_mul (φ.memLp 2 (volume : Measure ℝ)) hh2
      have hDPre : (∫ x : ℝ,
          deriv (φ : ℝ → ℂ) x * routeUCompactPrimitive b h x).re =
          ∫ x : ℝ, (deriv (φ : ℝ → ℂ) x * routeUCompactPrimitive b h x).re :=
        (integral_re hDP).symm
      have hDPim : (∫ x : ℝ,
          deriv (φ : ℝ → ℂ) x * routeUCompactPrimitive b h x).im =
          ∫ x : ℝ, (deriv (φ : ℝ → ℂ) x * routeUCompactPrimitive b h x).im :=
        (integral_im hDP).symm
      have hφhre : (∫ x : ℝ, φ x * h x).re =
          ∫ x : ℝ, (φ x * h x).re := (integral_re hφh).symm
      have hφhim : (∫ x : ℝ, φ x * h x).im =
          ∫ x : ℝ, (φ x * h x).im := (integral_im hφh).symm
      let dφ : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ φ
      have hdφ2 : MemLp (dφ : ℝ → ℂ) 2 (volume : Measure ℝ) :=
        dφ.memLp 2 (volume : Measure ℝ)
      have hp2 := memLp_routeUCompactPrimitive hh hbd hsupp hzero
      have hDrPr : Integrable (fun x : ℝ =>
          (deriv (φ : ℝ → ℂ) x).re * (routeUCompactPrimitive b h x).re) := by
        apply (MemLp.integrable_mul hdφ2.re hp2.re).congr
        filter_upwards with x
        simp [dφ, SchwartzMap.derivCLM_apply]
      have hDiPi : Integrable (fun x : ℝ =>
          (deriv (φ : ℝ → ℂ) x).im * (routeUCompactPrimitive b h x).im) := by
        apply (MemLp.integrable_mul hdφ2.im hp2.im).congr
        filter_upwards with x
        simp [dφ, SchwartzMap.derivCLM_apply]
      have hDrPi : Integrable (fun x : ℝ =>
          (deriv (φ : ℝ → ℂ) x).re * (routeUCompactPrimitive b h x).im) := by
        apply (MemLp.integrable_mul hdφ2.re hp2.im).congr
        filter_upwards with x
        simp [dφ, SchwartzMap.derivCLM_apply]
      have hDiPr : Integrable (fun x : ℝ =>
          (deriv (φ : ℝ → ℂ) x).im * (routeUCompactPrimitive b h x).re) := by
        apply (MemLp.integrable_mul hdφ2.im hp2.re).congr
        filter_upwards with x
        simp [dφ, SchwartzMap.derivCLM_apply]
      have hQrHr : Integrable (fun x : ℝ => (φ x).re * (h x).re) :=
        MemLp.integrable_mul (φ.memLp 2 (volume : Measure ℝ)).re hh2.re
      have hQiHi : Integrable (fun x : ℝ => (φ x).im * (h x).im) :=
        MemLp.integrable_mul (φ.memLp 2 (volume : Measure ℝ)).im hh2.im
      have hQrHi : Integrable (fun x : ℝ => (φ x).re * (h x).im) :=
        MemLp.integrable_mul (φ.memLp 2 (volume : Measure ℝ)).re hh2.im
      have hQiHr : Integrable (fun x : ℝ => (φ x).im * (h x).re) :=
        MemLp.integrable_mul (φ.memLp 2 (volume : Measure ℝ)).im hh2.re
      apply Complex.ext
      · simp only [Complex.neg_re]
        rw [hDPre, hφhre]
        simp_rw [Complex.mul_re]
        rw [integral_sub hDrPr hDiPi, integral_sub hQrHr hQiHi]
        linarith [hreP, himP]
      · simp only [Complex.neg_im]
        rw [hDPim, hφhim]
        simp_rw [Complex.mul_im]
        rw [integral_add hDrPi hDiPr, integral_add hQrHi hQiHr]
        linarith [hreCrossP, himCrossP]
    _ = ∫ x : ℝ, φ x • (H : ℝ → ℂ) x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hHae] with x hx
      rw [hx]
      rfl

/-! ## Exact real-frequency zero division -/

def routeURealFourier (h : ℝ → ℂ) (w : ℝ) : ℂ :=
  ∫ x : ℝ, h x * Complex.exp (Complex.I * (w : ℂ) * (x : ℂ))

/-- The real-frequency Fourier transform of an integrable source is continuous.  This is the
pointwise regularity needed to recover values at a removed root from the exact factor identity
away from that root. -/
theorem continuous_routeURealFourier {h : ℝ → ℂ} (hh : Integrable h) :
    Continuous (routeURealFourier h) := by
  have hfourier : Continuous (𝓕 h) := by
    have hcont := VectorFourier.fourierIntegral_continuous
      (V := ℝ) (W := ℝ) (E := ℂ)
      (e := Real.fourierChar) (μ := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hh
    refine hcont.congr fun ξ => ?_
    rw [Real.fourier_eq]
    rfl
  have heq : routeURealFourier h = fun w : ℝ => 𝓕 h (-w / (2 * Real.pi)) := by
    funext w
    rw [routeURealFourier, Real.fourier_real_eq_integral_exp_smul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [mul_comm]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  exact hfourier.comp (continuous_id.neg.div_const (2 * Real.pi))

def routeURealFourierPhase (w x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (w : ℂ) * (x : ℂ))

theorem norm_routeURealFourierPhase (w x : ℝ) :
    ‖routeURealFourierPhase w x‖ = 1 := by
  rw [routeURealFourierPhase, Complex.norm_exp]
  simp [Complex.mul_re]

theorem hasDerivAt_routeURealFourierPhase (w x : ℝ) :
    HasDerivAt (routeURealFourierPhase w)
      (Complex.I * (w : ℂ) * routeURealFourierPhase w x) x := by
  unfold routeURealFourierPhase
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  convert ((hx.const_mul (Complex.I * (w : ℂ))).cexp) using 1
  all_goals ring

theorem contDiff_routeURealFourierPhase (w : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (routeURealFourierPhase w) := by
  unfold routeURealFourierPhase
  exact Complex.contDiff_exp.comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_id))

theorem integrable_mul_routeURealFourierPhase {h : ℝ → ℂ}
    (hh : Integrable h) (w : ℝ) :
    Integrable (fun x : ℝ => h x * routeURealFourierPhase w x) := by
  refine Integrable.mono hh ?_ ?_
  · exact hh.aestronglyMeasurable.mul
      (contDiff_routeURealFourierPhase w).continuous.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, norm_routeURealFourierPhase, mul_one]

def routeURealModulatedSource (c : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  h x * routeURealFourierPhase c x

theorem integrable_routeURealModulatedSource {c : ℝ} {h : ℝ → ℂ}
    (hh : Integrable h) : Integrable (routeURealModulatedSource c h) := by
  refine Integrable.mono hh ?_ ?_
  · exact hh.aestronglyMeasurable.mul
      (contDiff_routeURealFourierPhase c).continuous.aestronglyMeasurable
  · filter_upwards with x
    rw [routeURealModulatedSource, norm_mul, norm_routeURealFourierPhase, mul_one]

theorem memLp_routeURealModulatedSource {c : ℝ} {h : ℝ → ℂ}
    (hh : MemLp h 2 (volume : Measure ℝ)) :
    MemLp (routeURealModulatedSource c h) 2 (volume : Measure ℝ) := by
  refine MemLp.mono hh ?_ ?_
  · exact hh.1.mul (contDiff_routeURealFourierPhase c).continuous.aestronglyMeasurable
  · filter_upwards with x
    rw [routeURealModulatedSource, norm_mul, norm_routeURealFourierPhase, mul_one]

theorem routeURealModulatedSource_support
    {b d c : ℝ} {h : ℝ → ℂ}
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0) :
    ∀ y, y ≤ b ∨ d ≤ y → routeURealModulatedSource c h y = 0 := by
  intro y hy
  rw [routeURealModulatedSource, hsupp y hy, zero_mul]

theorem intervalIntegral_routeURealModulatedSource_eq_zero
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ}
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : routeURealFourier h c = 0) :
    ∫ y in b..d, routeURealModulatedSource c h y = 0 := by
  rw [intervalIntegral.integral_of_le hbd]
  have hfull : (∫ y in Ioc b d, routeURealModulatedSource c h y) =
      ∫ y : ℝ, routeURealModulatedSource c h y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    apply routeURealModulatedSource_support hsupp y
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hy
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr hy.le
  rw [hfull]
  change routeURealFourier h c = 0
  simpa only [routeURealFourier, routeURealModulatedSource, routeURealFourierPhase] using hzero

def routeURealRootDividedTime (b c : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  -Complex.I * routeURealFourierPhase (-c) x *
    routeUCompactPrimitive b (routeURealModulatedSource c h) x

theorem continuous_routeURealRootDividedTime
    {b c : ℝ} {h : ℝ → ℂ} (hh : Integrable h) :
    Continuous (routeURealRootDividedTime b c h) := by
  exact (continuous_const.mul (contDiff_routeURealFourierPhase (-c)).continuous).mul
    (continuous_routeUCompactPrimitive b (integrable_routeURealModulatedSource hh))

theorem routeURealRootDividedTime_support
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : routeURealFourier h c = 0) :
    ∀ y, y ≤ b ∨ d ≤ y → routeURealRootDividedTime b c h y = 0 := by
  intro y hy
  rw [routeURealRootDividedTime]
  have hprim : routeUCompactPrimitive b (routeURealModulatedSource c h) y = 0 := by
    rcases hy with hy | hy
    · exact routeUCompactPrimitive_eq_zero_of_le
        (routeURealModulatedSource_support hsupp) hy
    · exact routeUCompactPrimitive_eq_zero_of_ge hbd
        (integrable_routeURealModulatedSource hh)
        (routeURealModulatedSource_support hsupp)
        (intervalIntegral_routeURealModulatedSource_eq_zero hbd hsupp hzero) hy
  rw [hprim, mul_zero]

theorem hasCompactSupport_routeURealRootDividedTime
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : routeURealFourier h c = 0) :
    HasCompactSupport (routeURealRootDividedTime b c h) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro y hy
  apply routeURealRootDividedTime_support hbd hh hsupp hzero y
  simp only [mem_Icc, not_and_or, not_le] at hy
  rcases hy with hy | hy
  · exact Or.inl hy.le
  · exact Or.inr hy.le

theorem integrable_routeURealRootDividedTime
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : routeURealFourier h c = 0) :
    Integrable (routeURealRootDividedTime b c h) :=
  (continuous_routeURealRootDividedTime hh).integrable_of_hasCompactSupport
    (hasCompactSupport_routeURealRootDividedTime hbd hh hsupp hzero)

theorem memLp_routeURealRootDividedTime
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : routeURealFourier h c = 0) :
    MemLp (routeURealRootDividedTime b c h) 2 (volume : Measure ℝ) :=
  (continuous_routeURealRootDividedTime hh).memLp_of_hasCompactSupport
    (hasCompactSupport_routeURealRootDividedTime hbd hh hsupp hzero)

private theorem deriv_re_routeURealFourierPhase (w x : ℝ) :
    deriv (fun y : ℝ => (routeURealFourierPhase w y).re) x =
      (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re := by
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_routeURealFourierPhase w x)).deriv

private theorem deriv_im_routeURealFourierPhase (w x : ℝ) :
    deriv (fun y : ℝ => (routeURealFourierPhase w y).im) x =
      (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im := by
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_routeURealFourierPhase w x)).deriv

private theorem integral_routeURealFourierPhase_mul_modulatedSource
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : routeURealFourier h c = 0) (w : ℝ) :
    (∫ x : ℝ, routeURealFourierPhase w x * routeURealModulatedSource c h x) =
      -∫ x : ℝ, (Complex.I * (w : ℂ) * routeURealFourierPhase w x) *
        routeUCompactPrimitive b (routeURealModulatedSource c h) x := by
  let g : ℝ → ℂ := routeURealModulatedSource c h
  let P : ℝ → ℂ := routeUCompactPrimitive b g
  have hg : Integrable g := integrable_routeURealModulatedSource hh
  have hgsupp : ∀ y, y ≤ b ∨ d ≤ y → g y = 0 :=
    routeURealModulatedSource_support (c := c) hsupp
  have hgzero := intervalIntegral_routeURealModulatedSource_eq_zero hbd hsupp hzero
  have hgRe : Integrable fun x => (g x).re := hg.re
  have hgIm : Integrable fun x => (g x).im := hg.im
  have hgsuppRe : ∀ y, y ≤ b ∨ d ≤ y → (g y).re = 0 := by
    intro y hy; rw [hgsupp y hy]; simp
  have hgsuppIm : ∀ y, y ≤ b ∨ d ≤ y → (g y).im = 0 := by
    intro y hy; rw [hgsupp y hy]; simp
  have hgzeroRe : ∫ y in b..d, (g y).re = 0 := by
    have hcomm := Complex.reCLM.intervalIntegral_comp_comm
      (hg.intervalIntegrable (a := b) (b := d))
    rw [hgzero] at hcomm
    simpa using hcomm
  have hgzeroIm : ∫ y in b..d, (g y).im = 0 := by
    have hcomm := Complex.imCLM.intervalIntegral_comp_comm
      (hg.intervalIntegrable (a := b) (b := d))
    rw [hgzero] at hcomm
    simpa using hcomm
  have hrr := integral_schwartz_coord_mul_compactPrimitive hbd hgRe hgsuppRe hgzeroRe
    (fun x => (routeURealFourierPhase w x).re)
    (fun x => (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re)
    ((Complex.reCLM.contDiff.comp (contDiff_routeURealFourierPhase w)))
    (deriv_re_routeURealFourierPhase w)
  have hii := integral_schwartz_coord_mul_compactPrimitive hbd hgIm hgsuppIm hgzeroIm
    (fun x => (routeURealFourierPhase w x).im)
    (fun x => (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im)
    ((Complex.imCLM.contDiff.comp (contDiff_routeURealFourierPhase w)))
    (deriv_im_routeURealFourierPhase w)
  have hri := integral_schwartz_coord_mul_compactPrimitive hbd hgIm hgsuppIm hgzeroIm
    (fun x => (routeURealFourierPhase w x).re)
    (fun x => (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re)
    ((Complex.reCLM.contDiff.comp (contDiff_routeURealFourierPhase w)))
    (deriv_re_routeURealFourierPhase w)
  have hir := integral_schwartz_coord_mul_compactPrimitive hbd hgRe hgsuppRe hgzeroRe
    (fun x => (routeURealFourierPhase w x).im)
    (fun x => (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im)
    ((Complex.imCLM.contDiff.comp (contDiff_routeURealFourierPhase w)))
    (deriv_im_routeURealFourierPhase w)
  have hPint : Integrable P :=
    (continuous_routeUCompactPrimitive b hg).integrable_of_hasCompactSupport
      (hasCompactSupport_routeUCompactPrimitive hg hbd hgsupp hgzero)
  have hPzero : ∀ x, x ∉ Icc b d → P x = 0 := by
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact routeUCompactPrimitive_eq_zero_of_le hgsupp hx.le
    · exact routeUCompactPrimitive_eq_zero_of_ge hbd hg hgsupp hgzero hx.le
  have hleft : Integrable (fun x : ℝ => routeURealFourierPhase w x * g x) := by
    refine Integrable.mono hg ?_ ?_
    · exact (contDiff_routeURealFourierPhase w).continuous.aestronglyMeasurable.mul hg.1
    · filter_upwards with x
      rw [norm_mul, norm_routeURealFourierPhase, one_mul]
  have hright : Integrable (fun x : ℝ =>
      (Complex.I * (w : ℂ) * routeURealFourierPhase w x) * P x) := by
    refine Integrable.mono (hPint.const_mul (Complex.I * (w : ℂ))) ?_ ?_
    · exact (((continuous_const.mul continuous_const).mul
          (contDiff_routeURealFourierPhase w).continuous).mul
            (continuous_routeUCompactPrimitive b hg)).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul, norm_mul, norm_mul, norm_routeURealFourierPhase]
      simp [mul_comm, mul_left_comm, mul_assoc]
  have hPRe (x : ℝ) : (P x).re = ∫ t in b..x, (g t).re :=
    routeUCompactPrimitive_re hg x
  have hPIm (x : ℝ) : (P x).im = ∫ t in b..x, (g t).im :=
    routeUCompactPrimitive_im hg x
  have hrrP : (∫ x : ℝ, (routeURealFourierPhase w x).re * (g x).re) =
      -∫ x : ℝ, (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).re := by
    simpa only [hPRe] using hrr
  have hiiP : (∫ x : ℝ, (routeURealFourierPhase w x).im * (g x).im) =
      -∫ x : ℝ, (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).im := by
    simpa only [hPIm] using hii
  have hriP : (∫ x : ℝ, (routeURealFourierPhase w x).re * (g x).im) =
      -∫ x : ℝ, (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).im := by
    simpa only [hPIm] using hri
  have hirP : (∫ x : ℝ, (routeURealFourierPhase w x).im * (g x).re) =
      -∫ x : ℝ, (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).re := by
    simpa only [hPRe] using hir
  have hleftRe : (∫ x : ℝ, routeURealFourierPhase w x * g x).re =
      ∫ x : ℝ, (routeURealFourierPhase w x * g x).re := (integral_re hleft).symm
  have hleftIm : (∫ x : ℝ, routeURealFourierPhase w x * g x).im =
      ∫ x : ℝ, (routeURealFourierPhase w x * g x).im := (integral_im hleft).symm
  have hrightRe : (∫ x : ℝ,
      (Complex.I * (w : ℂ) * routeURealFourierPhase w x) * P x).re =
      ∫ x : ℝ, ((Complex.I * (w : ℂ) * routeURealFourierPhase w x) * P x).re :=
    (integral_re hright).symm
  have hrightIm : (∫ x : ℝ,
      (Complex.I * (w : ℂ) * routeURealFourierPhase w x) * P x).im =
      ∫ x : ℝ, ((Complex.I * (w : ℂ) * routeURealFourierPhase w x) * P x).im :=
    (integral_im hright).symm
  change (∫ x : ℝ, routeURealFourierPhase w x * g x) =
    -∫ x : ℝ, (Complex.I * (w : ℂ) * routeURealFourierPhase w x) * P x
  -- Split the complex integral coordinatewise; all remaining terms are dominated by `hright`.
  apply Complex.ext
  · simp only [Complex.neg_re]
    rw [hleftRe, hrightRe]
    change (∫ x : ℝ,
      (routeURealFourierPhase w x).re * (g x).re -
        (routeURealFourierPhase w x).im * (g x).im) =
      -(∫ x : ℝ,
        (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).re -
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).im)
    have hA : Integrable (fun x : ℝ =>
        (routeURealFourierPhase w x).re * (g x).re) := by
      refine Integrable.mono hgRe
        ((Complex.continuous_re.comp
          (contDiff_routeURealFourierPhase w).continuous).aestronglyMeasurable.mul hgRe.1) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have hp := Complex.abs_re_le_norm (routeURealFourierPhase w x)
      rw [norm_routeURealFourierPhase] at hp
      nlinarith [abs_nonneg ((g x).re)]
    have hB : Integrable (fun x : ℝ =>
        (routeURealFourierPhase w x).im * (g x).im) := by
      refine Integrable.mono hgIm
        ((Complex.continuous_im.comp
          (contDiff_routeURealFourierPhase w).continuous).aestronglyMeasurable.mul hgIm.1) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have hp := Complex.abs_im_le_norm (routeURealFourierPhase w x)
      rw [norm_routeURealFourierPhase] at hp
      nlinarith [abs_nonneg ((g x).im)]
    have hC : Integrable (fun x : ℝ =>
        (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).re) := by
      have hcont : Continuous (fun x : ℝ =>
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).re) :=
        (Complex.continuous_re.comp
          (continuous_const.mul (contDiff_routeURealFourierPhase w).continuous)).mul
            (Complex.continuous_re.comp (continuous_routeUCompactPrimitive b hg))
      exact hcont.integrable_of_hasCompactSupport
        (HasCompactSupport.intro isCompact_Icc fun x hx => by rw [hPzero x hx]; simp)
    have hD : Integrable (fun x : ℝ =>
        (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).im) := by
      have hcont : Continuous (fun x : ℝ =>
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).im) :=
        (Complex.continuous_im.comp
          (continuous_const.mul (contDiff_routeURealFourierPhase w).continuous)).mul
            (Complex.continuous_im.comp (continuous_routeUCompactPrimitive b hg))
      exact hcont.integrable_of_hasCompactSupport
        (HasCompactSupport.intro isCompact_Icc fun x hx => by rw [hPzero x hx]; simp)
    calc
      (∫ x : ℝ,
          (routeURealFourierPhase w x).re * (g x).re -
            (routeURealFourierPhase w x).im * (g x).im) =
        (∫ x : ℝ, (routeURealFourierPhase w x).re * (g x).re) -
          ∫ x : ℝ, (routeURealFourierPhase w x).im * (g x).im :=
            integral_sub hA hB
      _ = -((∫ x : ℝ,
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).re) -
            ∫ x : ℝ,
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).im) := by
            linarith [hrrP, hiiP]
      _ = -(∫ x : ℝ,
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).re -
            (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).im) := by
              rw [integral_sub hC hD]
  · simp only [Complex.neg_im]
    rw [hleftIm, hrightIm]
    change (∫ x : ℝ,
      (routeURealFourierPhase w x).re * (g x).im +
        (routeURealFourierPhase w x).im * (g x).re) =
      -(∫ x : ℝ,
        (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).im +
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).re)
    have hA : Integrable (fun x : ℝ =>
        (routeURealFourierPhase w x).re * (g x).im) := by
      refine Integrable.mono hgIm
        ((Complex.continuous_re.comp
          (contDiff_routeURealFourierPhase w).continuous).aestronglyMeasurable.mul hgIm.1) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have hp := Complex.abs_re_le_norm (routeURealFourierPhase w x)
      rw [norm_routeURealFourierPhase] at hp
      nlinarith [abs_nonneg ((g x).im)]
    have hB : Integrable (fun x : ℝ =>
        (routeURealFourierPhase w x).im * (g x).re) := by
      refine Integrable.mono hgRe
        ((Complex.continuous_im.comp
          (contDiff_routeURealFourierPhase w).continuous).aestronglyMeasurable.mul hgRe.1) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have hp := Complex.abs_im_le_norm (routeURealFourierPhase w x)
      rw [norm_routeURealFourierPhase] at hp
      nlinarith [abs_nonneg ((g x).re)]
    have hC : Integrable (fun x : ℝ =>
        (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).im) := by
      have hcont : Continuous (fun x : ℝ =>
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).im) :=
        (Complex.continuous_re.comp
          (continuous_const.mul (contDiff_routeURealFourierPhase w).continuous)).mul
            (Complex.continuous_im.comp (continuous_routeUCompactPrimitive b hg))
      exact hcont.integrable_of_hasCompactSupport
        (HasCompactSupport.intro isCompact_Icc fun x hx => by rw [hPzero x hx]; simp)
    have hD : Integrable (fun x : ℝ =>
        (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).re) := by
      have hcont : Continuous (fun x : ℝ =>
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).re) :=
        (Complex.continuous_im.comp
          (continuous_const.mul (contDiff_routeURealFourierPhase w).continuous)).mul
            (Complex.continuous_re.comp (continuous_routeUCompactPrimitive b hg))
      exact hcont.integrable_of_hasCompactSupport
        (HasCompactSupport.intro isCompact_Icc fun x hx => by rw [hPzero x hx]; simp)
    calc
      (∫ x : ℝ,
          (routeURealFourierPhase w x).re * (g x).im +
            (routeURealFourierPhase w x).im * (g x).re) =
        (∫ x : ℝ, (routeURealFourierPhase w x).re * (g x).im) +
          ∫ x : ℝ, (routeURealFourierPhase w x).im * (g x).re :=
            integral_add hA hB
      _ = -((∫ x : ℝ,
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).im) +
            ∫ x : ℝ,
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).re) := by
            linarith [hriP, hirP]
      _ = -(∫ x : ℝ,
          (Complex.I * (w : ℂ) * routeURealFourierPhase w x).re * (P x).im +
            (Complex.I * (w : ℂ) * routeURealFourierPhase w x).im * (P x).re) := by
              rw [integral_add hC hD]

theorem routeURealRootDividedTime_fourier_factor
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hzero : routeURealFourier h c = 0) (w : ℝ) :
    ((w - c : ℝ) : ℂ) * routeURealFourier (routeURealRootDividedTime b c h) w =
      routeURealFourier h w := by
  have hibp := integral_routeURealFourierPhase_mul_modulatedSource
    hbd hh hsupp hzero (w - c)
  have hleft : (∫ x : ℝ,
      routeURealFourierPhase (w - c) x * routeURealModulatedSource c h x) =
      routeURealFourier h w := by
    rw [routeURealFourier]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [routeURealModulatedSource]
    rw [show routeURealFourierPhase (w - c) x *
        (h x * routeURealFourierPhase c x) =
      h x * (routeURealFourierPhase (w - c) x *
        routeURealFourierPhase c x) by ring]
    congr 1
    rw [routeURealFourierPhase, routeURealFourierPhase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hright : routeURealFourier (routeURealRootDividedTime b c h) w =
      -Complex.I * ∫ x : ℝ,
        routeURealFourierPhase (w - c) x *
          routeUCompactPrimitive b (routeURealModulatedSource c h) x := by
    rw [routeURealFourier]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [routeURealRootDividedTime]
    change (-Complex.I * routeURealFourierPhase (-c) x *
      routeUCompactPrimitive b (routeURealModulatedSource c h) x) *
        Complex.exp (Complex.I * (w : ℂ) * (x : ℂ)) =
      -Complex.I * (routeURealFourierPhase (w - c) x *
        routeUCompactPrimitive b (routeURealModulatedSource c h) x)
    rw [show (-Complex.I * routeURealFourierPhase (-c) x *
        routeUCompactPrimitive b (routeURealModulatedSource c h) x) *
          Complex.exp (Complex.I * (w : ℂ) * (x : ℂ)) =
      -Complex.I * (routeURealFourierPhase (-c) x *
        Complex.exp (Complex.I * (w : ℂ) * (x : ℂ))) *
          routeUCompactPrimitive b (routeURealModulatedSource c h) x by ring]
    have hphase : routeURealFourierPhase (-c) x *
        Complex.exp (Complex.I * (w : ℂ) * (x : ℂ)) =
      routeURealFourierPhase (w - c) x := by
      rw [routeURealFourierPhase, routeURealFourierPhase, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hphase]
    ring
  rw [hright]
  have hibp' : routeURealFourier h w =
      -∫ x : ℝ, (Complex.I * ((w - c : ℝ) : ℂ) *
        routeURealFourierPhase (w - c) x) *
          routeUCompactPrimitive b (routeURealModulatedSource c h) x := by
    rw [← hleft]
    exact hibp
  rw [hibp']
  calc
    ((w - c : ℝ) : ℂ) *
        (-Complex.I * ∫ x : ℝ, routeURealFourierPhase (w - c) x *
          routeUCompactPrimitive b (routeURealModulatedSource c h) x) =
      ∫ x : ℝ, ((w - c : ℝ) : ℂ) *
        (-Complex.I * (routeURealFourierPhase (w - c) x *
          routeUCompactPrimitive b (routeURealModulatedSource c h) x)) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = ∫ x : ℝ, -((Complex.I * ((w - c : ℝ) : ℂ) *
        routeURealFourierPhase (w - c) x) *
          routeUCompactPrimitive b (routeURealModulatedSource c h) x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      ring
    _ = -∫ x : ℝ, (Complex.I * ((w - c : ℝ) : ℂ) *
        routeURealFourierPhase (w - c) x) *
          routeUCompactPrimitive b (routeURealModulatedSource c h) x := by
      rw [MeasureTheory.integral_neg]

theorem routeURealRootDividedTime_fourier_zero_of_second_zero
    {b d c w : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hw : routeURealFourier h w = 0)
    (hwc : w ≠ c) :
    routeURealFourier (routeURealRootDividedTime b c h) w = 0 := by
  have hfactor := routeURealRootDividedTime_fourier_factor hbd hh hsupp hc w
  rw [hw] at hfactor
  exact (mul_eq_zero.mp hfactor).resolve_left (by exact_mod_cast sub_ne_zero.mpr hwc)

/-! ## Two-root odd descendant -/

def routeURealTwiceRootDividedTime (b c : ℝ) (h : ℝ → ℂ) : ℝ → ℂ :=
  routeURealRootDividedTime b (-c) (routeURealRootDividedTime b c h)

def routeURealOddRootDividedTime (b c : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  routeURealRootDividedTime b c h x -
    (c : ℂ) * routeURealTwiceRootDividedTime b c h x

theorem routeURealTwiceRootDividedTime_support
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    ∀ y, y ≤ b ∨ d ≤ y → routeURealTwiceRootDividedTime b c h y = 0 := by
  let h₁ : ℝ → ℂ := routeURealRootDividedTime b c h
  have hh₁ : Integrable h₁ := integrable_routeURealRootDividedTime hbd hh hsupp hc
  have hsupp₁ : ∀ y, y ≤ b ∨ d ≤ y → h₁ y = 0 :=
    routeURealRootDividedTime_support hbd hh hsupp hc
  have hzero₁ : routeURealFourier h₁ (-c) = 0 :=
    routeURealRootDividedTime_fourier_zero_of_second_zero hbd hh hsupp hc hnegc (by
      intro heq
      apply hc0
      linarith)
  exact routeURealRootDividedTime_support hbd hh₁ hsupp₁ hzero₁

theorem integrable_routeURealTwiceRootDividedTime
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    Integrable (routeURealTwiceRootDividedTime b c h) := by
  let h₁ : ℝ → ℂ := routeURealRootDividedTime b c h
  have hh₁ : Integrable h₁ := integrable_routeURealRootDividedTime hbd hh hsupp hc
  have hsupp₁ : ∀ y, y ≤ b ∨ d ≤ y → h₁ y = 0 :=
    routeURealRootDividedTime_support hbd hh hsupp hc
  have hzero₁ : routeURealFourier h₁ (-c) = 0 :=
    routeURealRootDividedTime_fourier_zero_of_second_zero hbd hh hsupp hc hnegc (by
      intro heq
      apply hc0
      linarith)
  exact integrable_routeURealRootDividedTime hbd hh₁ hsupp₁ hzero₁

theorem memLp_routeURealTwiceRootDividedTime
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    MemLp (routeURealTwiceRootDividedTime b c h) 2 (volume : Measure ℝ) := by
  let h₁ : ℝ → ℂ := routeURealRootDividedTime b c h
  have hh₁ : Integrable h₁ := integrable_routeURealRootDividedTime hbd hh hsupp hc
  have hsupp₁ : ∀ y, y ≤ b ∨ d ≤ y → h₁ y = 0 :=
    routeURealRootDividedTime_support hbd hh hsupp hc
  have hzero₁ : routeURealFourier h₁ (-c) = 0 :=
    routeURealRootDividedTime_fourier_zero_of_second_zero hbd hh hsupp hc hnegc (by
      intro heq
      apply hc0
      linarith)
  exact memLp_routeURealRootDividedTime hbd hh₁ hsupp₁ hzero₁

theorem routeURealOddRootDividedTime_support
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    ∀ y, y ≤ b ∨ d ≤ y → routeURealOddRootDividedTime b c h y = 0 := by
  intro y hy
  rw [routeURealOddRootDividedTime,
    routeURealRootDividedTime_support hbd hh hsupp hc y hy,
    routeURealTwiceRootDividedTime_support hbd hh hsupp hc hnegc hc0 y hy]
  simp

theorem integrable_routeURealOddRootDividedTime
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    Integrable (routeURealOddRootDividedTime b c h) := by
  exact (integrable_routeURealRootDividedTime hbd hh hsupp hc).sub
    ((integrable_routeURealTwiceRootDividedTime hbd hh hsupp hc hnegc hc0).const_mul c)

theorem memLp_routeURealOddRootDividedTime
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    MemLp (routeURealOddRootDividedTime b c h) 2 (volume : Measure ℝ) := by
  have h₁ := memLp_routeURealRootDividedTime hbd hh hsupp hc
  have h₂ := memLp_routeURealTwiceRootDividedTime hbd hh hsupp hc hnegc hc0
  apply MemLp.ae_eq _ (h₁.sub (h₂.const_mul c))
  filter_upwards with x
  rfl

theorem routeURealTwiceRootDividedTime_fourier_factors
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) (w : ℝ) :
    ((w + c : ℝ) : ℂ) * routeURealFourier (routeURealTwiceRootDividedTime b c h) w =
      routeURealFourier (routeURealRootDividedTime b c h) w := by
  let h₁ : ℝ → ℂ := routeURealRootDividedTime b c h
  have hh₁ : Integrable h₁ := integrable_routeURealRootDividedTime hbd hh hsupp hc
  have hsupp₁ : ∀ y, y ≤ b ∨ d ≤ y → h₁ y = 0 :=
    routeURealRootDividedTime_support hbd hh hsupp hc
  have hzero₁ : routeURealFourier h₁ (-c) = 0 :=
    routeURealRootDividedTime_fourier_zero_of_second_zero hbd hh hsupp hc hnegc (by
      intro heq
      apply hc0
      linarith)
  simpa [routeURealTwiceRootDividedTime, h₁, sub_eq_add_neg] using
    routeURealRootDividedTime_fourier_factor hbd hh₁ hsupp₁ hzero₁ w

theorem routeURealOddRootDividedTime_fourier_eq_mul_twice
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) (w : ℝ) :
    routeURealFourier (routeURealOddRootDividedTime b c h) w =
      (w : ℂ) * routeURealFourier (routeURealTwiceRootDividedTime b c h) w := by
  have hh₁ := integrable_routeURealRootDividedTime hbd hh hsupp hc
  have hh₂ := integrable_routeURealTwiceRootDividedTime hbd hh hsupp hc hnegc hc0
  have hfactor := routeURealTwiceRootDividedTime_fourier_factors
    hbd hh hsupp hc hnegc hc0 w
  have hsplit :
      routeURealFourier (routeURealOddRootDividedTime b c h) w =
        routeURealFourier (routeURealRootDividedTime b c h) w -
          (c : ℂ) * routeURealFourier (routeURealTwiceRootDividedTime b c h) w := by
    change (∫ x : ℝ, (routeURealRootDividedTime b c h x -
        (c : ℂ) * routeURealTwiceRootDividedTime b c h x) *
          routeURealFourierPhase w x) =
      (∫ x : ℝ, routeURealRootDividedTime b c h x * routeURealFourierPhase w x) -
        (c : ℂ) * ∫ x : ℝ, routeURealTwiceRootDividedTime b c h x *
          routeURealFourierPhase w x
    simp_rw [sub_mul]
    calc
      (∫ x : ℝ, routeURealRootDividedTime b c h x * routeURealFourierPhase w x -
          (c : ℂ) * routeURealTwiceRootDividedTime b c h x *
            routeURealFourierPhase w x) =
        (∫ x : ℝ, routeURealRootDividedTime b c h x * routeURealFourierPhase w x) -
          ∫ x : ℝ, (c : ℂ) * routeURealTwiceRootDividedTime b c h x *
            routeURealFourierPhase w x := by
          rw [MeasureTheory.integral_sub
            (integrable_mul_routeURealFourierPhase hh₁ w)
            (integrable_mul_routeURealFourierPhase (hh₂.const_mul c) w)]
      _ = _ := by
        rw [← MeasureTheory.integral_const_mul]
        congr 2
        funext x
        ring
  have hfactor' : (((w : ℂ) + (c : ℂ)) *
      routeURealFourier (routeURealTwiceRootDividedTime b c h) w) =
      routeURealFourier (routeURealRootDividedTime b c h) w := by
    exact_mod_cast hfactor
  rw [hsplit, ← hfactor']
  ring

/-- Removing symmetric real zeros has an explicit compactly supported time source whose Fourier
transform is the exact even quotient, expressed without division at either root. -/
theorem routeURealTwiceRootDividedTime_fourier_factor
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) (w : ℝ) :
    (((w ^ 2 - c ^ 2 : ℝ) : ℂ) *
      routeURealFourier (routeURealTwiceRootDividedTime b c h) w) =
        routeURealFourier h w := by
  have hfirst := routeURealRootDividedTime_fourier_factor hbd hh hsupp hc w
  have hsecond := routeURealTwiceRootDividedTime_fourier_factors
    hbd hh hsupp hc hnegc hc0 w
  have hfirst' : (((w : ℂ) - (c : ℂ)) *
      routeURealFourier (routeURealRootDividedTime b c h) w) =
      routeURealFourier h w := by
    exact_mod_cast hfirst
  have hsecond' : (((w : ℂ) + (c : ℂ)) *
      routeURealFourier (routeURealTwiceRootDividedTime b c h) w) =
      routeURealFourier (routeURealRootDividedTime b c h) w := by
    exact_mod_cast hsecond
  push_cast
  calc
    (((w : ℂ) ^ 2 - (c : ℂ) ^ 2) *
        routeURealFourier (routeURealTwiceRootDividedTime b c h) w) =
      ((w : ℂ) - (c : ℂ)) * (((w : ℂ) + (c : ℂ)) *
        routeURealFourier (routeURealTwiceRootDividedTime b c h) w) := by ring
    _ = ((w : ℂ) - (c : ℂ)) *
        routeURealFourier (routeURealRootDividedTime b c h) w := by rw [hsecond']
    _ = routeURealFourier h w := hfirst'

/-- **Same-aperture odd two-root division.**  Removing the symmetric real zeros `±c` and
multiplying by the spectral coordinate has an explicit compactly supported `L²` time source.
Its real-frequency Fourier transform is exactly `w F(w)/(w²-c²)`, expressed without division or
singular conventions. -/
theorem routeURealOddRootDividedTime_fourier_factor
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) (w : ℝ) :
    (((w ^ 2 - c ^ 2 : ℝ) : ℂ) *
      routeURealFourier (routeURealOddRootDividedTime b c h) w) =
        (w : ℂ) * routeURealFourier h w := by
  have hfirst := routeURealRootDividedTime_fourier_factor hbd hh hsupp hc w
  have hsecond := routeURealTwiceRootDividedTime_fourier_factors
    hbd hh hsupp hc hnegc hc0 w
  have hodd := routeURealOddRootDividedTime_fourier_eq_mul_twice
    hbd hh hsupp hc hnegc hc0 w
  have hfirst' : (((w : ℂ) - (c : ℂ)) *
      routeURealFourier (routeURealRootDividedTime b c h) w) =
      routeURealFourier h w := by
    exact_mod_cast hfirst
  have hsecond' : (((w : ℂ) + (c : ℂ)) *
      routeURealFourier (routeURealTwiceRootDividedTime b c h) w) =
      routeURealFourier (routeURealRootDividedTime b c h) w := by
    exact_mod_cast hsecond
  push_cast
  rw [hodd]
  calc
    (((w : ℂ) ^ 2 - (c : ℂ) ^ 2) *
        ((w : ℂ) * routeURealFourier (routeURealTwiceRootDividedTime b c h) w)) =
      (w : ℂ) * (((w : ℂ) - (c : ℂ)) * (((w : ℂ) + (c : ℂ)) *
        routeURealFourier (routeURealTwiceRootDividedTime b c h) w)) := by ring
    _ = (w : ℂ) * (((w : ℂ) - (c : ℂ)) *
        routeURealFourier (routeURealRootDividedTime b c h) w) := by rw [hsecond']
    _ = (w : ℂ) * routeURealFourier h w := by rw [hfirst']

/-- **Repeated-root closure of compact symmetric division.**  If the original transform has
`m+1` copies of the symmetric factor `w²-c²`, one compact two-root division has exactly `m`
copies everywhere, including at the two roots where cancellation alone says nothing.  Continuity
of both sides removes the apparent endpoint ambiguity. -/
theorem routeURealTwiceRootDividedTime_fourier_factor_pow
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) (m : ℕ) {G : ℝ → ℂ} (hG : Continuous G)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ (m + 1)) * G w) :
    ∀ w : ℝ, routeURealFourier (routeURealTwiceRootDividedTime b c h) w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * G w := by
  have hhq : Integrable (routeURealTwiceRootDividedTime b c h) :=
    integrable_routeURealTwiceRootDividedTime hbd hh hsupp hc hnegc hc0
  have hqcont : Continuous
      (routeURealFourier (routeURealTwiceRootDividedTime b c h)) :=
    continuous_routeURealFourier hhq
  have hrcont : Continuous (fun w : ℝ =>
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * G w) := by
    fun_prop
  have hdense : Dense (({c, -c} : Set ℝ)ᶜ) := by
    rw [show (({c, -c} : Set ℝ)ᶜ) = ({c}ᶜ ∩ ({-c}ᶜ)) by
      ext x
      simp]
    exact (dense_compl_singleton c).inter_of_isOpen_right
      (dense_compl_singleton (-c)) isOpen_compl_singleton
  have heq := Continuous.ext_on hdense hqcont hrcont (by
    intro w hw
    have hwc : w ≠ c := by
      intro h
      apply hw
      simp [h]
    have hwnegc : w ≠ -c := by
      intro h
      apply hw
      simp [h]
    have hAreal : w ^ 2 - c ^ 2 ≠ 0 := by
      intro hzero
      have hsquare : w ^ 2 = c ^ 2 := sub_eq_zero.mp hzero
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with h | h
      · exact hwc h
      · exact hwnegc h
    have hA : ((w ^ 2 - c ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hAreal
    apply (mul_left_cancel₀ hA)
    rw [routeURealTwiceRootDividedTime_fourier_factor
      hbd hh hsupp hc hnegc hc0 w, hfactor w]
    ring)
  exact fun w => congrFun heq w

end RHTower
