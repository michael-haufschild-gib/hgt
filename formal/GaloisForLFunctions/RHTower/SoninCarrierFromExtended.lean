import GaloisForLFunctions.RHTower.BurnolLemmaSevenFive
import GaloisForLFunctions.RHTower.SoninDeBrangesCarrier
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# From the extended space `L_a` to the Sonine space `K_a`

Two dilation shifts turn any vector of `L_a` into a vector of `K_b` (`b < a`) with the *same*
Mellin jets on the open critical strip.

The point is that the shift `U_r v - λ v` multiplies both aperture constants by explicit scalars:
the physical one by `√r - λ` and the cosine one by `1/√r - λ`.  Choosing `λ = √r` kills the physical
constant; a second shift with `λ = 1/√r'` then kills the cosine constant, and by linearity the
physical one stays `0`.  The two Mellin multipliers `r^{s-1/2} - √r` and `r'^{s-1/2} - 1/√r'` have
their zeros on `Re s = 1` and `Re s = 0` respectively — **outside the open critical strip** — so no
order anywhere in the strip is disturbed.

## Main results

* `mem_centralSoninCarrier_of_ae_zero`
* `soninShift`, `extendedMellinContinuation_soninShift`
* `exists_soninCarrier_of_extended`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Membership in the Sonine space -/

theorem mem_physicalForbidden_orthogonal_of_indicator_ae_zero {s : Set ℝ} {hs : MeasurableSet s}
    {f : SoninL2} (h : s.indicator (⇑f) =ᵐ[volume] 0) : f ∈ (physicalForbidden s hs)ᗮ := by
  have h0 : indicatorCutoff s hs f = 0 := by
    refine Lp.ext ?_
    filter_upwards [indicatorCutoff_ae s hs f, h,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with t h1 h2 h3
    rw [h1, h2, h3]
  rw [indicatorCutoff_eq_physicalForbidden_starProjection] at h0
  exact (Submodule.starProjection_apply_eq_zero_iff (K := physicalForbidden s hs)).1 h0

theorem mem_centralFourierForbidden_orthogonal_of_indicator_ae_zero {a : ℝ} {f : SoninL2}
    (h : (centralInterval a).indicator (⇑(fourierUnitary f)) =ᵐ[volume] 0) :
    f ∈ (centralFourierForbidden a)ᗮ := by
  have hcut : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (fourierUnitary f) = 0 := by
    refine Lp.ext ?_
    filter_upwards [indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a)
      (fourierUnitary f), h,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with t h1 h2 h3
    rw [h1, h2, h3]
  have h0 : fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f = 0 := by
    have := congrArg fourierUnitary.symm hcut
    rw [fourierCutoff_apply]
    simpa using this
  rw [fourierCutoff_eq_fourierForbidden_starProjection] at h0
  exact (Submodule.starProjection_apply_eq_zero_iff
    (K := fourierForbidden (centralInterval a) (measurableSet_centralInterval a))).1 h0

/-- **Both aperture constants zero is exactly membership in the Sonine space.** -/
theorem mem_centralSoninCarrier_of_ae_zero {a : ℝ} {f : SoninL2}
    (hphys : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0)
    (hfour : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) x = 0) :
    f ∈ centralSoninCarrier a := by
  constructor
  · refine mem_physicalForbidden_orthogonal_of_indicator_ae_zero ?_
    filter_upwards [hphys] with t ht
    show (centralInterval a).indicator (⇑f) t = (0 : ℝ → ℂ) t
    by_cases hmem : t ∈ centralInterval a
    · rw [Set.indicator_of_mem hmem, ht hmem, Pi.zero_apply]
    · rw [Set.indicator_of_notMem hmem, Pi.zero_apply]
  · refine mem_centralFourierForbidden_orthogonal_of_indicator_ae_zero ?_
    filter_upwards [hfour] with t ht
    show (centralInterval a).indicator (⇑(fourierUnitary f)) t = (0 : ℝ → ℂ) t
    by_cases hmem : t ∈ centralInterval a
    · rw [Set.indicator_of_mem hmem, ht hmem, Pi.zero_apply]
    · rw [Set.indicator_of_notMem hmem, Pi.zero_apply]

/-! ## The explicit dilation shift -/

theorem le_mul_self_of_one_le {a r : ℝ} (ha : 0 < a) (hr1 : 1 ≤ r) : a ≤ a * r * r := by
  have h1 : a * 1 ≤ a * r := mul_le_mul_of_nonneg_left hr1 ha.le
  have har : 0 ≤ a * r := by nlinarith
  have h2 : (a * r) * 1 ≤ (a * r) * r := mul_le_mul_of_nonneg_left hr1 har
  simp only [mul_one] at h1 h2
  linarith

/-- The shift `U_r v - λ v`. -/
def soninShift (r : ℝ) (lam : ℂ) (v : SoninL2) : SoninL2 := rayDilate r v - lam • v

theorem soninShift_mem_evenSubspace {r : ℝ} (hr : 0 < r) (lam : ℂ) {v : SoninL2}
    (hev : v ∈ evenSubspace) : soninShift r lam v ∈ evenSubspace := by
  refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ hev)
  rw [rayDilate_of_pos hr]
  exact dilation_mem_evenSubspace hr hev

theorem soninShift_ae_phys {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (lam : ℂ)
    {v : SoninL2} {d : ℂ}
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval (a / r) →
      ((soninShift r lam v : SoninL2) : ℝ → ℂ) t = ((Real.sqrt r : ℝ) : ℂ) * d - lam * d := by
  have hdil : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval (a / r) →
      ((rayDilate r v : SoninL2) : ℝ → ℂ) t = ((Real.sqrt r : ℝ) : ℂ) * d := by
    rw [rayDilate_of_pos hr]
    exact ae_const_dilation hr hd
  have hle : a / r ≤ a := by
    rw [div_le_iff₀ hr]
    nlinarith
  have hv : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval (a / r) → (v : ℝ → ℂ) t = d :=
    ae_const_mono hle hd
  filter_upwards [hdil, hv, Lp.coeFn_sub (rayDilate r v) (lam • v), Lp.coeFn_smul lam v]
    with t h1 h2 h3 h4 hmem
  rw [soninShift, h3, Pi.sub_apply, h4, Pi.smul_apply, smul_eq_mul, h1 hmem, h2 hmem]

theorem soninShift_ae_fourier {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (lam : ℂ)
    {v : SoninL2} {c : ℂ}
    (hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval (a / r) →
      ((fourierUnitary (soninShift r lam v) : SoninL2) : ℝ → ℂ) x
        = ((Real.sqrt r⁻¹ : ℝ) : ℂ) * c - lam * c := by
  have hinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr
  have hdil0 : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval (a / r⁻¹) →
      ((fourierUnitary (rayDilate r v) : SoninL2) : ℝ → ℂ) x
        = ((Real.sqrt r⁻¹ : ℝ) : ℂ) * c := by
    rw [rayDilate_of_pos hr, fourierUnitary_dilation r hr v]
    exact ae_const_dilation hinv hc
  have hmul : a / r⁻¹ = a * r := by field_simp
  rw [hmul] at hdil0
  have hle1 : a / r ≤ a * r := by
    rw [div_le_iff₀ hr]
    exact le_mul_self_of_one_le ha hr1
  have hdil : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval (a / r) →
      ((fourierUnitary (rayDilate r v) : SoninL2) : ℝ → ℂ) x
        = ((Real.sqrt r⁻¹ : ℝ) : ℂ) * c := ae_const_mono hle1 hdil0
  have hle : a / r ≤ a := by
    rw [div_le_iff₀ hr]
    nlinarith
  have hv : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval (a / r) →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c := ae_const_mono hle hc
  have hsm : fourierUnitary (soninShift r lam v)
      = fourierUnitary (rayDilate r v) - lam • fourierUnitary v := by
    rw [soninShift, map_sub, map_smul]
  filter_upwards [hdil, hv,
    (by rw [hsm]; exact Lp.coeFn_sub (fourierUnitary (rayDilate r v)) (lam • fourierUnitary v) :
      ((fourierUnitary (soninShift r lam v) : SoninL2) : ℝ → ℂ)
        =ᵐ[volume] (fourierUnitary (rayDilate r v) : ℝ → ℂ)
          - ((lam • fourierUnitary v : SoninL2) : ℝ → ℂ)),
    Lp.coeFn_smul lam (fourierUnitary v)] with x h1 h2 h3 h4 hmem
  rw [h3, Pi.sub_apply, h4, Pi.smul_apply, smul_eq_mul, h1 hmem, h2 hmem]

theorem soninShift_mem_extended {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (lam : ℂ)
    {v : SoninL2} (hmem : v ∈ centralSoninExtendedCarrier a) :
    soninShift r lam v ∈ centralSoninExtendedCarrier (a / r) := by
  have hle : a / r ≤ a := by
    rw [div_le_iff₀ hr]
    nlinarith
  have hdil : rayDilate r v ∈ centralSoninExtendedCarrier (a / r) := by
    rw [rayDilate_of_pos hr]
    refine dilation_mem_centralSoninExtendedCarrier hr hmem (le_refl _) ?_
    rw [div_le_iff₀ hr]
    exact le_mul_self_of_one_le ha hr1
  exact Submodule.sub_mem _ hdil
    (Submodule.smul_mem _ _ (centralSoninExtendedCarrier_antitone hle hmem))

/-- **The Mellin transform of the shift.** -/
theorem extendedMellinContinuation_soninShift {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r)
    (lam : ℂ) {v : SoninL2} {c d : ℂ} (hev : v ∈ evenSubspace)
    (hmem : v ∈ centralSoninExtendedCarrier a)
    (hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 1) :
    extendedMellinContinuation (a / r) (((Real.sqrt r⁻¹ : ℝ) : ℂ) * c - lam * c)
        (((Real.sqrt r : ℝ) : ℂ) * d - lam * d) (soninShift r lam v) s
      = (((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam) * extendedMellinContinuation a c d v s := by
  have har : 0 < a / r := div_pos ha hr
  have hVev : soninShift r lam v ∈ evenSubspace := soninShift_mem_evenSubspace hr lam hev
  have hphys := soninShift_ae_phys ha hr hr1 lam hd
  have hfour := soninShift_ae_fourier ha hr hr1 lam hc
  have hdilphys : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval (a / r) →
      ((rayDilate r v : SoninL2) : ℝ → ℂ) t = ((Real.sqrt r : ℝ) : ℂ) * d := by
    rw [rayDilate_of_pos hr]
    exact ae_const_dilation hr hd
  have hVint : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (rayDilate r v : ℝ → ℂ) t)
      (Ioi (0 : ℝ)) volume := integrableOn_cpow_mul_Ioi_zero har hdilphys hs1 hs2
  have hvint : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (v : ℝ → ℂ) t)
      (Ioi (0 : ℝ)) volume := integrableOn_cpow_mul_Ioi_zero ha hd hs1 hs2
  have hsub : soninMellinIntegral (soninShift r lam v) s
      = soninMellinIntegral (rayDilate r v) s - lam * soninMellinIntegral v s := by
    rw [soninMellinIntegral, soninMellinIntegral, soninMellinIntegral,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub hVint (hvint.const_mul lam)]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [Lp.coeFn_sub (rayDilate r v) (lam • v), Lp.coeFn_smul lam v] with t h1 h2 _
    rw [soninShift, h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul]
    ring
  rw [extendedMellinContinuation_eq_soninMellinIntegral har hVev hfour hphys hs1 hs2, hsub,
    soninMellinIntegral_rayDilate hr v s,
    ← extendedMellinContinuation_eq_soninMellinIntegral ha hev hc hd hs1 hs2]
  ring

/-! ## From `L_a` to `K_b` -/

theorem cpow_ofReal_ne_of_re_ne {r : ℝ} (hr1 : 1 < r) {s : ℂ} {t : ℝ} (hst : s.re ≠ t) :
    ((r : ℝ) : ℂ) ^ s ≠ ((r : ℝ) : ℂ) ^ ((t : ℝ) : ℂ) := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr1
  intro h
  have hnorm : ‖((r : ℝ) : ℂ) ^ s‖ = ‖((r : ℝ) : ℂ) ^ ((t : ℝ) : ℂ)‖ := by rw [h]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr0, Complex.norm_cpow_eq_rpow_re_of_pos hr0] at hnorm
  simp only [Complex.ofReal_re] at hnorm
  have hs : StrictMono fun z : ℝ => r ^ z := fun p q hpq =>
    (Real.rpow_lt_rpow_left_iff hr1).mpr hpq
  exact hst (hs.injective hnorm)

theorem ofReal_sqrt_eq_cpow {r : ℝ} (hr : 0 < r) :
    ((Real.sqrt r : ℝ) : ℂ) = ((r : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, ← Complex.ofReal_cpow hr.le]

theorem ofReal_sqrt_inv_eq_cpow {r : ℝ} (hr : 0 < r) :
    ((Real.sqrt r⁻¹ : ℝ) : ℂ) = ((r : ℝ) : ℂ) ^ (((-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  have hinv : Real.sqrt r⁻¹ = r ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one r, ← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [hinv, ← Complex.ofReal_cpow hr.le]

/-- **From `L_a` to `K_b`.**  Two dilation shifts kill both aperture constants without moving any
Mellin order inside the open critical strip. -/
theorem exists_soninCarrier_of_extended {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {v : SoninL2} {c d : ℂ} (hev : v ∈ evenSubspace)
    (hmem : v ∈ centralSoninExtendedCarrier a)
    (hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d) :
    ∃ V : SoninL2, V ∈ evenSubspace ∧ V ∈ centralSoninCarrier b ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval b →
        ((fourierUnitary V : SoninL2) : ℝ → ℂ) x = 0) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (V : ℝ → ℂ) t = 0) ∧
      ∀ w : ℂ, 0 < w.re → w.re < 1 →
        meromorphicOrderAt (extendedMellinContinuation b 0 0 V) w
          = meromorphicOrderAt (extendedMellinContinuation a c d v) w := by
  classical
  set q : ℝ := a / b with hq
  have hq1 : 1 < q := by
    rw [hq, lt_div_iff₀ hb]
    linarith
  set r : ℝ := Real.sqrt q with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.2 (lt_trans zero_lt_one hq1)
  have hr1 : 1 < r := by
    rw [hrdef, show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hq1
  have hq0 : (0 : ℝ) ≤ q := le_of_lt (lt_trans zero_lt_one hq1)
  have hrr : r * r = q := by
    rw [hrdef]
    exact Real.mul_self_sqrt hq0
  have hab2 : a / r / r = b := by
    rw [div_div, hrr, hq]
    field_simp
  -- first shift kills the physical constant
  set lam₁ : ℂ := ((Real.sqrt r : ℝ) : ℂ) with hlam₁
  set V₁ : SoninL2 := soninShift r lam₁ v with hV₁
  set c₁ : ℂ := ((Real.sqrt r⁻¹ : ℝ) : ℂ) * c - lam₁ * c with hc₁def
  set d₁ : ℂ := ((Real.sqrt r : ℝ) : ℂ) * d - lam₁ * d with hd₁def
  have hd₁zero : d₁ = 0 := by rw [hd₁def, hlam₁]; ring
  have hV₁ev : V₁ ∈ evenSubspace := soninShift_mem_evenSubspace hr0 lam₁ hev
  have hV₁mem : V₁ ∈ centralSoninExtendedCarrier (a / r) :=
    soninShift_mem_extended ha hr0 hr1.le lam₁ hmem
  have hV₁phys : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval (a / r) →
      (V₁ : ℝ → ℂ) t = d₁ := soninShift_ae_phys ha hr0 hr1.le lam₁ hd
  have hV₁four : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval (a / r) →
      ((fourierUnitary V₁ : SoninL2) : ℝ → ℂ) x = c₁ :=
    soninShift_ae_fourier ha hr0 hr1.le lam₁ hc
  have har : 0 < a / r := div_pos ha hr0
  -- second shift kills the cosine constant
  set lam₂ : ℂ := ((Real.sqrt r⁻¹ : ℝ) : ℂ) with hlam₂
  set V : SoninL2 := soninShift r lam₂ V₁ with hVdef
  set c₂ : ℂ := ((Real.sqrt r⁻¹ : ℝ) : ℂ) * c₁ - lam₂ * c₁ with hc₂def
  set d₂ : ℂ := ((Real.sqrt r : ℝ) : ℂ) * d₁ - lam₂ * d₁ with hd₂def
  have hc₂zero : c₂ = 0 := by rw [hc₂def, hlam₂]; ring
  have hd₂zero : d₂ = 0 := by rw [hd₂def, hd₁zero]; ring
  have hVev : V ∈ evenSubspace := soninShift_mem_evenSubspace hr0 lam₂ hV₁ev
  have hVmem : V ∈ centralSoninExtendedCarrier (a / r / r) :=
    soninShift_mem_extended har hr0 hr1.le lam₂ hV₁mem
  have hVphys : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval (a / r / r) →
      (V : ℝ → ℂ) t = d₂ := soninShift_ae_phys har hr0 hr1.le lam₂ hV₁phys
  have hVfour : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval (a / r / r) →
      ((fourierUnitary V : SoninL2) : ℝ → ℂ) x = c₂ :=
    soninShift_ae_fourier har hr0 hr1.le lam₂ hV₁four
  rw [hab2] at hVmem hVphys hVfour
  rw [hc₂zero] at hVfour
  rw [hd₂zero] at hVphys
  -- the Mellin identity on the convergence strip
  have hmul : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      extendedMellinContinuation b 0 0 V s
        = (((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₂) * ((((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁)
          * extendedMellinContinuation a c d v s) := by
    intro s hs1 hs2
    have h2 := extendedMellinContinuation_soninShift har hr0 hr1.le lam₂ hV₁ev hV₁mem
      hV₁four hV₁phys hs1 hs2
    have h1 := extendedMellinContinuation_soninShift ha hr0 hr1.le lam₁ hev hmem hc hd hs1 hs2
    rw [← hc₂def, ← hd₂def, hab2, hc₂zero, hd₂zero] at h2
    rw [h2, h1]
  refine ⟨V, hVev, mem_centralSoninCarrier_of_ae_zero hVphys hVfour, hVfour, hVphys, ?_⟩
  -- the two multipliers have no zeros in the open strip
  have hmult1 : ∀ s : ℂ, s.re < 1 → ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁ ≠ 0 := by
    intro s hs hzero
    have heq : ((r : ℝ) : ℂ) ^ (s - 1 / 2) = ((r : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [← ofReal_sqrt_eq_cpow hr0, ← hlam₁]
      linear_combination hzero
    refine cpow_ofReal_ne_of_re_ne hr1 (t := (1 / 2 : ℝ)) ?_ heq
    have hre : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by
      rw [Complex.sub_re]
      norm_num
    rw [hre]
    intro hcon
    linarith
  have hmult2 : ∀ s : ℂ, 0 < s.re → ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₂ ≠ 0 := by
    intro s hs hzero
    have heq : ((r : ℝ) : ℂ) ^ (s - 1 / 2) = ((r : ℝ) : ℂ) ^ (((-(1 / 2) : ℝ) : ℝ) : ℂ) := by
      rw [← ofReal_sqrt_inv_eq_cpow hr0, ← hlam₂]
      linear_combination hzero
    refine cpow_ofReal_ne_of_re_ne hr1 (t := (-(1 / 2) : ℝ)) ?_ heq
    have hre : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by
      rw [Complex.sub_re]
      norm_num
    rw [hre]
    intro hcon
    linarith
  -- extend the identity to the whole strip and compare orders
  have hmultdiff : Differentiable ℂ (fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2)) := by
    have hrc : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr0
    have h : (fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2))
        = fun s : ℂ => Complex.exp (Complex.log ((r : ℝ) : ℂ) * (s - 1 / 2)) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero hrc]
    rw [h]
    exact Complex.differentiable_exp.comp ((differentiable_const _).mul
      (differentiable_id.sub (differentiable_const _)))
  have hA1 : AnalyticOnNhd ℂ (extendedMellinContinuation b 0 0 V)
      {y : ℂ | 0 < y.re ∧ y.re < 1} := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h] at hy; norm_num at hy
    have hy1 : y ≠ 1 := by intro h; rw [h] at hy; norm_num at hy
    exact analyticAt_extendedMellinContinuation_of_ne hb hVev hVfour hVphys hy0 hy1
  have hA2 : AnalyticOnNhd ℂ
      (fun s : ℂ => (((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₂) * ((((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁)
        * extendedMellinContinuation a c d v s)) {y : ℂ | 0 < y.re ∧ y.re < 1} := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h] at hy; norm_num at hy
    have hy1 : y ≠ 1 := by intro h; rw [h] at hy; norm_num at hy
    exact ((hmultdiff.analyticAt y).sub analyticAt_const).mul
      (((hmultdiff.analyticAt y).sub analyticAt_const).mul
        (analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hy0 hy1))
  have hz₀ : ((3 / 4 : ℝ) : ℂ) ∈ {y : ℂ | 0 < y.re ∧ y.re < 1} := by
    constructor <;> simp <;> norm_num
  have hev₀ : extendedMellinContinuation b 0 0 V =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)]
      fun s : ℂ => (((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₂) * ((((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁)
        * extendedMellinContinuation a c d v s) := by
    have hopen : IsOpen {y : ℂ | 1 / 2 < y.re ∧ y.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmem₀ : ((3 / 4 : ℝ) : ℂ) ∈ {y : ℂ | 1 / 2 < y.re ∧ y.re < 1} := by
      constructor <;> simp <;> norm_num
    filter_upwards [hopen.mem_nhds hmem₀] with y hy
    exact hmul y hy.1 hy.2
  have hall : ∀ y : ℂ, 0 < y.re → y.re < 1 →
      extendedMellinContinuation b 0 0 V y
        = (((r : ℝ) : ℂ) ^ (y - 1 / 2) - lam₂) * ((((r : ℝ) : ℂ) ^ (y - 1 / 2) - lam₁)
          * extendedMellinContinuation a c d v y) := fun y hy0 hy1 =>
    hA1.eqOn_of_preconnected_of_eventuallyEq hA2 isPreconnected_criticalStrip hz₀ hev₀ ⟨hy0, hy1⟩
  intro w hw0 hw1
  have hloc : extendedMellinContinuation b 0 0 V
      =ᶠ[𝓝[≠] w] ((fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₂)
        * ((fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁)
          * extendedMellinContinuation a c d v)) := by
    refine EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds
    filter_upwards [isOpen_criticalOpenStrip.mem_nhds
      (⟨hw0, hw1⟩ : w ∈ {u : ℂ | 0 < u.re ∧ u.re < 1})] with u hu
    rw [Pi.mul_apply, Pi.mul_apply]
    exact hall u hu.1 hu.2
  have hmero₂ : MeromorphicAt (fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₂) w :=
    ((hmultdiff.analyticAt w).sub analyticAt_const).meromorphicAt
  have hmero₁ : MeromorphicAt (fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁) w :=
    ((hmultdiff.analyticAt w).sub analyticAt_const).meromorphicAt
  have hmeroM : MeromorphicAt (extendedMellinContinuation a c d v) w :=
    meromorphicAt_extendedMellinContinuation ha hev hc hd w
  rw [meromorphicOrderAt_congr hloc,
    meromorphicOrderAt_mul (f := fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₂)
      (g := (fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁) * extendedMellinContinuation a c d v)
      hmero₂ (hmero₁.mul hmeroM),
    meromorphicOrderAt_mul (f := fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁)
      (g := extendedMellinContinuation a c d v) hmero₁ hmeroM]
  have hord2 : meromorphicOrderAt (fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₂) w = 0 := by
    have hana : AnalyticAt ℂ (fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₂) w :=
      (hmultdiff.analyticAt w).sub analyticAt_const
    rw [hana.meromorphicOrderAt_eq, hana.analyticOrderAt_eq_zero.2 (hmult2 w hw0)]
    simp
  have hord1 : meromorphicOrderAt (fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁) w = 0 := by
    have hana : AnalyticAt ℂ (fun s : ℂ => ((r : ℝ) : ℂ) ^ (s - 1 / 2) - lam₁) w :=
      (hmultdiff.analyticAt w).sub analyticAt_const
    rw [hana.meromorphicOrderAt_eq, hana.analyticOrderAt_eq_zero.2 (hmult1 w hw1)]
    simp
  rw [hord1, hord2, zero_add, zero_add]

end

end RHTower
