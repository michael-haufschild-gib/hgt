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

end

end RHTower
