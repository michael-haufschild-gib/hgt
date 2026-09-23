import GaloisForLFunctions.RHTower.WeilPrimeFreeTest

/-!
# The prime-free restricted Weil family crosses zero

On the pole-vanishing low-frequency test of `WeilPrimeFreeTest` the quadratic form of the
prime-free family is the archimedean multiplier integral
`∫ 2·γ(2πξ)·|m(ξ)|²·L²·|φ̂(Lξ)|² dξ`, with `γ` the archimedean phase rate.  Near the origin `γ` is
negative and the integrand is bounded above by `γ(0)·(c/4)·L²ξ⁴` on `|ξ| ≤ ε₀/L`; away from the
origin `γ(t) ≤ 35 + |t|` and the transform decays like `|Lξ|^{-3}`, so the positive part is
`O(L^{-4})` while the negative part is of exact order `L^{-3}`.  Hence the prime-free ground
energy is negative at every sufficiently large aperture.  It is positive at small apertures, where
the prime-free operator is the literal one, so the generic family theory produces an aperture with
vanishing ground energy and a nonzero kernel element: the archimedean-plus-polar restricted Weil
operator, with every prime removed, has a spectral zero crossing.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform

noncomputable section

namespace RHTower.WeilDeletion

/-! ## The Fourier profile of the test -/

theorem norm_sq_fourier_primeFreeTest (L : ℝ) (hL : 1 ≤ L) (ξ : ℝ) :
    ‖𝓕 ((primeFreeTest L hL).toSchwartz : ℝ → ℂ) ξ‖ ^ (2 : ℕ) =
      mSym ξ ^ (2 : ℕ) * (L ^ (2 : ℕ) * ‖𝓕 phiTwoC (L * ξ)‖ ^ (2 : ℕ)) := by
  have hLpos : 0 < L := by linarith
  unfold primeFreeTest
  rw [fourier_polarTranslate, fourier_wideBumpSource, polarMultiplierSpectral_one_ofReal,
    norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hLpos]
  rw [mul_pow, mul_pow, sq_abs]

/-- The test's Fourier profile. -/
def testProfile (L : ℝ) (ξ : ℝ) : ℝ := mSym ξ ^ (2 : ℕ) * (L ^ (2 : ℕ) * ‖𝓕 phiTwoC (L * ξ)‖ ^ (2 : ℕ))

theorem testProfile_nonneg (L ξ : ℝ) : 0 ≤ testProfile L ξ := by
  unfold testProfile
  positivity

/-- Constant of the spectral symbol lower bound. -/
def cM : ℝ := 64 * (Real.cosh (1 / 2) - 1) ^ (2 : ℕ)

theorem cM_pos : 0 < cM := by
  unfold cM
  have : 1 < Real.cosh (1 / 2) := Real.one_lt_cosh.mpr (by norm_num)
  have h : 0 < Real.cosh (1 / 2) - 1 := by linarith
  positivity

/-- Upper constant of the spectral symbol. -/
def mM : ℝ := 2 * (1 + Real.cosh (1 / 2))

theorem mSym_sq_le (ξ : ℝ) : mSym ξ ^ (2 : ℕ) ≤ mM ^ (2 : ℕ) := by
  have h := abs_mSym_le ξ
  have h0 : 0 ≤ |mSym ξ| := abs_nonneg _
  calc mSym ξ ^ (2 : ℕ) = |mSym ξ| ^ (2 : ℕ) := (sq_abs _).symm
    _ ≤ mM ^ (2 : ℕ) := pow_le_pow_left₀ h0 h 2

theorem testProfile_ge {L ξ : ℝ} (hL : 0 < L) (hξ : |ξ| ≤ 1 / 2) (hLξ : |L * ξ| ≤ epsTwo) :
    cM / 4 * L ^ (2 : ℕ) * ξ ^ (4 : ℕ) ≤ testProfile L ξ := by
  unfold testProfile
  have h1 : cM * ξ ^ (4 : ℕ) ≤ mSym ξ ^ (2 : ℕ) := by
    unfold cM
    exact mSym_sq_ge hξ
  have h2 := norm_fourier_phiTwoC_ge hLξ
  have h2' : (1 / 2 : ℝ) ^ (2 : ℕ) ≤ ‖𝓕 phiTwoC (L * ξ)‖ ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 2
  have hL2 : 0 ≤ L ^ (2 : ℕ) := sq_nonneg L
  have hcM : 0 ≤ cM * ξ ^ (4 : ℕ) := by have := cM_pos; positivity
  calc cM / 4 * L ^ (2 : ℕ) * ξ ^ (4 : ℕ) = (cM * ξ ^ (4 : ℕ)) * (L ^ (2 : ℕ) * (1 / 2) ^ (2 : ℕ)) := by ring
    _ ≤ mSym ξ ^ (2 : ℕ) * (L ^ (2 : ℕ) * ‖𝓕 phiTwoC (L * ξ)‖ ^ (2 : ℕ)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2' hL2) (by positivity) (by positivity)

theorem testProfile_le {L ξ : ℝ} (hL : 0 < L) (hξ : ξ ≠ 0) :
    testProfile L ξ ≤ mM ^ (2 : ℕ) * kappaTwo ^ (2 : ℕ) / L ^ (4 : ℕ) / |ξ| ^ (6 : ℕ) := by
  unfold testProfile
  have hLξ : L * ξ ≠ 0 := mul_ne_zero hL.ne' hξ
  have h2 := norm_fourier_phiTwoC_le hLξ
  have h2' : ‖𝓕 phiTwoC (L * ξ)‖ ^ (2 : ℕ) ≤ (kappaTwo / |L * ξ| ^ (3 : ℕ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hm := mSym_sq_le ξ
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  have habs : |L * ξ| = L * |ξ| := by rw [abs_mul, abs_of_pos hL]
  rw [habs] at h2'
  calc mSym ξ ^ (2 : ℕ) * (L ^ (2 : ℕ) * ‖𝓕 phiTwoC (L * ξ)‖ ^ (2 : ℕ))
      ≤ mM ^ (2 : ℕ) * (L ^ (2 : ℕ) * (kappaTwo / (L * |ξ|) ^ (3 : ℕ)) ^ (2 : ℕ)) :=
        mul_le_mul hm (mul_le_mul_of_nonneg_left h2' (sq_nonneg L)) (by positivity) (by positivity)
    _ = mM ^ (2 : ℕ) * kappaTwo ^ (2 : ℕ) / L ^ (4 : ℕ) / |ξ| ^ (6 : ℕ) := by
        field_simp

/-! ## The archimedean part of the test as a Fourier integral -/

theorem archPart_primeFreeTest_eq (L : ℝ) (hL : 1 ≤ L) :
    archPart _ (primeFreeTest L hL).toCCMFormVector =
      ∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * testProfile L ξ := by
  unfold archPart
  refine integral_congr_ae ?_
  filter_upwards [(primeFreeTest L hL).toCCMFormVector_fourier_coeFn] with ξ hξ
  rw [hξ, norm_sq_fourier_primeFreeTest]
  rfl

theorem integrable_archIntegrand (L : ℝ) (hL : 1 ≤ L) :
    Integrable (fun ξ : ℝ => 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * testProfile L ξ) := by
  have h := integrable_two_gammaHardyPhaseRate_mul_norm_sq (primeFreeTest L hL).toCCMFormVector.1
  refine h.congr ?_
  filter_upwards [(primeFreeTest L hL).toCCMFormVector_fourier_coeFn] with ξ hξ
  rw [hξ, norm_sq_fourier_primeFreeTest]
  rfl

/-! ## The majorant -/

/-- The negative constant of the inner estimate: the integrand is at most
`γ(0)·(cM/4)·L²·ξ⁴` on `|ξ| ≤ ε₀/L`. -/
def innerConst : ℝ := (-gammaHardyPhaseRate 0) * cM * epsTwo ^ (5 : ℕ) / 10

theorem innerConst_pos : 0 < innerConst := by
  unfold innerConst
  have h1 := gammaHardyPhaseRate_zero_neg
  have h2 := cM_pos
  have h3 := epsTwo_pos
  have : 0 < -gammaHardyPhaseRate 0 := by linarith
  positivity

/-- Outer constant for a given negativity radius `ξ₀`. -/
def outerConst (ξ₀ : ℝ) : ℝ :=
  2 * mM ^ (2 : ℕ) * kappaTwo ^ (2 : ℕ) * (35 / ξ₀ + 2 * Real.pi) * (1 + 1 / ξ₀ ^ (2 : ℕ)) / ξ₀ ^ (3 : ℕ)

theorem outerConst_nonneg {ξ₀ : ℝ} (hξ₀ : 0 < ξ₀) : 0 ≤ outerConst ξ₀ := by
  unfold outerConst
  have := kappaTwo_pos
  positivity

/-- Outer pointwise bound: for `|ξ| ≥ ξ₀ > 0`, `(35 + 2π|ξ|)/|ξ|⁶ ≤ (35/ξ₀ + 2π)(1 + 1/ξ₀²)/ξ₀³ · (1 + ξ²)⁻¹`. -/
theorem outer_pointwise {ξ₀ ξ : ℝ} (hξ₀ : 0 < ξ₀) (hξ : ξ₀ ≤ |ξ|) :
    (35 + 2 * Real.pi * |ξ|) / |ξ| ^ (6 : ℕ) ≤
      (35 / ξ₀ + 2 * Real.pi) * (1 + 1 / ξ₀ ^ (2 : ℕ)) / ξ₀ ^ (3 : ℕ) * (1 + ξ ^ (2 : ℕ))⁻¹ := by
  have hξpos : 0 < |ξ| := lt_of_lt_of_le hξ₀ hξ
  have h1 : 35 + 2 * Real.pi * |ξ| ≤ (35 / ξ₀ + 2 * Real.pi) * |ξ| := by
    have : 35 ≤ 35 / ξ₀ * |ξ| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hξ₀]
      nlinarith
    nlinarith
  have h2 : ξ₀ ^ (3 : ℕ) * ξ ^ (2 : ℕ) ≤ |ξ| ^ (5 : ℕ) := by
    have hsq : ξ ^ (2 : ℕ) = |ξ| ^ (2 : ℕ) := (sq_abs ξ).symm
    rw [hsq]
    have h3 : ξ₀ ^ (3 : ℕ) ≤ |ξ| ^ (3 : ℕ) := pow_le_pow_left₀ hξ₀.le hξ 3
    calc ξ₀ ^ (3 : ℕ) * |ξ| ^ (2 : ℕ) ≤ |ξ| ^ (3 : ℕ) * |ξ| ^ (2 : ℕ) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = |ξ| ^ (5 : ℕ) := by ring
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hξ
    linarith
  have h3 : (1 : ℝ) / ξ ^ (2 : ℕ) ≤ (1 + 1 / ξ₀ ^ (2 : ℕ)) * (1 + ξ ^ (2 : ℕ))⁻¹ := by
    have hξ2 : 0 < ξ ^ (2 : ℕ) := by positivity
    have hξ₀2 : ξ₀ ^ (2 : ℕ) ≤ ξ ^ (2 : ℕ) := by
      rw [← sq_abs ξ]
      exact pow_le_pow_left₀ hξ₀.le hξ 2
    have hpos : 0 < 1 + ξ ^ (2 : ℕ) := by positivity
    rw [← div_eq_mul_inv, div_le_div_iff₀ hξ2 hpos, one_mul]
    have hξ₀pos2 : 0 < ξ₀ ^ (2 : ℕ) := by positivity
    have hq : 1 ≤ ξ ^ (2 : ℕ) / ξ₀ ^ (2 : ℕ) := by rw [le_div_iff₀ hξ₀pos2]; linarith
    have hexp : (1 + 1 / ξ₀ ^ (2 : ℕ)) * ξ ^ (2 : ℕ) = ξ ^ (2 : ℕ) + ξ ^ (2 : ℕ) / ξ₀ ^ (2 : ℕ) := by ring
    rw [hexp]
    linarith
  have hA : 0 ≤ (35 / ξ₀ + 2 * Real.pi) := by positivity
  calc (35 + 2 * Real.pi * |ξ|) / |ξ| ^ (6 : ℕ) ≤ ((35 / ξ₀ + 2 * Real.pi) * |ξ|) / |ξ| ^ (6 : ℕ) := by
        gcongr
    _ = (35 / ξ₀ + 2 * Real.pi) / |ξ| ^ (5 : ℕ) := by
        rw [pow_succ, mul_div_mul_right _ _ hξpos.ne']
    _ ≤ (35 / ξ₀ + 2 * Real.pi) / (ξ₀ ^ (3 : ℕ) * ξ ^ (2 : ℕ)) :=
        div_le_div_of_nonneg_left hA (by positivity) h2
    _ = (35 / ξ₀ + 2 * Real.pi) / ξ₀ ^ (3 : ℕ) * (1 / ξ ^ (2 : ℕ)) := by
        rw [div_mul_div_comm, mul_one]
    _ ≤ (35 / ξ₀ + 2 * Real.pi) / ξ₀ ^ (3 : ℕ) * ((1 + 1 / ξ₀ ^ (2 : ℕ)) * (1 + ξ ^ (2 : ℕ))⁻¹) := by
        gcongr
    _ = (35 / ξ₀ + 2 * Real.pi) * (1 + 1 / ξ₀ ^ (2 : ℕ)) / ξ₀ ^ (3 : ℕ) * (1 + ξ ^ (2 : ℕ))⁻¹ := by ring

/-- The two-piece majorant of the archimedean integrand. -/
def majorant (L ξ₀ : ℝ) (ξ : ℝ) : ℝ :=
  (Icc (-(epsTwo / L)) (epsTwo / L)).indicator
      (fun ξ => gammaHardyPhaseRate 0 * (cM / 4 * L ^ (2 : ℕ) * ξ ^ (4 : ℕ))) ξ +
    outerConst ξ₀ / L ^ (4 : ℕ) * (1 + ξ ^ (2 : ℕ))⁻¹

theorem integrable_majorant (L ξ₀ : ℝ) : Integrable (majorant L ξ₀) := by
  unfold majorant
  refine Integrable.add ?_ ?_
  · refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
    exact Continuous.integrableOn_Icc (by fun_prop)
  · exact integrable_inv_one_add_sq.const_mul _

theorem integral_majorant (L ξ₀ : ℝ) (hL : 0 < L) :
    ∫ ξ, majorant L ξ₀ ξ =
      gammaHardyPhaseRate 0 * (cM / 4 * L ^ (2 : ℕ) * (2 * (epsTwo / L) ^ (5 : ℕ) / 5)) +
        outerConst ξ₀ / L ^ (4 : ℕ) * ∫ ξ : ℝ, (1 + ξ ^ (2 : ℕ))⁻¹ := by
  unfold majorant
  have hi : Integrable ((Icc (-(epsTwo / L)) (epsTwo / L)).indicator
      (fun ξ : ℝ => gammaHardyPhaseRate 0 * (cM / 4 * L ^ (2 : ℕ) * ξ ^ (4 : ℕ)))) := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
    exact Continuous.integrableOn_Icc (by fun_prop)
  rw [integral_add hi (integrable_inv_one_add_sq.const_mul _), integral_indicator measurableSet_Icc]
  congr 1
  · rw [integral_const_mul]
    congr 1
    have he : 0 ≤ epsTwo / L := by have := epsTwo_pos; positivity
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    ring
  · exact integral_const_mul _ _

/-! ## The pointwise domination -/

theorem archIntegrand_le_majorant {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀π : t₀ ≤ Real.pi)
    (hneg : ∀ t : ℝ, |t| ≤ t₀ → gammaHardyPhaseRate t ≤ gammaHardyPhaseRate 0 / 2)
    {L : ℝ} (hL : 1 ≤ L) (hLbig : epsTwo * (2 * Real.pi) / t₀ ≤ L) (hLtwo : 2 * epsTwo ≤ L) (ξ : ℝ) :
    2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * testProfile L ξ ≤ majorant L (t₀ / (2 * Real.pi)) ξ := by
  set ξ₀ : ℝ := t₀ / (2 * Real.pi) with hξ₀
  have hξ₀pos : 0 < ξ₀ := by rw [hξ₀]; positivity
  have hLpos : 0 < L := by linarith
  have hε := epsTwo_pos
  have hεL : epsTwo / L ≤ ξ₀ := by
    rw [hξ₀, div_le_div_iff₀ hLpos (by positivity)]
    have := (div_le_iff₀ ht₀).mp hLbig
    linarith
  have hεhalf : epsTwo / L ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hLpos (by norm_num)]
    linarith
  have hξ₀half : ξ₀ ≤ 1 / 2 := by
    rw [hξ₀, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hg0 := gammaHardyPhaseRate_zero_neg
  have hF := testProfile_nonneg L ξ
  have houter_nonneg : 0 ≤ outerConst ξ₀ / L ^ (4 : ℕ) * (1 + ξ ^ (2 : ℕ))⁻¹ := by
    have := outerConst_nonneg hξ₀pos
    positivity
  unfold majorant
  by_cases hin : |ξ| ≤ epsTwo / L
  · -- inner region
    have hmem : ξ ∈ Icc (-(epsTwo / L)) (epsTwo / L) := by
      rw [mem_Icc]; exact abs_le.mp hin
    rw [indicator_of_mem hmem]
    have hξt : |2 * Real.pi * ξ| ≤ t₀ := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have h1 : |ξ| ≤ ξ₀ := hin.trans hεL
      rw [hξ₀, le_div_iff₀ (by positivity)] at h1
      linarith
    have hγ : 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) ≤ gammaHardyPhaseRate 0 := by
      have h := hneg (2 * Real.pi * ξ) hξt
      linarith
    have hLξ : |L * ξ| ≤ epsTwo := by
      rw [abs_mul, abs_of_pos hLpos]
      have := (le_div_iff₀ hLpos).mp hin
      linarith
    have hFge : cM / 4 * L ^ (2 : ℕ) * ξ ^ (4 : ℕ) ≤ testProfile L ξ :=
      testProfile_ge hLpos (hin.trans hεhalf) hLξ
    have hstep1 : 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * testProfile L ξ ≤
        gammaHardyPhaseRate 0 * testProfile L ξ :=
      mul_le_mul_of_nonneg_right hγ hF
    have hstep2 : gammaHardyPhaseRate 0 * testProfile L ξ ≤
        gammaHardyPhaseRate 0 * (cM / 4 * L ^ (2 : ℕ) * ξ ^ (4 : ℕ)) :=
      mul_le_mul_of_nonpos_left hFge hg0.le
    linarith
  · have hnotmem : ξ ∉ Icc (-(epsTwo / L)) (epsTwo / L) := by
      rw [mem_Icc]
      intro h
      exact hin (abs_le.mpr h)
    rw [indicator_of_notMem hnotmem, zero_add]
    by_cases hmid : |ξ| ≤ ξ₀
    · -- middle region: the integrand is nonpositive
      have hξt : |2 * Real.pi * ξ| ≤ t₀ := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        have h1 := hmid
        rw [hξ₀, le_div_iff₀ (by positivity)] at h1
        linarith
      have hγ : 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) ≤ gammaHardyPhaseRate 0 := by
        have h := hneg (2 * Real.pi * ξ) hξt
        linarith
      have : 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * testProfile L ξ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hF
      linarith
    · -- outer region
      have hout : ξ₀ ≤ |ξ| := le_of_not_ge hmid
      have hξne : ξ ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hout
        linarith
      have hγ : gammaHardyPhaseRate (2 * Real.pi * ξ) ≤ 35 + 2 * Real.pi * |ξ| := by
        have := gammaHardyPhaseRate_le_linear (2 * Real.pi * ξ)
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at this
        exact this
      have hFle := testProfile_le hLpos hξne
      have hpt := outer_pointwise hξ₀pos hout
      have hA : 0 ≤ 35 + 2 * Real.pi * |ξ| := by positivity
      calc 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * testProfile L ξ
          ≤ 2 * (35 + 2 * Real.pi * |ξ|) * testProfile L ξ := by
            apply mul_le_mul_of_nonneg_right _ hF
            linarith
        _ ≤ 2 * (35 + 2 * Real.pi * |ξ|) * (mM ^ (2 : ℕ) * kappaTwo ^ (2 : ℕ) / L ^ (4 : ℕ) / |ξ| ^ (6 : ℕ)) :=
            mul_le_mul_of_nonneg_left hFle (by positivity)
        _ = 2 * mM ^ (2 : ℕ) * kappaTwo ^ (2 : ℕ) / L ^ (4 : ℕ) * ((35 + 2 * Real.pi * |ξ|) / |ξ| ^ (6 : ℕ)) := by
            ring
        _ ≤ 2 * mM ^ (2 : ℕ) * kappaTwo ^ (2 : ℕ) / L ^ (4 : ℕ) *
              ((35 / ξ₀ + 2 * Real.pi) * (1 + 1 / ξ₀ ^ (2 : ℕ)) / ξ₀ ^ (3 : ℕ) * (1 + ξ ^ (2 : ℕ))⁻¹) := by
            apply mul_le_mul_of_nonneg_left hpt
            have := kappaTwo_pos
            positivity
        _ = outerConst ξ₀ / L ^ (4 : ℕ) * (1 + ξ ^ (2 : ℕ))⁻¹ := by
            unfold outerConst
            ring

/-! ## Negativity of the archimedean part at large apertures -/

theorem exists_archPart_primeFreeTest_neg :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ hL : 1 ≤ L,
      archPart _ (primeFreeTest L hL).toCCMFormVector < 0 := by
  obtain ⟨t₀, ht₀, ht₀π, hneg⟩ := exists_phaseRate_negative_radius
  set ξ₀ : ℝ := t₀ / (2 * Real.pi) with hξ₀
  have hξ₀pos : 0 < ξ₀ := by rw [hξ₀]; positivity
  set Ipi : ℝ := ∫ ξ : ℝ, (1 + ξ ^ (2 : ℕ))⁻¹ with hIpi
  have hIpi0 : 0 ≤ Ipi := integral_nonneg fun ξ => by positivity
  have hcin := innerConst_pos
  have hout := outerConst_nonneg hξ₀pos
  have hε := epsTwo_pos
  -- threshold: `L > outerConst·Ipi / innerConst` and the two admissibility bounds
  set L₀ : ℝ := max (max 1 (epsTwo * (2 * Real.pi) / t₀)) (max (2 * epsTwo)
    (outerConst ξ₀ * Ipi / innerConst + 1)) with hL₀
  refine ⟨L₀, le_max_of_le_left (le_max_left _ _), fun L hLL hL => ?_⟩
  have hLbig : epsTwo * (2 * Real.pi) / t₀ ≤ L :=
    le_trans (le_max_of_le_left (le_max_right _ _)) hLL
  have hLtwo : 2 * epsTwo ≤ L := le_trans (le_max_of_le_right (le_max_left _ _)) hLL
  have hLratio : outerConst ξ₀ * Ipi / innerConst + 1 ≤ L :=
    le_trans (le_max_of_le_right (le_max_right _ _)) hLL
  have hLpos : 0 < L := by linarith
  rw [archPart_primeFreeTest_eq]
  have hmono := integral_mono (integrable_archIntegrand L hL) (integrable_majorant L ξ₀)
    (fun ξ => archIntegrand_le_majorant ht₀ ht₀π hneg hL hLbig hLtwo ξ)
  rw [integral_majorant L ξ₀ hLpos] at hmono
  refine lt_of_le_of_lt hmono ?_
  -- the closed form is `−innerConst / L³ + outerConst·Ipi / L⁴`
  have hclosed : gammaHardyPhaseRate 0 * (cM / 4 * L ^ (2 : ℕ) * (2 * (epsTwo / L) ^ (5 : ℕ) / 5)) +
      outerConst ξ₀ / L ^ (4 : ℕ) * Ipi = (-innerConst + outerConst ξ₀ * Ipi / L) / L ^ (3 : ℕ) := by
    unfold innerConst
    field_simp
    ring
  rw [hclosed]
  have hL3 : 0 < L ^ (3 : ℕ) := by positivity
  rw [div_lt_iff₀ hL3, zero_mul]
  have hratio : outerConst ξ₀ * Ipi / L < innerConst := by
    rw [div_lt_iff₀ hLpos]
    have h1 : outerConst ξ₀ * Ipi ≤ innerConst * (outerConst ξ₀ * Ipi / innerConst) := by
      rw [mul_div_cancel₀ _ hcin.ne']
    have h2 : innerConst * (outerConst ξ₀ * Ipi / innerConst) < innerConst * L := by
      apply mul_lt_mul_of_pos_left _ hcin
      linarith
    linarith
  linarith

/-! ## Main theorems -/

/-- **The prime-free restricted Weil family has negative ground energy at every sufficiently
large aperture.** -/
theorem exists_primeFree_energy_neg :
    ∃ A₀ : ℝ, ∀ a : SuzukiPositiveAperture, A₀ ≤ a.1 → primeFreeFamily.energy a < 0 := by
  obtain ⟨L₀, hL₀, hneg⟩ := exists_archPart_primeFreeTest_neg
  have hs := sTwo_pos
  refine ⟨L₀ * sTwo + 4, fun a ha => ?_⟩
  -- realise the aperture `a` as an enlarged wide-bump aperture: `a = L·sTwo + 4`
  set L : ℝ := (a.1 - 4) / sTwo with hL_def
  have hL : 1 ≤ L := by
    rw [hL_def, le_div_iff₀ hs]
    nlinarith
  have hLL : L₀ ≤ L := by
    rw [hL_def, le_div_iff₀ hs]
    linarith
  have haper : (wideBumpAperture L hL).enlarge 1 one_pos = a := by
    apply Subtype.ext
    show L * sTwo + 1 + 2 * 1 + 1 = a.1
    rw [hL_def]
    have hs' : sTwo ≠ 0 := hs.ne'
    field_simp
    ring
  have hQ : primeFreeFamily.Q _ (primeFreeTest L hL).toCCMFormVector < 0 := by
    rw [primeFreeFamily_Q_eq_archPart (primeFreeTest_isPolarConstrained L hL)]
    exact hneg L hLL hL
  have hray := primeFreeFamily.energy_mul_formNorm_sq_le _ (primeFreeTest L hL).toCCMFormVector
  have henergy : primeFreeFamily.energy ((wideBumpAperture L hL).enlarge 1 one_pos) < 0 := by
    rcases lt_or_ge (primeFreeFamily.energy ((wideBumpAperture L hL).enlarge 1 one_pos)) 0
      with h | h
    · exact h
    · exfalso
      have := mul_nonneg h (sq_nonneg ‖ccmArchimedeanFormToAperture _
        (primeFreeTest L hL).toCCMFormVector‖)
      linarith
  rw [haper] at henergy
  exact henergy

/-- **The archimedean-plus-polar restricted Weil operator, with every prime removed, has a
spectral zero crossing**: an aperture with vanishing ground energy and a nonzero kernel
element. -/
theorem exists_primeFree_zero_crossing :
    ∃ a : SuzukiPositiveAperture, primeFreeFamily.energy a = 0 ∧
      ∃ x : (primeFreeFamily.operator a).domain,
        (x : suzukiApertureHilbert a) ≠ 0 ∧ primeFreeFamily.operator a x = 0 := by
  obtain ⟨δ, hδ, hpos⟩ := exists_small_aperture_primeFree_energy_pos
  obtain ⟨A₀, hneg⟩ := exists_primeFree_energy_neg
  let a₀ : SuzukiPositiveAperture := ⟨δ / 2, by linarith⟩
  let a₁ : SuzukiPositiveAperture := ⟨max A₀ (δ / 2) + 1, by
    have := le_max_right A₀ (δ / 2); linarith⟩
  have h01 : a₀.1 ≤ a₁.1 := by
    show δ / 2 ≤ max A₀ (δ / 2) + 1
    have := le_max_right A₀ (δ / 2); linarith
  have h0 : 0 < primeFreeFamily.energy a₀ := hpos a₀ (by show δ / 2 < δ; linarith)
  have h1 : primeFreeFamily.energy a₁ < 0 :=
    hneg a₁ (by show A₀ ≤ max A₀ (δ / 2) + 1; have := le_max_left A₀ (δ / 2); linarith)
  obtain ⟨a, -, -, hzero⟩ := primeFreeFamily.exists_energy_eq_zero h01 h0 h1
  exact ⟨a, hzero, primeFreeFamily.exists_kernel_of_energy_eq_zero hzero⟩

end RHTower.WeilDeletion

end
