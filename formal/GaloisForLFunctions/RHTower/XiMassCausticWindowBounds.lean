import GaloisForLFunctions.RHTower.XiMassCausticWindowRegion

/-!
# The caustic coefficients on the balance window

On `‖s‖ ≤ √u` the propagation rate is at least `√((κ_B²−1)/2)·u`, so every quantity the Cauchy
iteration needs has its natural size:

* the transport coefficient `c₁ = 2a·w/Z` is bounded, because `‖w‖ ≍ u` and `Re Z ≍ u`;
* the zeroth-order coefficient `c₀ = symbol + a(1/Z − w²/Z³)` is `O(u^{-1/2})`, the symbol supplying
  the half power and the curvature term only `O(1/u)`;
* the conjugated carrier is `O(u^{-1/2})`, from the Schläfli envelope against `Re Z ≍ u`.

These are the three inputs of `norm_xiCausticIterate_le`.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- The propagation rate constant of the balance window. -/
def xiMassWindowRate (a : ℝ) : ℝ :=
  Real.sqrt ((xiMassSpacelikeSharpSlope a ^ 2 - 1) / 2)

theorem xiMassWindowRate_pos {a : ℝ} (ha : 1 / 2 < a) : 0 < xiMassWindowRate a := by
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  rw [xiMassWindowRate]
  exact Real.sqrt_pos.2 (by nlinarith)

theorem xiMassWindowRate_sq {a : ℝ} (ha : 1 / 2 < a) :
    xiMassWindowRate a ^ 2 = (xiMassSpacelikeSharpSlope a ^ 2 - 1) / 2 := by
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  rw [xiMassWindowRate]
  exact Real.sq_sqrt (by nlinarith)

theorem sqrt_le_self_of_one_le {u : ℝ} (hu : 1 ≤ u) : Real.sqrt u ≤ u := by
  have h : Real.sqrt u ≤ Real.sqrt (u ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq (by linarith)] at h

/-- **The propagation rate on the balance window.** -/
theorem xiMassWindowRate_mul_le_csqrtRe {a sigma u : ℝ} (ha : 1 / 2 < a)
    (hu : xiMassWindowThreshold a ≤ u) {s : ℂ} (hs : ‖s‖ ≤ Real.sqrt u) :
    xiMassWindowRate a * u
      ≤ HTGeometry.csqrtRe (((sigma : ℂ) + (u : ℂ) * Complex.I) ^ 2
          + ((((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + s) ^ 2) := by
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_xiMassWindowThreshold a) hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hq0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
  set z : ℂ := ((sigma : ℂ) + (u : ℂ) * Complex.I) ^ 2
    + ((((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + s) ^ 2 with hzdef
  have hlow : (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ 2 / 2 ≤ z.re :=
    re_propagation_ge_of_window (sigma := sigma) ha hu hs
  have hzre : (0 : ℝ) < z.re := lt_of_lt_of_le (by positivity) hlow
  have hsq := HTGeometry.re_le_sq_csqrtRe hzre
  have hrate := xiMassWindowRate_sq ha
  have hrpos : (0 : ℝ) < xiMassWindowRate a := xiMassWindowRate_pos ha
  have hcpos : (0 : ℝ) < HTGeometry.csqrtRe z := HTGeometry.csqrtRe_pos hzre
  have hkey : (xiMassWindowRate a * u) ^ 2 ≤ HTGeometry.csqrtRe z ^ 2 := by
    have hexp : (xiMassWindowRate a * u) ^ 2
        = (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ 2 / 2 := by
      rw [mul_pow, hrate]
      ring
    rw [hexp]
    linarith
  nlinarith [hkey, hrpos, hu0, hcpos]

/-- **The transport coefficient is bounded on the balance window.** -/
theorem norm_xiCausticCoeffOne_le_window {a sigma u : ℝ} (ha : 1 / 2 < a)
    (hu : xiMassWindowThreshold a ≤ u) {s : ℂ} (hs : ‖s‖ ≤ Real.sqrt u) :
    ‖xiCausticCoeffOne a ((sigma : ℂ) + (u : ℂ) * Complex.I)
        ((((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + s)‖
      ≤ 2 * a * (xiMassSpacelikeSharpSlope a + 1) / xiMassWindowRate a := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_xiMassWindowThreshold a) hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hκ0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a := by linarith
  have hrpos : (0 : ℝ) < xiMassWindowRate a := xiMassWindowRate_pos ha
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set w : ℂ := (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + s with hwdef
  have hzre : (0 : ℝ) < (τ ^ 2 + w ^ 2).re := by
    have hlow : (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ 2 / 2 ≤ (τ ^ 2 + w ^ 2).re :=
      re_propagation_ge_of_window (sigma := sigma) ha hu hs
    have hq0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
    have : (0 : ℝ) < (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ 2 / 2 := by positivity
    linarith
  have hZre : (xiMassHeightRadius τ w).re = HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) := by
    rw [xiMassHeightRadius, HTGeometry.csqrt_re]
  have hrate := xiMassWindowRate_mul_le_csqrtRe (sigma := sigma) ha hu hs
  have hZnorm : xiMassWindowRate a * u ≤ ‖xiMassHeightRadius τ w‖ := by
    refine le_trans hrate ?_
    have h := Complex.abs_re_le_norm (xiMassHeightRadius τ w)
    rw [hZre] at h
    have hc0 : (0 : ℝ) < HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) := HTGeometry.csqrtRe_pos hzre
    calc HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) ≤ |HTGeometry.csqrtRe (τ ^ 2 + w ^ 2)| :=
          le_abs_self _
      _ ≤ ‖xiMassHeightRadius τ w‖ := h
  have hwnorm : ‖w‖ ≤ (xiMassSpacelikeSharpSlope a + 1) * u := by
    have h1 : ‖w‖ ≤ ‖(((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)‖ + ‖s‖ := by
      rw [hwdef]; exact norm_add_le _ _
    have h2 : ‖(((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)‖ = xiMassSpacelikeSharpSlope a * u := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h3 : Real.sqrt u ≤ u := sqrt_le_self_of_one_le hu1
    rw [h2] at h1
    nlinarith [h1, hs, h3]
  have hZpos : (0 : ℝ) < ‖xiMassHeightRadius τ w‖ := by
    have := mul_pos hrpos hu0
    linarith
  rw [xiCausticCoeffOne, xiMassRadiusRate, norm_mul, norm_div]
  have hcoef : ‖2 * (a : ℂ)‖ = 2 * a := by
    rw [show (2 : ℂ) * (a : ℂ) = ((2 * a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hcoef]
  have hq : ‖w‖ / ‖xiMassHeightRadius τ w‖
      ≤ (xiMassSpacelikeSharpSlope a + 1) * u / (xiMassWindowRate a * u) := by
    have h1 : ‖w‖ / ‖xiMassHeightRadius τ w‖
        ≤ (xiMassSpacelikeSharpSlope a + 1) * u / ‖xiMassHeightRadius τ w‖ :=
      div_le_div_of_nonneg_right hwnorm (norm_nonneg _)
    have h2 : (xiMassSpacelikeSharpSlope a + 1) * u / ‖xiMassHeightRadius τ w‖
        ≤ (xiMassSpacelikeSharpSlope a + 1) * u / (xiMassWindowRate a * u) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hZnorm
    linarith
  have hval : (xiMassSpacelikeSharpSlope a + 1) * u / (xiMassWindowRate a * u)
      = (xiMassSpacelikeSharpSlope a + 1) / xiMassWindowRate a := by
    field_simp
  rw [hval] at hq
  have hfin : 2 * a * (‖w‖ / ‖xiMassHeightRadius τ w‖)
      ≤ 2 * a * ((xiMassSpacelikeSharpSlope a + 1) / xiMassWindowRate a) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  calc 2 * a * (‖w‖ / ‖xiMassHeightRadius τ w‖)
      ≤ 2 * a * ((xiMassSpacelikeSharpSlope a + 1) / xiMassWindowRate a) := hfin
    _ = 2 * a * (xiMassSpacelikeSharpSlope a + 1) / xiMassWindowRate a := by ring

/-- **The zeroth-order coefficient is `O(u^{-1/2})` on the balance window.** -/
theorem exists_norm_xiCausticCoeffZero_le_window {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) :
    ∃ C u₀ : ℝ, 0 < C ∧ xiMassWindowThreshold a ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ s : ℂ,
      ‖s‖ ≤ Real.sqrt u →
      ‖xiCausticCoeffZero a ((sigma : ℂ) + (u : ℂ) * Complex.I)
          ((((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + s)‖ ≤ C / Real.sqrt u := by
  obtain ⟨Cs, us, hCs, hus, hsym⟩ := exists_norm_xiMassCausticSymbolC_le ha hsigma
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hκ0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a := by linarith
  set c : ℝ := xiMassWindowRate a with hcdef
  have hc0 : (0 : ℝ) < c := xiMassWindowRate_pos ha
  refine ⟨Cs + a * (1 / c + (xiMassSpacelikeSharpSlope a + 1) ^ 2 / c ^ 3),
    max us (xiMassWindowThreshold a), by positivity, le_max_right _ _, ?_⟩
  intro u hu s hs
  have hus' : us ≤ u := le_trans (le_max_left _ _) hu
  have huw : xiMassWindowThreshold a ≤ u := le_trans (le_max_right _ _) hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_xiMassWindowThreshold a) huw
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hru : Real.sqrt u ≤ u := sqrt_le_self_of_one_le hu1
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set w : ℂ := (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + s with hwdef
  have hlow : (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ 2 / 2 ≤ (τ ^ 2 + w ^ 2).re :=
    re_propagation_ge_of_window (sigma := sigma) ha huw hs
  have hq0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
  have hzre : (0 : ℝ) < (τ ^ 2 + w ^ 2).re := by
    have : (0 : ℝ) < (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ 2 / 2 := by positivity
    linarith
  have hrate := xiMassWindowRate_mul_le_csqrtRe (sigma := sigma) ha huw hs
  have hZre : (xiMassHeightRadius τ w).re = HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) := by
    rw [xiMassHeightRadius, HTGeometry.csqrt_re]
  have hZnorm : c * u ≤ ‖xiMassHeightRadius τ w‖ := by
    refine le_trans hrate ?_
    have h := Complex.abs_re_le_norm (xiMassHeightRadius τ w)
    rw [hZre] at h
    exact le_trans (le_abs_self _) h
  have hZpos : (0 : ℝ) < ‖xiMassHeightRadius τ w‖ := lt_of_lt_of_le (by positivity) hZnorm
  have hwnorm : ‖w‖ ≤ (xiMassSpacelikeSharpSlope a + 1) * u := by
    have h1 : ‖w‖ ≤ ‖(((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)‖ + ‖s‖ := by
      rw [hwdef]; exact norm_add_le _ _
    have h2 : ‖(((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)‖
        = xiMassSpacelikeSharpSlope a * u := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2] at h1
    nlinarith [h1, hs, hru]
  -- the curvature term
  have hcurv : ‖(a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3)‖
      ≤ a * (1 / c + (xiMassSpacelikeSharpSlope a + 1) ^ 2 / c ^ 3) / u := by
    have hanorm : ‖(a : ℂ)‖ = a := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    have h1 : ‖1 / xiMassHeightRadius τ w‖ ≤ 1 / (c * u) := by
      rw [norm_div, norm_one]
      exact div_le_div_of_nonneg_left zero_le_one (by positivity) hZnorm
    have h2 : ‖w ^ 2 / xiMassHeightRadius τ w ^ 3‖
        ≤ ((xiMassSpacelikeSharpSlope a + 1) * u) ^ 2 / (c * u) ^ 3 := by
      rw [norm_div, norm_pow, norm_pow]
      have hnum : ‖w‖ ^ 2 ≤ ((xiMassSpacelikeSharpSlope a + 1) * u) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg w) hwnorm 2
      have hden : (c * u) ^ 3 ≤ ‖xiMassHeightRadius τ w‖ ^ 3 :=
        pow_le_pow_left₀ (by positivity) hZnorm 3
      have hstep1 : ‖w‖ ^ 2 / ‖xiMassHeightRadius τ w‖ ^ 3
          ≤ ((xiMassSpacelikeSharpSlope a + 1) * u) ^ 2 / ‖xiMassHeightRadius τ w‖ ^ 3 :=
        div_le_div_of_nonneg_right hnum (by positivity)
      have hstep2 : ((xiMassSpacelikeSharpSlope a + 1) * u) ^ 2 / ‖xiMassHeightRadius τ w‖ ^ 3
          ≤ ((xiMassSpacelikeSharpSlope a + 1) * u) ^ 2 / (c * u) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      linarith
    have hsub : ‖1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3‖
        ≤ 1 / (c * u) + ((xiMassSpacelikeSharpSlope a + 1) * u) ^ 2 / (c * u) ^ 3 := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith
    have hval : 1 / (c * u) + ((xiMassSpacelikeSharpSlope a + 1) * u) ^ 2 / (c * u) ^ 3
        = (1 / c + (xiMassSpacelikeSharpSlope a + 1) ^ 2 / c ^ 3) / u := by
      field_simp
    rw [norm_mul, hanorm]
    have hstep := mul_le_mul_of_nonneg_left hsub ha0.le
    calc a * ‖1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3‖
        ≤ a * (1 / (c * u) + ((xiMassSpacelikeSharpSlope a + 1) * u) ^ 2 / (c * u) ^ 3) := hstep
      _ = a * (1 / c + (xiMassSpacelikeSharpSlope a + 1) ^ 2 / c ^ 3) / u := by
          rw [hval]; ring
  have hsymb := hsym u hus' s hs
  rw [← hτdef] at hsymb
  have hcurv' : a * (1 / c + (xiMassSpacelikeSharpSlope a + 1) ^ 2 / c ^ 3) / u
      ≤ a * (1 / c + (xiMassSpacelikeSharpSlope a + 1) ^ 2 / c ^ 3) / Real.sqrt u :=
    div_le_div_of_nonneg_left (by positivity) hr0 hru
  rw [xiCausticCoeffZero]
  have htri := norm_add_le (xiMassCausticSymbolC a τ w)
    ((a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3))
  have hsplit : (Cs + a * (1 / c + (xiMassSpacelikeSharpSlope a + 1) ^ 2 / c ^ 3)) / Real.sqrt u
      = Cs / Real.sqrt u
        + a * (1 / c + (xiMassSpacelikeSharpSlope a + 1) ^ 2 / c ^ 3) / Real.sqrt u := by
    field_simp
  rw [hsplit]
  linarith [htri, hsymb, hcurv, hcurv']

/-- **The conjugated carrier is `O(u^{-1/2})` on the balance window.** -/
theorem exists_norm_conjugatedCarrier_le_window {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) :
    ∃ C u₀ : ℝ, 0 < C ∧ xiMassWindowThreshold a ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ s : ℂ,
      ‖s‖ ≤ Real.sqrt u →
      ‖xiMassConjugatedCarrier a ((sigma : ℂ) + (u : ℂ) * Complex.I)
          ((((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + s)‖ ≤ C / Real.sqrt u := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  set c : ℝ := xiMassWindowRate a with hcdef
  have hc0 : (0 : ℝ) < c := xiMassWindowRate_pos ha
  refine ⟨2 * a * (sigma + 1) / c
      * (Real.exp (1 / (2 * (a * c))) * Real.sqrt (2 * Real.pi / (a * c))),
    xiMassWindowThreshold a, by positivity, le_rfl, ?_⟩
  intro u hu s hs
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_xiMassWindowThreshold a) hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hrsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set w : ℂ := (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + s with hwdef
  have hlow : (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ 2 / 2 ≤ (τ ^ 2 + w ^ 2).re :=
    re_propagation_ge_of_window (sigma := sigma) ha hu hs
  have hq0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
  have hzre : (0 : ℝ) < (τ ^ 2 + w ^ 2).re := by
    have : (0 : ℝ) < (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ 2 / 2 := by positivity
    linarith
  set R : ℝ := HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) with hRdef
  have hR0 : (0 : ℝ) < R := HTGeometry.csqrtRe_pos hzre
  have hRge : c * u ≤ R := xiMassWindowRate_mul_le_csqrtRe (sigma := sigma) ha hu hs
  have hcu0 : (0 : ℝ) < c * u := by positivity
  have hτnorm : ‖τ‖ ≤ (sigma + 1) * u := by
    have h1 : ‖τ‖ ≤ ‖(sigma : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ := by
      rw [hτdef]; exact norm_add_le _ _
    have h2 : ‖(sigma : ℂ)‖ = sigma := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsigma]
    have h3 : ‖(u : ℂ) * Complex.I‖ = u := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hu0]
    rw [h2, h3] at h1
    nlinarith [h1, hsigma.le, hu1]
  have hmain := norm_xiMassConjugatedCarrier_le (a := a) (τ := τ) (w := w) ha0 hzre
  rw [← hRdef] at hmain
  -- three monotone replacements
  have hfac1 : 2 * a * ‖τ‖ / R ≤ 2 * a * (sigma + 1) / c := by
    have hnum : 2 * a * ‖τ‖ ≤ 2 * a * ((sigma + 1) * u) :=
      mul_le_mul_of_nonneg_left hτnorm (by positivity)
    have hstep1 : 2 * a * ‖τ‖ / R ≤ 2 * a * ((sigma + 1) * u) / R :=
      div_le_div_of_nonneg_right hnum hR0.le
    have hstep2 : 2 * a * ((sigma + 1) * u) / R ≤ 2 * a * ((sigma + 1) * u) / (c * u) :=
      div_le_div_of_nonneg_left (by positivity) hcu0 hRge
    have hval : 2 * a * ((sigma + 1) * u) / (c * u) = 2 * a * (sigma + 1) / c := by
      field_simp
    linarith [hstep1, hstep2, hval.le, hval.ge]
  have hfac2 : Real.exp (1 / (2 * (a * R))) ≤ Real.exp (1 / (2 * (a * c))) := by
    refine Real.exp_le_exp.2 ?_
    have hcc : c ≤ c * u := by nlinarith [hc0, hu1]
    have hcR : c ≤ R := le_trans hcc hRge
    have hinner : 2 * (a * c) ≤ 2 * (a * R) := by nlinarith [hcR, ha0]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) hinner
  have hfac3 : Real.sqrt (2 * Real.pi / (a * R))
      ≤ Real.sqrt (2 * Real.pi / (a * c)) / Real.sqrt u := by
    have hval : Real.sqrt (2 * Real.pi / (a * c)) / Real.sqrt u
        = Real.sqrt (2 * Real.pi / (a * c * u)) := by
      rw [← Real.sqrt_div' _ (by positivity)]
      congr 1
      field_simp
    rw [hval]
    refine Real.sqrt_le_sqrt ?_
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [hRge, ha0]
  have hnn2 : (0 : ℝ) ≤ Real.exp (1 / (2 * (a * R))) := (Real.exp_pos _).le
  have hnn3 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi / (a * R)) := Real.sqrt_nonneg _
  have hprod : Real.exp (1 / (2 * (a * R))) * Real.sqrt (2 * Real.pi / (a * R))
      ≤ Real.exp (1 / (2 * (a * c))) * (Real.sqrt (2 * Real.pi / (a * c)) / Real.sqrt u) :=
    mul_le_mul hfac2 hfac3 hnn3 (Real.exp_pos _).le
  have hfin : 2 * a * ‖τ‖ / R * (Real.exp (1 / (2 * (a * R)))
        * Real.sqrt (2 * Real.pi / (a * R)))
      ≤ 2 * a * (sigma + 1) / c
        * (Real.exp (1 / (2 * (a * c))) * (Real.sqrt (2 * Real.pi / (a * c)) / Real.sqrt u)) :=
    mul_le_mul hfac1 hprod (by positivity) (by positivity)
  refine le_trans hmain (le_trans hfin (le_of_eq ?_))
  field_simp

end

end RHTower
