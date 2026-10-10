import GaloisForLFunctions.RHTower.GaussianCentralGapFilterLightCone

/-!
# Finite-range converse: every off-line zero breaks the central budget at an explicit scale

Let `G(u) = P_½(e^{-u}) − C_½(e^{-u})` and filter it with the Gaussian window of width `ε` centred at
`2ε`, twisted by `e^{−iτu}`.  A zero `ρ = ½ + δ + iγ` enters the filtered zero series with weight
`e^{εE_ρ(τ)}`, `E_ρ(τ) = δ + δ²/8 − (γ − 2τ)²/8`: a downward parabola in `τ` with vertex `γ/2`.

**Locally extremal zeros** (`not_gaussianCentralGap_budget_of_localExtremalZero`).  If `ρ₀` with
`δ₀ > 0` strictly maximizes `Re ρ` among the zeros of height within `4` of `γ₀`, then at `τ = γ₀/2` all
other zeros lie at least `g > 0` below `Ψ₀ = δ₀ + δ₀²/8`, and `|G| ≤ K` fails on `(0, 4ε]` as soon as
`A e^{−εg} ≤ |c₀|/2` and `K + C < (|c₀|/2) e^{εΨ₀}` (`c₀ = ½Γ((ρ₀−½)/2)`, `A = Σ_ρ |½Γ((ρ−½)/2)|`).

**Every off-line zero** (`not_gaussianCentralGap_budget_of_offLineZero`).  Two parabolas with
distinct vertices cross at one centre, and equal vertices with equal height force equal zeros.  So a
centre `τ ∈ [γ₀/2, γ₀/2 + √Ψ₀/2]` avoiding the finitely many crossings of the zeros near `ρ₀` has a
unique dominant zero `ρ₁` with `E_{ρ₁}(τ) ≥ Ψ₀/2` and a gap `g > 0` to all other zeros.  Hence `|G| ≤ K`
fails on `(0, 4ε]` once `A e^{−εg} ≤ |c₁|/2` and `K + C < (|c₁|/2) e^{εE_{ρ₁}(τ)}`.  No separation or
simplicity hypothesis enters: ties among equal real parts (the Turán/Pintz cluster case) are broken by
the height-dependence of the light-cone exponent.

Both bounds rest on the same estimate: the budget on `(0, 4ε]` and the unconditional envelope
`|G(u)| ≤ C₁e^{u/4}` bound the filtered gap by `K√(2πε) + O(1)`; the filtered zero expansion turns this
into a bound on the zero series; the copies of the dominant zero are equal terms and add up, and the
rest is smaller by `e^{−εg}`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- Unconditional exponential envelope of the central gap. -/
theorem exists_abs_gaussianCentralGapLog_le_exp :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ u : ℝ, 0 < u → |gaussianCentralGapLog u| ≤ C₁ * Real.exp (u / 4) := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_norm_gaussianCentralGapLog_add_zeroSeries_le
  have hAs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude
  set A : ℝ := ∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨C₀ + A, by positivity, fun u hu => ?_⟩
  have hterm : ∀ q : XiZeroCopy, ‖zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)‖ ≤
      ‖zeroBohrAmplitude q‖ * Real.exp (u / 4) := by
    intro q
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have hre : ((xiZero q - 1 / 2) / 2 * (u : ℂ)).re = ((xiZero q - 1 / 2) / 2).re * u := by simp
    rw [hre]
    nlinarith [(re_xiZero_sub_half_div_two_le q).2]
  have hsZ : Summable fun q : XiZeroCopy =>
      ‖zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hAs.mul_right _)
  have hZ : ‖∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)‖ ≤
      A * Real.exp (u / 4) := by
    refine (norm_tsum_le_tsum_norm hsZ).trans ?_
    rw [hA, ← tsum_mul_right]
    exact Summable.tsum_le_tsum hterm hsZ (hAs.mul_right _)
  have h1 := hC₀b u hu
  have htri := norm_sub_le ((gaussianCentralGapLog u : ℂ) + ∑' q : XiZeroCopy,
      zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u))
    (∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u))
  rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] at htri
  have he : 1 ≤ Real.exp (u / 4) := Real.one_le_exp (by linarith)
  nlinarith

/-- The Gaussian window beyond `4ε`, weighted by `e^{u/4}`, has mass at most `4/3`. -/
theorem integral_Ioi_exp_quarter_mul_window_le {ε : ℝ} (hε : 0 < ε) :
    ∫ u in Ioi (4 * ε), Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) ≤ 4 / 3 := by
  have hpt : ∀ u ∈ Ioi (4 * ε), Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) ≤
      Real.exp (3 * ε) * Real.exp (-(3 / 4) * u) := by
    intro u hu
    have hu' : 4 * ε < u := hu
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hsq : (u - 2 * ε) ≤ (u - 2 * ε) ^ 2 / (2 * ε) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hint : IntegrableOn (fun u : ℝ => Real.exp (3 * ε) * Real.exp (-(3 / 4) * u)) (Ioi (4 * ε)) :=
    (integrableOn_exp_mul_Ioi (by norm_num) (4 * ε)).const_mul _
  have hint' : IntegrableOn (fun u : ℝ => Real.exp (u / 4) *
      Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))) (Ioi (4 * ε)) :=
    (integrable_exp_quarter_mul_gaussianWindow hε).integrableOn
  calc ∫ u in Ioi (4 * ε), Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))
      ≤ ∫ u in Ioi (4 * ε), Real.exp (3 * ε) * Real.exp (-(3 / 4) * u) :=
        setIntegral_mono_on hint' hint measurableSet_Ioi hpt
    _ = 4 / 3 := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num) (4 * ε),
          show -(3 / 4 : ℝ) * (4 * ε) = -(3 * ε) by ring]
        have he : Real.exp (3 * ε) * Real.exp (-(3 * ε)) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        field_simp
        linarith

/-- **Finite budget bounds the filtered gap.**  If `|G| ≤ K` on `(0, 4ε]` then
`‖F(ε, τ)‖ ≤ K√(2πε) + (4/3)C₁`. -/
theorem norm_filteredCentralGap_le_of_budget {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hC₁b : ∀ u : ℝ, 0 < u → |gaussianCentralGapLog u| ≤ C₁ * Real.exp (u / 4))
    {ε : ℝ} (hε : 0 < ε) (τ : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbud : ∀ u ∈ Ioc (0 : ℝ) (4 * ε), |gaussianCentralGapLog u| ≤ K) :
    ‖gaussianFilteredCentralGap ε τ‖ ≤ K * Real.sqrt (2 * Real.pi * ε) + 4 / 3 * C₁ := by
  set f : ℝ → ℝ := fun u => ‖(gaussianCentralGapLog u : ℂ) * gaussianFilterKernel ε τ u‖ with hf
  have hfc : Continuous f := by
    have := (Complex.continuous_ofReal.comp continuous_gaussianCentralGapLog).mul
      (continuous_gaussianFilterKernel ε τ)
    exact this.norm
  have hfb : ∀ u : ℝ, 0 < u → f u ≤ C₁ * (Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))) := by
    intro u hu
    simp only [hf]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gaussianFilterKernel]
    calc |gaussianCentralGapLog u| * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))
        ≤ (C₁ * Real.exp (u / 4)) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) := by
          gcongr; exact hC₁b u hu
      _ = _ := by ring
  have hfint : IntegrableOn f (Ioi 0) := by
    refine ((integrable_exp_quarter_mul_gaussianWindow hε).const_mul C₁).integrableOn.mono'
      hfc.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hfb u hu
  have hsplit : ∫ u in Ioi (0 : ℝ), f u = (∫ u in Ioc (0 : ℝ) (4 * ε), f u) +
      ∫ u in Ioi (4 * ε), f u := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hfint.mono_set Ioc_subset_Ioi_self)
      (hfint.mono_set (Ioi_subset_Ioi (by positivity))),
      Ioc_union_Ioi_eq_Ioi (by positivity)]
  have h1 : ∫ u in Ioc (0 : ℝ) (4 * ε), f u ≤ K * Real.sqrt (2 * Real.pi * ε) := by
    have hle : ∀ u ∈ Ioc (0 : ℝ) (4 * ε), f u ≤ K * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) := by
      intro u hu
      simp only [hf]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gaussianFilterKernel]
      exact mul_le_mul_of_nonneg_right (hbud u hu) (Real.exp_pos _).le
    calc ∫ u in Ioc (0 : ℝ) (4 * ε), f u
        ≤ ∫ u in Ioc (0 : ℝ) (4 * ε), K * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) :=
          setIntegral_mono_on (hfint.mono_set Ioc_subset_Ioi_self)
            ((integrable_gaussianWindow hε).const_mul K).integrableOn measurableSet_Ioc hle
      _ ≤ ∫ u : ℝ, K * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) :=
          setIntegral_le_integral ((integrable_gaussianWindow hε).const_mul K)
            (Eventually.of_forall fun u => by positivity)
      _ = K * Real.sqrt (2 * Real.pi * ε) := by rw [integral_const_mul, integral_gaussianWindow hε]
  have h2 : ∫ u in Ioi (4 * ε), f u ≤ 4 / 3 * C₁ := by
    calc ∫ u in Ioi (4 * ε), f u
        ≤ ∫ u in Ioi (4 * ε), C₁ * (Real.exp (u / 4) *
            Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))) :=
          setIntegral_mono_on (hfint.mono_set (Ioi_subset_Ioi (by positivity)))
            ((integrable_exp_quarter_mul_gaussianWindow hε).const_mul C₁).integrableOn
            measurableSet_Ioi (fun u hu => hfb u (lt_trans (by positivity) hu))
      _ = C₁ * ∫ u in Ioi (4 * ε), Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) :=
          integral_const_mul _ _
      _ ≤ C₁ * (4 / 3) := mul_le_mul_of_nonneg_left (integral_Ioi_exp_quarter_mul_window_le hε) hC₁
      _ = 4 / 3 * C₁ := by ring
  calc ‖gaussianFilteredCentralGap ε τ‖ ≤ ∫ u in Ioi (0 : ℝ), f u :=
        norm_integral_le_integral_norm _
    _ = _ := hsplit
    _ ≤ _ := add_le_add h1 h2

/-- `−Re w_q(γ₀/2) = δ_q + δ_q²/8 − (γ_q − γ₀)²/8`. -/
theorem neg_re_zeroLightConeExponent_eq (q q₀ : XiZeroCopy) :
    -(zeroLightConeExponent ((xiZero q₀).im / 2) q).re =
      ((xiZero q).re - 1 / 2) + ((xiZero q).re - 1 / 2) ^ 2 / 8 -
        ((xiZero q).im - (xiZero q₀).im) ^ 2 / 8 := by
  rw [re_zeroLightConeExponent]
  ring

/-- `−Re w_q(τ) = δ_q + δ_q²/8 − (γ_q − 2τ)²/8`. -/
theorem neg_re_zeroLightConeExponent_eq_centre (τ : ℝ) (q : XiZeroCopy) :
    -(zeroLightConeExponent τ q).re =
      ((xiZero q).re - 1 / 2) + ((xiZero q).re - 1 / 2) ^ 2 / 8 - ((xiZero q).im - 2 * τ) ^ 2 / 8 := by
  rw [re_zeroLightConeExponent]
  ring

/-- Zeros far from a centre near `γ₀/2` have negative light-cone exponent. -/
theorem neg_re_zeroLightConeExponent_neg_of_far {q₀ q : XiZeroCopy} {τ : ℝ}
    (hτ : |2 * τ - (xiZero q₀).im| ≤ 1)
    (hq : ‖xiZero q₀ - 1 / 2‖ + 6 < ‖xiZero q - 1 / 2‖) :
    -(zeroLightConeExponent τ q).re < 0 := by
  rw [neg_re_zeroLightConeExponent_eq_centre]
  have hb := re_xiZero_sub_half_bounds q
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
  have hn1 : ‖xiZero q - 1 / 2‖ ≤ 1 / 2 + |(xiZero q).im| := by
    calc ‖xiZero q - 1 / 2‖ ≤ |(xiZero q - 1 / 2).re| + |(xiZero q - 1 / 2).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 / 2 + |(xiZero q).im| := by
          have : |(xiZero q - 1 / 2).re| ≤ 1 / 2 := by
            simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
            exact abs_le.2 ⟨by linarith, by linarith⟩
          have h2 : (xiZero q - 1 / 2).im = (xiZero q).im := by simp
          rw [h2]; linarith
  have hn0 : |(xiZero q₀).im| ≤ ‖xiZero q₀ - 1 / 2‖ := by
    have h2 : (xiZero q₀ - 1 / 2).im = (xiZero q₀).im := by simp
    rw [← h2]; exact Complex.abs_im_le_norm _
  have hgap : 4 ≤ |(xiZero q).im - 2 * τ| := by
    have h1 := abs_sub_abs_le_abs_sub (xiZero q).im (2 * τ)
    have h2 : |2 * τ| ≤ |(xiZero q₀).im| + 1 := by
      have := abs_sub_abs_le_abs_sub (2 * τ) (xiZero q₀).im
      linarith
    linarith
  have h16 : 16 ≤ ((xiZero q).im - 2 * τ) ^ 2 := by
    have := sq_abs ((xiZero q).im - 2 * τ)
    nlinarith
  nlinarith

/-- A strict bound on a finite set and a negative bound off it give a uniform gap. -/
theorem exists_uniform_gap_of_finite {ι : Type*} (T : Finset ι) (P : ι → Prop) [DecidablePred P]
    (E : ι → ℝ) {M : ℝ} (hM : 0 < M) (hstrict : ∀ q ∈ T, ¬ P q → E q < M)
    (hfar : ∀ q, q ∉ T → E q < 0) :
    ∃ g : ℝ, 0 < g ∧ ∀ q, ¬ P q → E q ≤ M - g := by
  rcases (T.filter fun q => ¬ P q).eq_empty_or_nonempty with he | hne
  · refine ⟨M, hM, fun q hq => ?_⟩
    by_cases hqT : q ∈ T
    · exfalso
      have : q ∈ T.filter fun q => ¬ P q := Finset.mem_filter.2 ⟨hqT, hq⟩
      rw [he] at this
      exact Finset.notMem_empty q this
    · linarith [hfar q hqT]
  · obtain ⟨q₂, hq₂, hmin⟩ := (T.filter fun q => ¬ P q).exists_min_image (fun q => M - E q) hne
    have hq₂' := Finset.mem_filter.1 hq₂
    have hg2 : 0 < M - E q₂ := by linarith [hstrict q₂ hq₂'.1 hq₂'.2]
    refine ⟨min M (M - E q₂), lt_min hM hg2, fun q hq => ?_⟩
    by_cases hqT : q ∈ T
    · have := hmin q (Finset.mem_filter.2 ⟨hqT, hq⟩)
      have := min_le_right M (M - E q₂)
      linarith
    · have := hfar q hqT
      have := min_le_left M (M - E q₂)
      linarith

/-- **The local gap.**  If `ρ₀` (with `Re ρ₀ > ½`) strictly maximizes `Re ρ` among the zeros of height
within `4` of its own, every other zero has light-cone exponent at most `Ψ₀ − g` at the centre `γ₀/2`. -/
theorem exists_lightCone_gap_of_localExtremalZero {q₀ : XiZeroCopy} (hoff : 1 / 2 < (xiZero q₀).re)
    (hloc : ∀ q : XiZeroCopy, xiZero q ≠ xiZero q₀ →
      |(xiZero q).im - (xiZero q₀).im| < 4 → (xiZero q).re < (xiZero q₀).re) :
    ∃ g : ℝ, 0 < g ∧ ∀ q : XiZeroCopy, xiZero q ≠ xiZero q₀ →
      -(zeroLightConeExponent ((xiZero q₀).im / 2) q).re ≤
        ((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8 - g := by
  classical
  have hb₀ := re_xiZero_sub_half_bounds q₀
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb₀
  have hstrict : ∀ q : XiZeroCopy, xiZero q ≠ xiZero q₀ →
      -(zeroLightConeExponent ((xiZero q₀).im / 2) q).re <
        ((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8 := by
    intro q hq
    rw [neg_re_zeroLightConeExponent_eq]
    have hb := re_xiZero_sub_half_bounds q
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
    by_cases hnear : |(xiZero q).im - (xiZero q₀).im| < 4
    · have hlt := hloc q hq hnear
      have hsq : 0 ≤ ((xiZero q).im - (xiZero q₀).im) ^ 2 / 8 := by positivity
      nlinarith
    · push Not at hnear
      have h16 : 16 ≤ ((xiZero q).im - (xiZero q₀).im) ^ 2 := by
        have := sq_abs ((xiZero q).im - (xiZero q₀).im)
        nlinarith
      nlinarith
  have hfin := finite_xiZeroCopy_norm_le (‖xiZero q₀ - 1 / 2‖ + 6)
  refine exists_uniform_gap_of_finite hfin.toFinset (fun q => xiZero q = xiZero q₀)
    (fun q => -(zeroLightConeExponent ((xiZero q₀).im / 2) q).re) (by nlinarith)
    (fun q _ hq => hstrict q hq) (fun q hq => ?_)
  refine neg_re_zeroLightConeExponent_neg_of_far (q₀ := q₀) (τ := (xiZero q₀).im / 2)
    (by rw [show 2 * ((xiZero q₀).im / 2) - (xiZero q₀).im = 0 by ring, abs_zero]; norm_num) ?_
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le, norm_xiSpectralPoint] at hq
  exact hq

theorem zeroBohrAmplitude_congr_xiZero {q q' : XiZeroCopy} (h : xiZero q = xiZero q') :
    zeroBohrAmplitude q = zeroBohrAmplitude q' := by
  unfold zeroBohrAmplitude; rw [h]

theorem zeroLightConeExponent_eq_of_xiZero_eq {τ : ℝ} {q q' : XiZeroCopy} (h : xiZero q = xiZero q') :
    zeroLightConeExponent τ q = zeroLightConeExponent τ q' := by
  unfold zeroLightConeExponent; rw [h]

/-- **Lower bound at a dominant zero**, for an arbitrary centre `τ`. -/
theorem norm_lightConeSeries_ge_of_dominant {τ g : ℝ} {q₁ : XiZeroCopy}
    (hgap : ∀ q : XiZeroCopy, xiZero q ≠ xiZero q₁ →
      -(zeroLightConeExponent τ q).re ≤ -(zeroLightConeExponent τ q₁).re - g)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Real.exp (ε * -(zeroLightConeExponent τ q₁).re) *
        (‖zeroBohrAmplitude q₁‖ - (∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖) * Real.exp (-(ε * g))) ≤
      ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ := by
  classical
  set M : ℝ := -(zeroLightConeExponent τ q₁).re with hM
  set f : XiZeroCopy → ℂ := fun q => zeroBohrAmplitude q *
    Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q) with hf
  set P : XiZeroCopy → Prop := fun q => xiZero q = xiZero q₁ with hP
  have hAs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude
  set A : ℝ := ∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ with hA
  have hnormf : ∀ q, ‖f q‖ = ‖zeroBohrAmplitude q‖ *
      Real.exp (ε * -(zeroLightConeExponent τ q).re) := by
    intro q
    simp only [hf]
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp
  have hfs : Summable fun q => ‖f q‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hAs.mul_right (Real.exp ε))
    rw [hnormf]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    nlinarith [neg_re_zeroLightConeExponent_le τ q]
  have hfib : {q : XiZeroCopy | P q}.Finite := by
    refine (finite_xiZeroCopy_norm_le ‖xiZero q₁ - 1 / 2‖).subset fun q hq => ?_
    simp only [mem_setOf_eq, hP] at hq ⊢
    rw [norm_xiSpectralPoint]
    show ‖xiZero q - 1 / 2‖ ≤ ‖xiZero q₁ - 1 / 2‖
    rw [hq]
  set N : ℝ := ∑' q : XiZeroCopy, if P q then (1 : ℝ) else 0 with hN
  have hNs : Summable fun q : XiZeroCopy => if P q then (1 : ℝ) else 0 := by
    refine summable_of_ne_finset_zero (s := hfib.toFinset) fun q hq => ?_
    rw [Set.Finite.mem_toFinset, mem_setOf_eq] at hq
    rw [if_neg hq]
  have hN1 : 1 ≤ N := by
    have h := hNs.le_tsum q₁ (fun j _ => by split_ifs <;> norm_num)
    simp only [hP, if_true] at h
    exact h
  have hfiber : ∑' q, (if P q then f q else 0) = (N : ℂ) * f q₁ := by
    have hcongr : ∀ q, (if P q then f q else 0) = ((if P q then (1 : ℝ) else 0 : ℝ) : ℂ) * f q₁ := by
      intro q
      by_cases hq : P q
      · rw [if_pos hq, if_pos hq, Complex.ofReal_one, one_mul]
        simp only [hf]
        rw [zeroBohrAmplitude_congr_xiZero hq, zeroLightConeExponent_eq_of_xiZero_eq hq]
      · rw [if_neg hq, if_neg hq, Complex.ofReal_zero, zero_mul]
    rw [tsum_congr hcongr, tsum_mul_right, hN, Complex.ofReal_tsum]
  have hs1 : Summable fun q => (if P q then f q else 0) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => by split_ifs <;> simp) hfs)
  have hs2 : Summable fun q => (if P q then 0 else f q) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => by split_ifs <;> simp) hfs)
  have hsum : ∑' q, f q = (∑' q, (if P q then f q else 0)) + ∑' q, (if P q then 0 else f q) := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr fun q => by split_ifs <;> simp
  have hrest : ‖∑' q, (if P q then 0 else f q)‖ ≤ A * Real.exp (ε * (M - g)) := by
    have hb : ∀ q, ‖(if P q then 0 else f q)‖ ≤ ‖zeroBohrAmplitude q‖ * Real.exp (ε * (M - g)) := by
      intro q
      by_cases hq : P q
      · rw [if_pos hq, norm_zero]; positivity
      · rw [if_neg hq, hnormf]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (hgap q hq) hε
    refine (norm_tsum_le_tsum_norm hs2.norm).trans ?_
    rw [hA, ← tsum_mul_right]
    exact Summable.tsum_le_tsum hb hs2.norm (hAs.mul_right _)
  have hfibnorm : ‖zeroBohrAmplitude q₁‖ * Real.exp (ε * M) ≤ ‖(N : ℂ) * f q₁‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hnormf]
    have : 0 ≤ ‖zeroBohrAmplitude q₁‖ * Real.exp (ε * M) := by positivity
    nlinarith
  have htri := norm_sub_norm_le ((N : ℂ) * f q₁) (-(∑' q, (if P q then 0 else f q)))
  rw [norm_neg, sub_neg_eq_add] at htri
  rw [hsum, hfiber]
  have hexp : Real.exp (ε * (M - g)) = Real.exp (ε * M) * Real.exp (-(ε * g)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp] at hrest
  nlinarith [Real.exp_pos (ε * M)]

/-- **Lower bound for the filtered zero series at a locally extremal zero.** -/
theorem norm_lightConeSeries_ge {q₀ : XiZeroCopy} {g : ℝ}
    (hgap : ∀ q : XiZeroCopy, xiZero q ≠ xiZero q₀ →
      -(zeroLightConeExponent ((xiZero q₀).im / 2) q).re ≤
        ((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8 - g)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Real.exp (ε * (((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8)) *
        (‖zeroBohrAmplitude q₀‖ - (∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖) * Real.exp (-(ε * g))) ≤
      ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent ((xiZero q₀).im / 2) q)‖ := by
  have h0 : -(zeroLightConeExponent ((xiZero q₀).im / 2) q₀).re =
      ((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8 := by
    rw [neg_re_zeroLightConeExponent_eq]; ring
  have h := norm_lightConeSeries_ge_of_dominant (q₁ := q₀)
    (fun q hq => (hgap q hq).trans_eq (by rw [h0])) hε
  rwa [h0] at h

/-- **Finite-range converse.**  For an off-line zero `ρ₀` that strictly maximizes `Re ρ` among zeros of
height within `4`, there are `g > 0` and an absolute `C` such that the central budget `|G| ≤ K` fails on
`(0, 4ε]` as soon as `ε ≥ 1`, `A e^{−εg} ≤ |c₀|/2` and `K + C < (|c₀|/2) e^{ε(δ₀ + δ₀²/8)}`. -/
theorem not_gaussianCentralGap_budget_of_localExtremalZero {q₀ : XiZeroCopy}
    (hoff : 1 / 2 < (xiZero q₀).re)
    (hloc : ∀ q : XiZeroCopy, xiZero q ≠ xiZero q₀ →
      |(xiZero q).im - (xiZero q₀).im| < 4 → (xiZero q).re < (xiZero q₀).re) :
    ∃ g C : ℝ, 0 < g ∧ 0 ≤ C ∧ ∀ K ε : ℝ, 0 ≤ K → 1 ≤ ε →
      (∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖) * Real.exp (-(ε * g)) ≤
        ‖zeroBohrAmplitude q₀‖ / 2 →
      K + C < ‖zeroBohrAmplitude q₀‖ / 2 *
        Real.exp (ε * (((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8)) →
      ¬ ∀ u ∈ Ioc (0 : ℝ) (4 * ε), |gaussianCentralGapLog u| ≤ K := by
  obtain ⟨g, hg, hgap⟩ := exists_lightCone_gap_of_localExtremalZero hoff hloc
  obtain ⟨C₀, hC₀, hexp⟩ := exists_norm_filteredGap_add_zeroSeries_le
  obtain ⟨C₁, hC₁, hC₁b⟩ := exists_abs_gaussianCentralGapLog_le_exp
  refine ⟨g, 2 * C₀ + 4 / 3 * C₁, hg, by positivity, fun K ε hK hε hsmall hbig hbud => ?_⟩
  have hε0 : 0 < ε := by linarith
  set τ₀ : ℝ := (xiZero q₀).im / 2 with hτ₀
  set Zs : ℂ := ∑' q : XiZeroCopy, zeroBohrAmplitude q *
    Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ₀ q) with hZs
  set s : ℝ := Real.sqrt (2 * Real.pi * ε) with hs
  have hs1 : 1 ≤ s := by
    rw [hs, Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  have hF := norm_filteredCentralGap_le_of_budget hC₁ hC₁b hε0 τ₀ hK hbud
  have he := hexp ε hε0 τ₀
  have hexp1 : Real.exp (-2 * ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  -- upper bound for the zero series
  have htri := norm_sub_le (gaussianFilteredCentralGap ε τ₀ + ((s : ℝ) : ℂ) * Zs)
    (gaussianFilteredCentralGap ε τ₀)
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at htri
  have hup : s * ‖Zs‖ ≤ s * (K + (2 * C₀ + 4 / 3 * C₁)) := by
    have h1 : s * ‖Zs‖ ≤ C₀ * (s + 1) + (K * s + 4 / 3 * C₁) := by
      have := mul_le_mul_of_nonneg_left hexp1 hC₀
      nlinarith
    nlinarith
  have hup' : ‖Zs‖ ≤ K + (2 * C₀ + 4 / 3 * C₁) := le_of_mul_le_mul_left hup (by linarith)
  -- lower bound
  have hlow := norm_lightConeSeries_ge hgap hε0.le
  have hpos : 0 < Real.exp (ε * (((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8)) :=
    Real.exp_pos _
  have hlow' : ‖zeroBohrAmplitude q₀‖ / 2 *
      Real.exp (ε * (((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8)) ≤ ‖Zs‖ := by
    refine le_trans ?_ hlow
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) hpos.le
  linarith

/-! ## Every off-line zero: breaking ties by moving the centre -/

/-- `Ψ(δ) = δ + δ²/8` is injective on `(−½, ½)`. -/
theorem lightCone_psi_injective {d d' : ℝ} (hd : -(1 / 2) < d ∧ d < 1 / 2)
    (hd' : -(1 / 2) < d' ∧ d' < 1 / 2) (h : d + d ^ 2 / 8 = d' + d' ^ 2 / 8) : d = d' := by
  have hfac : (d - d') * (1 + (d + d') / 8) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hfac with h1 | h1
  · linarith
  · exfalso; linarith [hd.1, hd'.1]

/-- Two parabolas `Ψ − (γ − 2τ)²/8` with distinct vertices cross at one centre only. -/
theorem lightCone_tie_eq {P P' c c' τ : ℝ} (hc : c ≠ c')
    (h : P - (c - 2 * τ) ^ 2 / 8 = P' - (c' - 2 * τ) ^ 2 / 8) :
    τ = (c + c') / 4 - 2 * (P - P') / (c - c') := by
  have hd : c - c' ≠ 0 := sub_ne_zero.2 hc
  field_simp
  linear_combination (8 : ℝ) * h

/-- **A dominant centre near every off-line zero.**  For an off-line zero `ρ₀` there are a centre `τ`
within `√Ψ₀/2` of `γ₀/2`, a zero `ρ₁` and a gap `g > 0` such that `ρ₁` alone carries the largest
light-cone exponent at `τ`, at least `Ψ₀/2`, and all other zeros lie at least `g` below it.  The
exponents are downward parabolas in `τ`; distinct zeros cross at most once, and the centre avoids the
finitely many crossings of the zeros near `ρ₀`. -/
theorem exists_dominant_lightCone_centre {q₀ : XiZeroCopy} (hoff : 1 / 2 < (xiZero q₀).re) :
    ∃ τ g : ℝ, ∃ q₁ : XiZeroCopy, 0 < g ∧
      (((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8) / 2 ≤
        -(zeroLightConeExponent τ q₁).re ∧
      ∀ q : XiZeroCopy, xiZero q ≠ xiZero q₁ →
        -(zeroLightConeExponent τ q).re ≤ -(zeroLightConeExponent τ q₁).re - g := by
  classical
  have hb₀ := re_xiZero_sub_half_bounds q₀
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb₀
  obtain ⟨Ψ₀, hΨ₀⟩ : ∃ Ψ₀ : ℝ,
      Ψ₀ = ((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8 := ⟨_, rfl⟩
  rw [← hΨ₀]
  have hΨ₀pos : 0 < Ψ₀ := by rw [hΨ₀]; nlinarith
  have hΨ₀lt : Ψ₀ < 1 := by rw [hΨ₀]; nlinarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt Ψ₀ / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 / 2 := by
    rw [hr]
    have : Real.sqrt Ψ₀ ≤ 1 := Real.sqrt_le_one.2 hΨ₀lt.le
    linarith
  have hr2 : (2 * r) ^ 2 = Ψ₀ := by
    rw [hr, show 2 * (Real.sqrt Ψ₀ / 2) = Real.sqrt Ψ₀ by ring, Real.sq_sqrt hΨ₀pos.le]
  have hfin := finite_xiZeroCopy_norm_le (‖xiZero q₀ - 1 / 2‖ + 6)
  obtain ⟨T, hT⟩ : ∃ T : Finset XiZeroCopy, T = hfin.toFinset := ⟨_, rfl⟩
  have hmemT : ∀ q, q ∈ T ↔ ‖xiZero q - 1 / 2‖ ≤ ‖xiZero q₀ - 1 / 2‖ + 6 := by
    intro q
    rw [hT, Set.Finite.mem_toFinset, mem_setOf_eq, norm_xiSpectralPoint]
    rfl
  have hq₀T : q₀ ∈ T := (hmemT q₀).2 (by linarith [norm_nonneg (xiZero q₀ - 1 / 2)])
  -- crossing points of the parabolas of `T`
  let Ψf : XiZeroCopy → ℝ := fun q => ((xiZero q).re - 1 / 2) + ((xiZero q).re - 1 / 2) ^ 2 / 8
  let tie : XiZeroCopy × XiZeroCopy → ℝ := fun p =>
    ((xiZero p.1).im + (xiZero p.2).im) / 4 - 2 * (Ψf p.1 - Ψf p.2) / ((xiZero p.1).im - (xiZero p.2).im)
  obtain ⟨τ, hτI, hτB⟩ := (Set.Icc_infinite (show (xiZero q₀).im / 2 < (xiZero q₀).im / 2 + r by
    linarith)).exists_notMem_finset ((T ×ˢ T).image tie)
  have hτ1 : (xiZero q₀).im / 2 ≤ τ := hτI.1
  have hτ2 : τ ≤ (xiZero q₀).im / 2 + r := hτI.2
  have hτnear : |2 * τ - (xiZero q₀).im| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  let E : XiZeroCopy → ℝ := fun q => -(zeroLightConeExponent τ q).re
  have hEq : ∀ q, E q = Ψf q - ((xiZero q).im - 2 * τ) ^ 2 / 8 := fun q =>
    neg_re_zeroLightConeExponent_eq_centre τ q
  obtain ⟨q₁, hq₁T, hmax⟩ := T.exists_max_image E ⟨q₀, hq₀T⟩
  have hE₀ : Ψ₀ / 2 ≤ E q₀ := by
    rw [hEq]
    have hd : ((xiZero q₀).im - 2 * τ) ^ 2 ≤ Ψ₀ := by
      rw [← hr2]
      have h1 : 0 ≤ 2 * τ - (xiZero q₀).im := by linarith
      have h2 : 2 * τ - (xiZero q₀).im ≤ 2 * r := by linarith
      nlinarith
    have : Ψf q₀ = Ψ₀ := hΨ₀.symm
    rw [this]
    nlinarith
  have hE₁ : Ψ₀ / 2 ≤ E q₁ := le_trans hE₀ (hmax q₀ hq₀T)
  have hfar : ∀ q : XiZeroCopy, q ∉ T → E q < 0 := fun q hq =>
    neg_re_zeroLightConeExponent_neg_of_far hτnear (by
      by_contra h; push Not at h; exact hq ((hmemT q).2 h))
  have hstrict : ∀ q ∈ T, xiZero q ≠ xiZero q₁ → E q < E q₁ := by
    intro q hqT hne
    refine lt_of_le_of_ne (hmax q hqT) fun heq => ?_
    rw [hEq, hEq] at heq
    by_cases him : (xiZero q).im = (xiZero q₁).im
    · rw [him] at heq
      have hb := re_xiZero_sub_half_bounds q
      have hb₁ := re_xiZero_sub_half_bounds q₁
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb hb₁
      have hd := lightCone_psi_injective hb hb₁ (by simp only [Ψf] at heq; linarith)
      exact hne (Complex.ext (by linarith) him)
    · exact hτB (Finset.mem_image.2 ⟨(q, q₁), Finset.mem_product.2 ⟨hqT, hq₁T⟩,
        (lightCone_tie_eq him heq).symm⟩)
  obtain ⟨g, hg, hgap⟩ := exists_uniform_gap_of_finite T (fun q => xiZero q = xiZero q₁) E
    (by linarith) hstrict hfar
  exact ⟨τ, g, q₁, hg, hE₁, hgap⟩

/-- **Finite-range converse for every off-line zero.**  If `ξ` has a zero `ρ₀` with `Re ρ₀ > ½`, there
are a centre `τ`, a zero `ρ₁`, a gap `g > 0` and an absolute `C` such that, with
`M = −Re w_{ρ₁}(τ) ≥ (δ₀ + δ₀²/8)/2`, the bound `|G| ≤ K` fails on `(0, 4ε]` whenever `ε ≥ 1`,
`A e^{−εg} ≤ |c₁|/2` and `K + C < (|c₁|/2) e^{εM}`. -/
theorem not_gaussianCentralGap_budget_of_offLineZero {q₀ : XiZeroCopy}
    (hoff : 1 / 2 < (xiZero q₀).re) :
    ∃ τ g C : ℝ, ∃ q₁ : XiZeroCopy, 0 < g ∧ 0 ≤ C ∧
      (((xiZero q₀).re - 1 / 2) + ((xiZero q₀).re - 1 / 2) ^ 2 / 8) / 2 ≤
        -(zeroLightConeExponent τ q₁).re ∧
      ∀ K ε : ℝ, 0 ≤ K → 1 ≤ ε →
      (∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖) * Real.exp (-(ε * g)) ≤
        ‖zeroBohrAmplitude q₁‖ / 2 →
      K + C < ‖zeroBohrAmplitude q₁‖ / 2 * Real.exp (ε * -(zeroLightConeExponent τ q₁).re) →
      ¬ ∀ u ∈ Ioc (0 : ℝ) (4 * ε), |gaussianCentralGapLog u| ≤ K := by
  obtain ⟨τ, g, q₁, hg, hM, hgap⟩ := exists_dominant_lightCone_centre hoff
  obtain ⟨C₀, hC₀, hexp⟩ := exists_norm_filteredGap_add_zeroSeries_le
  obtain ⟨C₁, hC₁, hC₁b⟩ := exists_abs_gaussianCentralGapLog_le_exp
  refine ⟨τ, g, 2 * C₀ + 4 / 3 * C₁, q₁, hg, by positivity, hM,
    fun K ε hK hε hsmall hbig hbud => ?_⟩
  have hε0 : 0 < ε := by linarith
  set Zs : ℂ := ∑' q : XiZeroCopy, zeroBohrAmplitude q *
    Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q) with hZs
  set s : ℝ := Real.sqrt (2 * Real.pi * ε) with hs
  have hs1 : 1 ≤ s := by
    rw [hs, Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  have hF := norm_filteredCentralGap_le_of_budget hC₁ hC₁b hε0 τ hK hbud
  have he := hexp ε hε0 τ
  have hexp1 : Real.exp (-2 * ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have htri := norm_sub_le (gaussianFilteredCentralGap ε τ + ((s : ℝ) : ℂ) * Zs)
    (gaussianFilteredCentralGap ε τ)
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at htri
  have hup : s * ‖Zs‖ ≤ s * (K + (2 * C₀ + 4 / 3 * C₁)) := by
    have h1 : s * ‖Zs‖ ≤ C₀ * (s + 1) + (K * s + 4 / 3 * C₁) := by
      have := mul_le_mul_of_nonneg_left hexp1 hC₀
      nlinarith
    nlinarith
  have hup' : ‖Zs‖ ≤ K + (2 * C₀ + 4 / 3 * C₁) := le_of_mul_le_mul_left hup (by linarith)
  have hlow := norm_lightConeSeries_ge_of_dominant hgap hε0.le
  have hpos : 0 < Real.exp (ε * -(zeroLightConeExponent τ q₁).re) := Real.exp_pos _
  have hlow' : ‖zeroBohrAmplitude q₁‖ / 2 * Real.exp (ε * -(zeroLightConeExponent τ q₁).re) ≤
      ‖Zs‖ := by
    refine le_trans ?_ hlow
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) hpos.le
  linarith

end

end RHTower
