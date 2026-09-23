import GaloisForLFunctions.RHTower.XiMassShellBesselRemainder

/-!
# The shell ratio

The exact leading term of the mass profile on a spacelike shell differs from its pure rapidity
model by the single ratio

`R = (τ/(iu)) · e^{-a(z−ζ)} · (q u)^{3/2}/(z √z)`,

a product of three factors each within `O(1/u)` of `1`: the first because `τ − iu = σ`, the second
by the window bound on `z − ζ`, the third because `z/(qu)` is a near-unit and both `w ↦ w√w` and
inversion preserve that.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The propagation radius of the shell. -/
def shellRoot (sigma kappa u s : ℝ) : ℂ :=
  HTGeometry.csqrt (xiMassShellArgument sigma kappa u s)

theorem shellRoot_re_ge {sigma kappa u s : ℝ} (hkappa : 1 < kappa) (hu : 0 < u) (hs : 0 ≤ s)
    (hsigma : 0 < sigma) : shellQ kappa * u ≤ (shellRoot sigma kappa u s).re := by
  rw [shellRoot, HTGeometry.csqrt_re]
  exact csqrt_shellArgument_re_ge hkappa hu hs hsigma

theorem shellRoot_re_pos {sigma kappa u s : ℝ} (hkappa : 1 < kappa) (hu : 0 < u) (hs : 0 ≤ s)
    (hsigma : 0 < sigma) : 0 < (shellRoot sigma kappa u s).re :=
  lt_of_lt_of_le (mul_pos (shellQ_pos hkappa) hu) (shellRoot_re_ge hkappa hu hs hsigma)

theorem shellRoot_ne_zero {sigma kappa u s : ℝ} (hkappa : 1 < kappa) (hu : 0 < u) (hs : 0 ≤ s)
    (hsigma : 0 < sigma) : shellRoot sigma kappa u s ≠ 0 := by
  intro h
  have := shellRoot_re_pos hkappa hu hs hsigma
  rw [h] at this
  simp at this

/-- The exact ratio between the shell leading term and its rapidity model. -/
def shellRatio (a sigma kappa u s : ℝ) : ℂ :=
  (((sigma : ℂ) + (u : ℂ) * I) / ((u : ℂ) * I))
    * Complex.exp (-((a : ℂ) * (shellRoot sigma kappa u s - xiMassShellRadius sigma kappa u s)))
    * ((((shellQ kappa * u : ℝ) : ℂ) * ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ))
        / (shellRoot sigma kappa u s * HTGeometry.csqrt (shellRoot sigma kappa u s)))

/-- **The exact factorization of the shell leading term.** -/
theorem shellLeading_eq_model_mul_ratio {a sigma kappa u s : ℝ} (hkappa : 1 < kappa) (hu : 0 < u)
    (hs : 0 ≤ s) (hsigma : 0 < sigma) :
    ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * ((sigma : ℂ) + (u : ℂ) * I)
        * Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s))
        / (shellRoot sigma kappa u s * HTGeometry.csqrt (shellRoot sigma kappa u s))
      = (((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * ((u : ℂ) * I)
          * Complex.exp (-((a : ℂ) * xiMassShellRadius sigma kappa u s))
          / (((shellQ kappa * u : ℝ) : ℂ) * ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ)))
        * shellRatio a sigma kappa u s := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hqu : (0 : ℝ) < shellQ kappa * u := mul_pos hq hu
  have hroot : (0 : ℝ) < Real.sqrt (shellQ kappa * u) := Real.sqrt_pos.2 hqu
  have hquC : ((shellQ kappa * u : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hqu
  have hrootC : ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hroot
  have hZne : shellRoot sigma kappa u s ≠ 0 := shellRoot_ne_zero hkappa hu hs hsigma
  have hZre : 0 < (shellRoot sigma kappa u s).re := shellRoot_re_pos hkappa hu hs hsigma
  have hcsne : HTGeometry.csqrt (shellRoot sigma kappa u s) ≠ 0 :=
    HTGeometry.csqrt_ne_zero hZre
  have huC : ((u : ℂ)) ≠ 0 := by simpa using ne_of_gt hu
  have hIne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hexp : Complex.exp (-((a : ℂ) * xiMassShellRadius sigma kappa u s))
      * Complex.exp (-((a : ℂ) * (shellRoot sigma kappa u s
        - xiMassShellRadius sigma kappa u s)))
      = Complex.exp (-((a : ℂ) * shellRoot sigma kappa u s)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have key : (((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * ((u : ℂ) * I)
        * Complex.exp (-((a : ℂ) * xiMassShellRadius sigma kappa u s))
        / (((shellQ kappa * u : ℝ) : ℂ) * ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ)))
      * shellRatio a sigma kappa u s
      = ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * ((sigma : ℂ) + (u : ℂ) * I)
        * (Complex.exp (-((a : ℂ) * xiMassShellRadius sigma kappa u s))
          * Complex.exp (-((a : ℂ) * (shellRoot sigma kappa u s
            - xiMassShellRadius sigma kappa u s))))
        / (shellRoot sigma kappa u s * HTGeometry.csqrt (shellRoot sigma kappa u s)) := by
    rw [shellRatio]
    field_simp
  rw [key, hexp]


/-! ## The ratio is a near-unit -/

theorem norm_shellBoost_sub_one {sigma u : ℝ} (hsigma : 0 < sigma) (hu : 0 < u) :
    ‖((sigma : ℂ) + (u : ℂ) * I) / ((u : ℂ) * I) - 1‖ = sigma / u := by
  have huC : ((u : ℂ)) ≠ 0 := by simpa using ne_of_gt hu
  have hden : ((u : ℂ)) * I ≠ 0 := mul_ne_zero huC Complex.I_ne_zero
  have hval : ((sigma : ℂ) + (u : ℂ) * I) / ((u : ℂ) * I) - 1
      = (sigma : ℂ) / ((u : ℂ) * I) := by
    field_simp
    ring
  rw [hval, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsigma, abs_of_pos hu]

theorem shellAmplitude_ratio_eq {sigma kappa u s : ℝ} (hkappa : 1 < kappa) (hu : 0 < u)
    (hs : 0 ≤ s) (hsigma : 0 < sigma) :
    (((shellQ kappa * u : ℝ) : ℂ) * ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ))
        / (shellRoot sigma kappa u s * HTGeometry.csqrt (shellRoot sigma kappa u s))
      = ((shellRoot sigma kappa u s / ((shellQ kappa * u : ℝ) : ℂ))
          * HTGeometry.csqrt (shellRoot sigma kappa u s / ((shellQ kappa * u : ℝ) : ℂ)))⁻¹ := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hqu : (0 : ℝ) < shellQ kappa * u := mul_pos hq hu
  have hquC : ((shellQ kappa * u : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hqu
  have hZre : 0 < (shellRoot sigma kappa u s).re := shellRoot_re_pos hkappa hu hs hsigma
  set W : ℂ := shellRoot sigma kappa u s / ((shellQ kappa * u : ℝ) : ℂ) with hW
  have hWre : 0 < W.re := by
    rw [hW, Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, add_zero]
    have hns : 0 < Complex.normSq (((shellQ kappa * u : ℝ) : ℂ)) := by
      simpa using Complex.normSq_pos.2 hquC
    positivity
  have hZeq : shellRoot sigma kappa u s = ((shellQ kappa * u : ℝ) : ℂ) * W := by
    rw [hW]
    field_simp
  have hfac : shellRoot sigma kappa u s * HTGeometry.csqrt (shellRoot sigma kappa u s)
      = ((shellQ kappa * u : ℝ) : ℂ) * ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ)
        * (W * HTGeometry.csqrt W) := by
    rw [hZeq]
    exact mul_csqrt_ofReal_mul hqu hWre
  have hWne : W ≠ 0 := by
    intro h
    rw [h] at hWre
    simp at hWre
  have hcsWne : HTGeometry.csqrt W ≠ 0 := HTGeometry.csqrt_ne_zero hWre
  have hrootC : ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt (Real.sqrt_pos.2 hqu)
  rw [hfac]
  field_simp

/-- The exponential factor of the shell ratio is a near-unit. -/
theorem norm_shellExpFactor_sub_one_le {a sigma kappa u s L D q : ℝ} (ha : 0 < a)
    (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hqdef : shellQ kappa = q)
    (hDdef : sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + (kappa * L + sigma) ^ (2 : ℕ) / shellQ kappa ^ (2 : ℕ) = D)
    (hu0 : 0 < u) (hs : 0 ≤ s) (hsL : s ≤ L) (hsmall : a * D / (q * u) ≤ 1) :
    ‖Complex.exp (-((a : ℂ) * (shellRoot sigma kappa u s
      - xiMassShellRadius sigma kappa u s))) - 1‖ ≤ a * D / (q * u) := by
  have hq : 0 < q := hqdef ▸ shellQ_pos hkappa
  have hqu : (0 : ℝ) < q * u := mul_pos hq hu0
  have hstep := norm_csqrt_shellArgument_sub_shellRadius_le hkappa hu0 hs hsigma
  have hdef := norm_xiMassShellDefect_le hkappa hs hsL hsigma.le
  rw [hDdef] at hdef
  have hqroot : Real.sqrt (kappa ^ (2 : ℕ) - 1) = q := by rw [← hqdef, shellQ]
  rw [hqroot] at hstep
  have hZζ : ‖shellRoot sigma kappa u s - xiMassShellRadius sigma kappa u s‖
      ≤ D / (2 * q * u) := by
    rw [shellRoot]
    refine le_trans hstep ?_
    have hpos : (0 : ℝ) < 2 * q * u := by positivity
    exact div_le_div_of_nonneg_right hdef hpos.le
  have hax : ‖-((a : ℂ) * (shellRoot sigma kappa u s - xiMassShellRadius sigma kappa u s))‖
      = a * ‖shellRoot sigma kappa u s - xiMassShellRadius sigma kappa u s‖ := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hhalf : a * (D / (2 * q * u)) = a * D / (q * u) / 2 := by
    field_simp
  have haxle : ‖-((a : ℂ) * (shellRoot sigma kappa u s - xiMassShellRadius sigma kappa u s))‖
      ≤ a * D / (q * u) / 2 := by
    rw [hax, ← hhalf]
    exact mul_le_mul_of_nonneg_left hZζ ha.le
  have hle1 : ‖-((a : ℂ) * (shellRoot sigma kappa u s
      - xiMassShellRadius sigma kappa u s))‖ ≤ 1 := by
    refine le_trans haxle ?_
    linarith
  have hexp := Complex.norm_exp_sub_one_le hle1
  linarith [hexp, haxle]

/-- The amplitude factor of the shell ratio is a near-unit. -/
theorem norm_shellAmplitudeFactor_sub_one_le {sigma kappa u s L B q : ℝ}
    (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hqdef : shellQ kappa = q)
    (hBdef : shellRadiusBound sigma kappa L = B) (hu1 : 1 ≤ u) (hs : 0 ≤ s) (hsL : s ≤ L)
    (hsmall : B / (q * u) ≤ 1 / 5) :
    ‖(((shellQ kappa * u : ℝ) : ℂ) * ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ))
      / (shellRoot sigma kappa u s * HTGeometry.csqrt (shellRoot sigma kappa u s)) - 1‖
      ≤ 5 * (B / (q * u)) := by
  have hq : 0 < q := hqdef ▸ shellQ_pos hkappa
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have hqu : (0 : ℝ) < q * u := mul_pos hq hu0
  have hnn : (0 : ℝ) ≤ B / (q * u) := by
    have hB0 : 0 ≤ B := hBdef ▸ shellRadiusBound_nonneg hkappa hsigma.le (le_trans hs hsL)
    positivity
  have hquC : ((q * u : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hqu
  have hZre : 0 < (shellRoot sigma kappa u s).re := shellRoot_re_pos hkappa hu0 hs hsigma
  have hWre : 0 < (shellRoot sigma kappa u s / ((q * u : ℝ) : ℂ)).re := by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, add_zero]
    have hns : 0 < Complex.normSq (((q * u : ℝ) : ℂ)) := by
      simpa using Complex.normSq_pos.2 hquC
    positivity
  have hWbound : ‖shellRoot sigma kappa u s / ((q * u : ℝ) : ℂ) - 1‖ ≤ B / (q * u) := by
    have hmain := norm_shellRadius_ratio_sub_one_le hkappa hu1 hs hsL hsigma
    rw [hqdef, hBdef] at hmain
    rw [shellRoot]
    exact hmain
  have hmulW : ‖(shellRoot sigma kappa u s / ((q * u : ℝ) : ℂ))
      * HTGeometry.csqrt (shellRoot sigma kappa u s / ((q * u : ℝ) : ℂ)) - 1‖
      ≤ (2 + B / (q * u)) * (B / (q * u)) := by
    refine le_trans (HTGeometry.norm_mul_csqrt_sub_one_le hWre) ?_
    have hw0 : (0 : ℝ) ≤ ‖shellRoot sigma kappa u s / ((q * u : ℝ) : ℂ) - 1‖ := norm_nonneg _
    nlinarith [hWbound, hnn, hw0, mul_le_mul hWbound hWbound hw0 hnn]
  have hsq : (B / (q * u)) * (B / (q * u)) ≤ (1 / 5) * (1 / 5) :=
    mul_le_mul hsmall hsmall hnn (by norm_num)
  have hγbound : (2 + B / (q * u)) * (B / (q * u)) ≤ 1 / 2 := by
    have hexpand : (2 + B / (q * u)) * (B / (q * u))
        = 2 * (B / (q * u)) + (B / (q * u)) * (B / (q * u)) := by ring
    rw [hexpand]
    linarith [hsmall, hsq]
  rw [shellAmplitude_ratio_eq hkappa hu0 hs hsigma, hqdef]
  have hinv := HTGeometry.norm_inv_sub_one_le
    (W := (shellRoot sigma kappa u s / ((q * u : ℝ) : ℂ))
      * HTGeometry.csqrt (shellRoot sigma kappa u s / ((q * u : ℝ) : ℂ)))
    hmulW hγbound
  refine le_trans hinv ?_
  nlinarith [hsmall, hnn]

/-- **The shell ratio is within `O(1/u)` of one.** -/
theorem exists_shellRatio_bound {a sigma kappa L : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (hkappa : 1 < kappa) (hL : 0 ≤ L) :
    ∃ C u₀ : ℝ, 0 < C ∧ 1 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ s : ℝ, 0 ≤ s → s ≤ L →
      ‖shellRatio a sigma kappa u s - 1‖ ≤ C / u := by
  classical
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, shellQ kappa = q := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ,
      sigma ^ (2 : ℕ) + L ^ (2 : ℕ) + (kappa * L + sigma) ^ (2 : ℕ) / shellQ kappa ^ (2 : ℕ) = D := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, shellRadiusBound sigma kappa L = B := ⟨_, rfl⟩
  have hq : 0 < q := hqdef ▸ shellQ_pos hkappa
  have hD0 : 0 ≤ D := by
    rw [← hDdef]
    have hdiv := div_nonneg (sq_nonneg (kappa * L + sigma)) (sq_nonneg (shellQ kappa))
    nlinarith [sq_nonneg sigma, sq_nonneg L]
  have hB0 : 0 ≤ B := hBdef ▸ shellRadiusBound_nonneg hkappa hsigma.le hL
  refine ⟨4 * sigma + 2 * (a * D / q) + 5 * (B / q) + 1,
    1 + sigma + a * D / q + 5 * (B / q), by positivity, by
      have : (0 : ℝ) ≤ sigma + a * D / q + 5 * (B / q) := by positivity
      linarith, fun u hu s hs hsL => ?_⟩
  have hu1 : (1 : ℝ) ≤ u := by
    have : (0 : ℝ) ≤ sigma + a * D / q + 5 * (B / q) := by positivity
    linarith
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have hqu : (0 : ℝ) < q * u := mul_pos hq hu0
  have hBq0 : (0 : ℝ) ≤ B / q := by positivity
  have hADq0 : (0 : ℝ) ≤ a * D / q := by positivity
  have hβ : a * D / (q * u) ≤ 1 := by
    have hADq : a * D / q ≤ u := by linarith [hsigma.le, hBq0]
    rw [div_le_iff₀ hq] at hADq
    rw [div_le_one hqu]
    calc a * D ≤ u * q := hADq
      _ = q * u := by ring
  have hWsmall : B / (q * u) ≤ 1 / 5 := by
    have hBq : 5 * (B / q) ≤ u := by linarith [hsigma.le, hADq0]
    have hstep : B / q ≤ u / 5 := by linarith
    rw [div_le_iff₀ hq] at hstep
    rw [div_le_div_iff₀ hqu (by norm_num : (0 : ℝ) < 5)]
    calc B * 5 ≤ (u / 5 * q) * 5 := by linarith [hstep]
      _ = 1 * (q * u) := by ring
  have hF1 : ‖((sigma : ℂ) + (u : ℂ) * I) / ((u : ℂ) * I) - 1‖ = sigma / u :=
    norm_shellBoost_sub_one hsigma hu0
  have hF2 := norm_shellExpFactor_sub_one_le (L := L) ha hsigma hkappa hqdef hDdef hu0 hs hsL hβ
  have hF3 := norm_shellAmplitudeFactor_sub_one_le (L := L) hsigma hkappa hqdef hBdef hu1 hs hsL
    hWsmall
  have hγ1 : 5 * (B / (q * u)) ≤ 1 := by
    have hnn : (0 : ℝ) ≤ B / (q * u) := by positivity
    linarith [hWsmall]
  have hcomb := HTGeometry.norm_mul3_sub_one_le
    (A := ((sigma : ℂ) + (u : ℂ) * I) / ((u : ℂ) * I))
    (B := Complex.exp (-((a : ℂ) * (shellRoot sigma kappa u s
      - xiMassShellRadius sigma kappa u s))))
    (C := (((shellQ kappa * u : ℝ) : ℂ) * ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ))
      / (shellRoot sigma kappa u s * HTGeometry.csqrt (shellRoot sigma kappa u s)))
    (le_of_eq hF1) hF2 hF3 hβ hγ1
  rw [shellRatio]
  refine le_trans hcomb ?_
  have e1 : a * D / (q * u) = (a * D / q) / u := by field_simp
  have e2 : B / (q * u) = (B / q) / u := by field_simp
  rw [e1, e2]
  have hfinal : 4 * (sigma / u) + 2 * (a * D / q / u) + 5 * (B / q / u)
      = (4 * sigma + 2 * (a * D / q) + 5 * (B / q)) / u := by
    field_simp
  rw [hfinal, div_le_div_iff₀ hu0 hu0]
  nlinarith [hu0]

end

end RHTower
