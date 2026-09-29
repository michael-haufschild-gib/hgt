import Mathlib

/-!
# Short bumps, their Mellin transforms, and smoothed Dirichlet sums

Tools for detecting the support of a weight system `lam : ℕ → ℝ` in short intervals through its
Dirichlet series `D(s) = Σ lam(n) n^{-s}`.

* `norm_sub_le_of_re_nonneg_on_ball`: the Harnack bound for holomorphic functions of nonnegative
  real part on a disc (Schwarz lemma applied to a Cayley transform).
* `shortBump δ`: a smooth bump `φ_δ(u) = ψ((u − 1)/δ)` supported in `(1, 1 + δ)`, with
  `∫ φ_δ ≥ δ/4` (`integral_shortBump_ge`).
* Its Mellin transform satisfies the Lorentzian bound `‖𝓜φ_δ(σ + it)‖ ≤ C δ/(1 + δ²t²)` on
  `0 < σ ≤ 2` (`norm_mellin_shortBump_le_lorentz`), by two integrations by parts.
* Mellin inversion gives `Σ lam(n) φ_δ(n/x) = (1/2π) ∫ x^{2+iy} 𝓜φ_δ(2+iy) D(2+iy) dy`
  (`tsum_mul_shortBump_eq_integral`).  The pole `1/(s − 1)` contributes exactly `x ∫ φ_δ`
  (`integral_shortBump_eq_pole_integral`), by Fubini against `∫_{u>1} u^{-s} du = 1/(s − 1)`.
* `integral_lorentz_rpow_le`: `∫ δ/(1 + δ²y²) (|y| + 3)^κ dy ≤ δ^{-κ} · lorentzHalfConst`.
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- **Harnack bound for positive real part.**  A holomorphic function of nonnegative real part on
a disc moves, off the centre, by at most `2‖z − c‖/(R − ‖z − c‖)` times its real part at the
centre.  Proof: the Cayley transform of `f + ε` maps the disc into the closed unit disc and fixes
the centre at `0`, so the Schwarz lemma applies; then `ε → 0`. -/
theorem norm_sub_le_of_re_nonneg_on_ball {f : ℂ → ℂ} {c z : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hre : ∀ w ∈ ball c R, 0 ≤ (f w).re)
    (hz : z ∈ ball c R) :
    ‖f z - f c‖ ≤ 2 * ‖z - c‖ / (R - ‖z - c‖) * (f c).re := by
  have hr : ‖z - c‖ < R := mem_ball_iff_norm.mp hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hr
  have hRr : 0 < R - ‖z - c‖ := by linarith
  have key : ∀ ε : ℝ, 0 < ε → ‖f z - f c‖ ≤ 2 * ‖z - c‖ / (R - ‖z - c‖) * ((f c).re + ε) := by
    intro ε hε
    set g : ℂ → ℂ := fun w => f w + ε with hg
    have hgre : ∀ w ∈ ball c R, ε ≤ (g w).re := by
      intro w hw; simp only [hg, add_re, ofReal_re]; linarith [hre w hw]
    have hden : ∀ w ∈ ball c R, g w + (starRingEnd ℂ) (g c) ≠ 0 := by
      intro w hw h0
      have := congrArg re h0
      simp only [add_re, conj_re, zero_re] at this
      linarith [hgre w hw, hgre c (mem_ball_self hR)]
    set φ : ℂ → ℂ := fun w => (g w - g c) / (g w + (starRingEnd ℂ) (g c)) with hφ
    have hφc : φ c = 0 := by simp [hφ]
    have hgd : DifferentiableOn ℂ g (ball c R) := hf.add (differentiableOn_const _)
    have hφd : DifferentiableOn ℂ φ (ball c R) :=
      (hgd.sub (differentiableOn_const _)).div (hgd.add (differentiableOn_const _)) hden
    have hmaps : MapsTo φ (ball c R) (closedBall (φ c) 1) := by
      intro w hw
      rw [hφc, mem_closedBall, dist_zero_right, hφ]
      simp only
      rw [norm_div, div_le_one (norm_pos_iff.mpr (hden w hw))]
      have h1 : ‖g w - g c‖ ^ 2 = (g w - g c).re ^ 2 + (g w - g c).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have h2 : ‖g w + (starRingEnd ℂ) (g c)‖ ^ 2 =
          (g w + (starRingEnd ℂ) (g c)).re ^ 2 + (g w + (starRingEnd ℂ) (g c)).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have hle : ‖g w - g c‖ ^ 2 ≤ ‖g w + (starRingEnd ℂ) (g c)‖ ^ 2 := by
        rw [h1, h2]
        simp only [sub_re, sub_im, add_re, add_im, conj_re, conj_im]
        nlinarith [hgre w hw, hgre c (mem_ball_self hR)]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle
    rcases eq_or_ne z c with rfl | hzc
    · simp
    have hd := Complex.norm_dslope_le_div_of_mapsTo_ball hφd hmaps hz
    rw [dslope_of_ne _ hzc, slope_def_field, hφc, sub_zero, norm_div] at hd
    have hzc' : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
    have hφz : ‖φ z‖ ≤ ‖z - c‖ / R := by
      rw [div_le_div_iff₀ hzc' hR] at hd
      rw [le_div_iff₀ hR]
      linarith
    have hgz : g z - g c = f z - f c := by simp [hg]
    have hsum : ‖g z + (starRingEnd ℂ) (g c)‖ ≤ ‖f z - f c‖ + 2 * ((f c).re + ε) := by
      have : g z + (starRingEnd ℂ) (g c) = (f z - f c) + ((g c) + (starRingEnd ℂ) (g c)) := by
        simp [hg]; ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      gcongr
      have hgc : (g c).re = (f c).re + ε := by simp [hg]
      rw [Complex.add_conj, hgc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hre c (mem_ball_self hR)])]
    have hφeq : ‖φ z‖ * ‖g z + (starRingEnd ℂ) (g c)‖ = ‖f z - f c‖ := by
      rw [hφ]; simp only
      rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hden z hz)), hgz]
    have hmain : ‖f z - f c‖ ≤ ‖z - c‖ / R * (‖f z - f c‖ + 2 * ((f c).re + ε)) := by
      calc ‖f z - f c‖ = ‖φ z‖ * ‖g z + (starRingEnd ℂ) (g c)‖ := hφeq.symm
        _ ≤ ‖z - c‖ / R * (‖f z - f c‖ + 2 * ((f c).re + ε)) :=
          mul_le_mul hφz hsum (norm_nonneg _) (by positivity)
    rw [div_mul_eq_mul_div, le_div_iff₀ hR] at hmain
    rw [div_mul_eq_mul_div, le_div_iff₀ hRr]
    nlinarith
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set k : ℝ := 2 * ‖z - c‖ / (R - ‖z - c‖)
  have hk : 0 ≤ k := by positivity
  have := key (δ / (k + 1)) (by positivity)
  calc ‖f z - f c‖ ≤ k * ((f c).re + δ / (k + 1)) := this
    _ = k * (f c).re + δ * (k / (k + 1)) := by ring
    _ < k * (f c).re + δ := by
        have : k / (k + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
        nlinarith

theorem one_lt_log_abs_add_three (t : ℝ) : 1 < Real.log (|t| + 3) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have := Real.exp_one_lt_d9
  have : (0 : ℝ) ≤ |t| := abs_nonneg t
  linarith

/-- The bump profile `ψ`: smooth, with values in `[0,1]`, supported in `(1/4, 3/4)`, and equal to
`1` on `[3/8, 5/8]`. -/
noncomputable def shortBumpProfile : ℝ → ℝ :=
  ⇑(⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩ : ContDiffBump (1 / 2 : ℝ))

theorem shortBumpProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) shortBumpProfile :=
  ContDiffBump.contDiff _

theorem shortBumpProfile_nonneg (v : ℝ) : 0 ≤ shortBumpProfile v := ContDiffBump.nonneg _

theorem shortBumpProfile_le_one (v : ℝ) : shortBumpProfile v ≤ 1 := ContDiffBump.le_one _

theorem support_shortBumpProfile : Function.support shortBumpProfile = Ioo (1 / 4) (3 / 4) := by
  rw [shortBumpProfile, ContDiffBump.support_eq, Real.ball_eq_Ioo]
  norm_num

theorem tsupport_shortBumpProfile : tsupport shortBumpProfile = Icc (1 / 4) (3 / 4) := by
  rw [tsupport, shortBumpProfile, ContDiffBump.support_eq, closure_ball _ (by norm_num),
    Real.closedBall_eq_Icc]
  norm_num

theorem shortBumpProfile_eq_one {v : ℝ} (hv : v ∈ Icc (3 / 8) (5 / 8)) : shortBumpProfile v = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Real.closedBall_eq_Icc]
  convert hv using 2 <;> norm_num

theorem shortBumpProfile_eq_zero {v : ℝ} (hv : v ∉ Ioo (1 / 4) (3 / 4)) : shortBumpProfile v = 0 := by
  rw [← support_shortBumpProfile] at hv
  simpa using hv

theorem deriv_shortBumpProfile_eq_zero {v : ℝ} (hv : v ∉ Icc (1 / 4) (3 / 4)) :
    deriv shortBumpProfile v = 0 := by
  by_contra h
  exact hv (tsupport_shortBumpProfile ▸ support_deriv_subset (Function.mem_support.mpr h))

theorem deriv_deriv_shortBumpProfile_eq_zero {v : ℝ} (hv : v ∉ Icc (1 / 4) (3 / 4)) :
    deriv (deriv shortBumpProfile) v = 0 := by
  by_contra h
  exact hv (tsupport_shortBumpProfile ▸ tsupport_deriv_subset
    (support_deriv_subset (Function.mem_support.mpr h)))

theorem contDiff_deriv_shortBumpProfile : ContDiff ℝ (⊤ : ℕ∞) (deriv shortBumpProfile) :=
  (contDiff_infty_iff_deriv.mp shortBumpProfile_contDiff).2

theorem hasDerivAt_shortBumpProfile (v : ℝ) :
    HasDerivAt shortBumpProfile (deriv shortBumpProfile v) v :=
  ((shortBumpProfile_contDiff.differentiable (by simp)) v).hasDerivAt

theorem hasDerivAt_deriv_shortBumpProfile (v : ℝ) :
    HasDerivAt (deriv shortBumpProfile) (deriv (deriv shortBumpProfile) v) v :=
  ((contDiff_deriv_shortBumpProfile.differentiable (by simp)) v).hasDerivAt

theorem continuous_deriv_deriv_shortBumpProfile : Continuous (deriv (deriv shortBumpProfile)) :=
  contDiff_deriv_shortBumpProfile.continuous_deriv (by simp)

theorem exists_bound_deriv_deriv_shortBumpProfile :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v, |deriv (deriv shortBumpProfile) v| ≤ M := by
  have hcs : HasCompactSupport (deriv (deriv shortBumpProfile)) := by
    have : HasCompactSupport shortBumpProfile :=
      ContDiffBump.hasCompactSupport _
    exact this.deriv.deriv
  obtain ⟨C, hC⟩ := continuous_deriv_deriv_shortBumpProfile.bounded_above_of_compact_support hcs
  exact ⟨max C 0, le_max_right _ _, fun v => (by simpa using hC v : _ ≤ C).trans (le_max_left _ _)⟩

/-- The rescaled bump `φ_δ(u) = ψ((u − 1)/δ)`, supported in `(1 + δ/4, 1 + 3δ/4)`. -/
noncomputable def shortBump (δ u : ℝ) : ℝ := shortBumpProfile ((u - 1) / δ)

theorem shortBump_nonneg (δ u : ℝ) : 0 ≤ shortBump δ u := shortBumpProfile_nonneg _

theorem shortBump_le_one (δ u : ℝ) : shortBump δ u ≤ 1 := shortBumpProfile_le_one _

theorem shortBump_eq_zero {δ u : ℝ} (hδ : 0 < δ) (hu : u ∉ Ioo 1 (1 + δ)) : shortBump δ u = 0 := by
  apply shortBumpProfile_eq_zero
  intro h
  apply hu
  rcases h with ⟨h1, h2⟩
  constructor
  · have : 0 < (u - 1) / δ := by linarith
    have := (div_pos_iff_of_pos_right hδ).mp this
    linarith
  · rw [div_lt_iff₀ hδ] at h2
    linarith

theorem shortBump_eq_one {δ u : ℝ} (hδ : 0 < δ) (hu : u ∈ Icc (1 + 3 * δ / 8) (1 + 5 * δ / 8)) :
    shortBump δ u = 1 := by
  apply shortBumpProfile_eq_one
  rcases hu with ⟨h1, h2⟩
  constructor
  · rw [le_div_iff₀ hδ]; linarith
  · rw [div_le_iff₀ hδ]; linarith

theorem continuous_shortBump (δ : ℝ) : Continuous (shortBump δ) :=
  shortBumpProfile_contDiff.continuous.comp (by fun_prop)

theorem hasDerivAt_shortBump (δ u : ℝ) :
    HasDerivAt (shortBump δ) (deriv shortBumpProfile ((u - 1) / δ) / δ) u := by
  have hin : HasDerivAt (fun u : ℝ => (u - 1) / δ) (1 / δ) u :=
    ((hasDerivAt_id u).sub_const 1).div_const δ
  have := (hasDerivAt_shortBumpProfile ((u - 1) / δ)).comp u hin
  exact this.congr_deriv (by ring)

theorem hasDerivAt_deriv_shortBump (δ u : ℝ) :
    HasDerivAt (fun u => deriv shortBumpProfile ((u - 1) / δ) / δ)
      (deriv (deriv shortBumpProfile) ((u - 1) / δ) / δ ^ 2) u := by
  have hin : HasDerivAt (fun u : ℝ => (u - 1) / δ) (1 / δ) u :=
    ((hasDerivAt_id u).sub_const 1).div_const δ
  have := ((hasDerivAt_deriv_shortBumpProfile ((u - 1) / δ)).comp u hin).div_const δ
  exact this.congr_deriv (by ring)

/-- The Mellin transform of `φ_δ` is an integral over its support window `[1, 1 + δ]`. -/
theorem mellin_shortBump_eq {δ : ℝ} (hδ : 0 < δ) (s : ℂ) :
    mellin (fun u => (shortBump δ u : ℂ)) s =
      ∫ u in (1 : ℝ)..(1 + δ), (u : ℂ) ^ (s - 1) * shortBump δ u := by
  rw [mellin, intervalIntegral.integral_of_le (by linarith)]
  simp_rw [smul_eq_mul]
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_)
  · intro u hu; exact lt_trans zero_lt_one hu.1
  · intro u hu
    have : shortBump δ u = 0 := by
      apply shortBump_eq_zero hδ
      rintro ⟨h1, h2⟩
      exact hu.2 ⟨h1, h2.le⟩
    simp [this]

theorem norm_mellin_shortBump_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : ℂ} (hs : s.re ≤ 2) :
    ‖mellin (fun u => (shortBump δ u : ℂ)) s‖ ≤ 2 * δ := by
  rw [mellin_shortBump_eq hδ]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := 1 + δ) (C := 2)
    (f := fun u : ℝ => (u : ℂ) ^ (s - 1) * shortBump δ u) ?_
  · simpa [abs_of_pos hδ] using h
  intro u hu
  rw [uIoc_of_le (by linarith)] at hu
  have hu1 : 1 < u := hu.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (shortBump_nonneg _ _)]
  have h1 : u ^ (s - 1).re ≤ u ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1.le (by simp; linarith)
  rw [Real.rpow_one] at h1
  have h2 : u ^ (s - 1).re ≤ 2 := h1.trans (by linarith [hu.2])
  calc u ^ (s - 1).re * shortBump δ u ≤ 2 * 1 :=
        mul_le_mul h2 (shortBump_le_one _ _) (shortBump_nonneg _ _) (by norm_num)
    _ = 2 := by ring

/-- **Two integrations by parts.**  For `s ≠ 0, −1`,
`𝓜φ_δ(s) = (s(s+1))⁻¹ ∫_1^{1+δ} φ_δ''(u) u^{s+1} du`. -/
theorem mellin_shortBump_eq_second_deriv {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ -1) :
    mellin (fun u => (shortBump δ u : ℂ)) s = (1 / (s * (s + 1))) *
      ∫ u in (1 : ℝ)..(1 + δ),
        ((deriv (deriv shortBumpProfile) ((u - 1) / δ) / δ ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ (s + 1) := by
  rw [mellin_shortBump_eq hδ]
  have hle : (1 : ℝ) ≤ 1 + δ := by linarith
  have hpos : ∀ u ∈ uIcc (1 : ℝ) (1 + δ), (u : ℝ) ≠ 0 := by
    intro u hu; rw [uIcc_of_le hle] at hu; linarith [hu.1]
  -- boundary values
  have hb0 : shortBump δ 1 = 0 := shortBump_eq_zero hδ (by simp)
  have hb1 : shortBump δ (1 + δ) = 0 := shortBump_eq_zero hδ (by simp)
  have hd0 : deriv shortBumpProfile ((1 - 1) / δ) = 0 :=
    deriv_shortBumpProfile_eq_zero (by norm_num)
  have hd1 : deriv shortBumpProfile ((1 + δ - 1) / δ) = 0 := by
    apply deriv_shortBumpProfile_eq_zero
    rw [show (1 + δ - 1) / δ = 1 by rw [add_sub_cancel_left, div_self hδ.ne']]
    norm_num
  -- first integration by parts: `u^(s-1) = d/du (u^s / s)`
  have hV : ∀ u ∈ uIcc (1 : ℝ) (1 + δ),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ s / s) ((u : ℂ) ^ (s - 1)) u := by
    intro u hu
    have := hasDerivAt_ofReal_cpow_const' (hpos u hu) (r := s - 1) (by
      intro h; apply hs0; linear_combination h)
    simpa using this
  have hU : ∀ u ∈ uIcc (1 : ℝ) (1 + δ),
      HasDerivAt (fun y : ℝ => ((shortBump δ y : ℝ) : ℂ))
        (((deriv shortBumpProfile ((u - 1) / δ) / δ : ℝ) : ℂ)) u := by
    intro u _
    exact (hasDerivAt_shortBump δ u).ofReal_comp
  have hcontU' : Continuous fun u : ℝ => (((deriv shortBumpProfile ((u - 1) / δ) / δ : ℝ)) : ℂ) := by
    have : Continuous (deriv shortBumpProfile) := contDiff_deriv_shortBumpProfile.continuous
    fun_prop
  have hcontV' : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (s - 1)) (uIcc 1 (1 + δ)) := by
    intro u hu
    exact (continuousAt_ofReal_cpow_const u (s - 1) (Or.inr (hpos u hu))).continuousWithinAt
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU hV
    (hcontU'.intervalIntegrable _ _) (hcontV'.intervalIntegrable)
  -- second integration by parts: `u^s = d/du (u^(s+1)/(s+1))`
  have hW : ∀ u ∈ uIcc (1 : ℝ) (1 + δ),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (s + 1) / (s + 1)) ((u : ℂ) ^ s) u := by
    intro u hu
    exact hasDerivAt_ofReal_cpow_const' (hpos u hu) hs1
  have hU' : ∀ u ∈ uIcc (1 : ℝ) (1 + δ),
      HasDerivAt (fun y : ℝ => (((deriv shortBumpProfile ((y - 1) / δ) / δ : ℝ)) : ℂ))
        (((deriv (deriv shortBumpProfile) ((u - 1) / δ) / δ ^ 2 : ℝ) : ℂ)) u := by
    intro u _
    exact (hasDerivAt_deriv_shortBump δ u).ofReal_comp
  have hcontU'' : Continuous fun u : ℝ =>
      (((deriv (deriv shortBumpProfile) ((u - 1) / δ) / δ ^ 2 : ℝ)) : ℂ) := by
    have := continuous_deriv_deriv_shortBumpProfile
    fun_prop
  have hcontW' : ContinuousOn (fun u : ℝ => (u : ℂ) ^ s) (uIcc 1 (1 + δ)) := by
    intro u hu
    exact (continuousAt_ofReal_cpow_const u s (Or.inr (hpos u hu))).continuousWithinAt
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU' hW
    (hcontU''.intervalIntegrable _ _) (hcontW'.intervalIntegrable)
  -- assemble
  have e1 : (∫ u in (1 : ℝ)..(1 + δ), (u : ℂ) ^ (s - 1) * shortBump δ u) =
      ∫ u in (1 : ℝ)..(1 + δ), ((shortBump δ u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1) := by
    congr 1; ext u; ring
  rw [e1, ibp1, hb0, hb1]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_sub]
  have e2 : (∫ u in (1 : ℝ)..(1 + δ),
      (((deriv shortBumpProfile ((u - 1) / δ) / δ : ℝ)) : ℂ) * ((u : ℂ) ^ s / s)) =
      (1 / s) * ∫ u in (1 : ℝ)..(1 + δ),
        (((deriv shortBumpProfile ((u - 1) / δ) / δ : ℝ)) : ℂ) * (u : ℂ) ^ s := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext u; field_simp
  rw [e2, ibp2, hd0, hd1]
  simp only [zero_div, Complex.ofReal_zero, zero_mul, sub_zero, zero_sub]
  have e3 : (∫ u in (1 : ℝ)..(1 + δ),
      (((deriv (deriv shortBumpProfile) ((u - 1) / δ) / δ ^ 2 : ℝ)) : ℂ) *
        ((u : ℂ) ^ (s + 1) / (s + 1))) =
      (1 / (s + 1)) * ∫ u in (1 : ℝ)..(1 + δ),
        (((deriv (deriv shortBumpProfile) ((u - 1) / δ) / δ ^ 2 : ℝ)) : ℂ) * (u : ℂ) ^ (s + 1) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext u; field_simp
  rw [e3]
  have hs1' : s + 1 ≠ 0 := fun h => hs1 (by linear_combination h)
  field_simp

theorem norm_mellin_shortBump_le_decay {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M : ℝ}
    (hM : ∀ v, |deriv (deriv shortBumpProfile) v| ≤ M) {s : ℂ} (hs : s.re ≤ 2)
    (hs0 : s ≠ 0) (hs1 : s ≠ -1) :
    ‖mellin (fun u => (shortBump δ u : ℂ)) s‖ ≤ 8 * M / (δ * (‖s‖ * ‖s + 1‖)) := by
  rw [mellin_shortBump_eq_second_deriv hδ hs0 hs1, norm_mul]
  have hs1' : s + 1 ≠ 0 := fun h => hs1 (by linear_combination h)
  have hnorm : ‖(1 : ℂ) / (s * (s + 1))‖ = 1 / (‖s‖ * ‖s + 1‖) := by
    rw [norm_div, norm_one, norm_mul]
  have hint : ‖∫ u in (1 : ℝ)..(1 + δ),
      (((deriv (deriv shortBumpProfile) ((u - 1) / δ) / δ ^ 2 : ℝ)) : ℂ) * (u : ℂ) ^ (s + 1)‖
      ≤ 8 * M / δ ^ 2 * |1 + δ - 1| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [uIoc_of_le (by linarith)] at hu
    have hu1 : 1 < u := hu.1
    have hu2 : u ≤ 2 := by linarith [hu.2]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < δ ^ 2)]
    have h1 : u ^ (s + 1).re ≤ u ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1.le (by simp; linarith)
    have h2 : u ^ (3 : ℝ) ≤ 8 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ u) hu2 3]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    calc |deriv (deriv shortBumpProfile) ((u - 1) / δ)| / δ ^ 2 * u ^ (s + 1).re
        ≤ M / δ ^ 2 * 8 := by
          apply mul_le_mul (div_le_div_of_nonneg_right (hM _) (by positivity)) (h1.trans h2)
            (by positivity) (by positivity)
      _ = 8 * M / δ ^ 2 := by ring
  rw [hnorm]
  have hpos : 0 < ‖s‖ * ‖s + 1‖ := by
    have := norm_pos_iff.mpr hs0; have := norm_pos_iff.mpr hs1'; positivity
  calc 1 / (‖s‖ * ‖s + 1‖) * ‖∫ u in (1 : ℝ)..(1 + δ),
        (((deriv (deriv shortBumpProfile) ((u - 1) / δ) / δ ^ 2 : ℝ)) : ℂ) * (u : ℂ) ^ (s + 1)‖
      ≤ 1 / (‖s‖ * ‖s + 1‖) * (8 * M / δ ^ 2 * |1 + δ - 1|) := by gcongr
    _ = 8 * M / (δ * (‖s‖ * ‖s + 1‖)) := by
        rw [show (1 + δ - 1) = δ by ring, abs_of_pos hδ]
        field_simp

/-- **Lorentzian bound for the Mellin transform of the short bump.**  On `0 < Re s ≤ 2`,
`‖𝓜φ_δ(σ + it)‖ ≤ (4 + 16M) δ / (1 + δ²t²)`, where `M` bounds `ψ''`. -/
theorem norm_mellin_shortBump_le_lorentz {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M : ℝ}
    (hM : ∀ v, |deriv (deriv shortBumpProfile) v| ≤ M) {σ t : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) :
    ‖mellin (fun u => (shortBump δ u : ℂ)) (σ + t * I)‖ ≤ (4 + 16 * M) * δ / (1 + δ ^ 2 * t ^ 2) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hden : 0 < 1 + δ ^ 2 * t ^ 2 := by positivity
  rcases le_or_gt (δ ^ 2 * t ^ 2) 1 with hsmall | hbig
  · have h := norm_mellin_shortBump_le hδ hδ1 (s := σ + t * I) (by simpa using hσ2)
    refine h.trans ?_
    rw [le_div_iff₀ hden]
    nlinarith
  · have hs0 : (σ : ℂ) + t * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hs1 : (σ : ℂ) + t * I ≠ -1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h := norm_mellin_shortBump_le_decay hδ hδ1 hM (s := σ + t * I) (by simpa using hσ2) hs0 hs1
    refine h.trans ?_
    have ht1 : |t| ≤ ‖(σ : ℂ) + t * I‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + t * I); simpa using this
    have ht2 : |t| ≤ ‖(σ : ℂ) + t * I + 1‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + t * I + 1); simpa using this
    have htt : t ^ 2 ≤ ‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I + 1‖ := by
      have : t ^ 2 = |t| * |t| := by rw [← sq_abs]; ring
      rw [this]; exact mul_le_mul ht1 ht2 (abs_nonneg _) (norm_nonneg _)
    have ht0 : 0 < t ^ 2 := by
      by_contra h0
      have h0 : t ^ 2 ≤ 0 := not_lt.mp h0
      have : δ ^ 2 * t ^ 2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
      linarith
    calc 8 * M / (δ * (‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I + 1‖)) ≤ 8 * M / (δ * t ^ 2) := by
          gcongr
      _ ≤ (4 + 16 * M) * δ / (1 + δ ^ 2 * t ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) hden]
          nlinarith [mul_le_mul_of_nonneg_left hbig.le hM0]

/-- The short bump is Mellin-convergent at every `s`. -/
theorem mellinConvergent_shortBump {δ : ℝ} (hδ : 0 < δ) (s : ℂ) :
    MellinConvergent (fun u => (shortBump δ u : ℂ)) s := by
  have hc : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (s - 1) • ((shortBump δ u : ℝ) : ℂ))
      (Icc 1 (1 + δ)) := by
    intro u hu
    have hu0 : (u : ℝ) ≠ 0 := by linarith [hu.1]
    exact ((continuousAt_ofReal_cpow_const u (s - 1) (Or.inr hu0)).smul
      (Complex.continuous_ofReal.comp (continuous_shortBump δ)).continuousAt).continuousWithinAt
  have hI : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) • ((shortBump δ u : ℝ) : ℂ))
      (Icc 1 (1 + δ)) := hc.integrableOn_compact isCompact_Icc
  refine hI.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  intro u hu
  have : shortBump δ u = 0 := by
    apply shortBump_eq_zero hδ
    rintro ⟨h1, h2⟩; exact hu.2 ⟨h1.le, h2.le⟩
  simp [this]

theorem differentiable_mellin_shortBump {δ : ℝ} (hδ : 0 < δ) :
    Differentiable ℂ (mellin (fun u => (shortBump δ u : ℂ))) := by
  intro s
  have hloc : LocallyIntegrableOn (fun u : ℝ => (shortBump δ u : ℂ)) (Ioi 0) :=
    ((Complex.continuous_ofReal.comp (continuous_shortBump δ)).locallyIntegrable).locallyIntegrableOn _
  have htop : (fun u : ℝ => (shortBump δ u : ℂ)) =O[atTop] fun u => u ^ (-(s.re + 1)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (1 + δ)] with u hu
    have : shortBump δ u = 0 := shortBump_eq_zero hδ (fun h => by linarith [h.2])
    simp [this]
  have hzero : (fun u : ℝ => (shortBump δ u : ℂ)) =O[𝓝[>] 0] fun u => u ^ (-(s.re - 1)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    have : shortBump δ u = 0 := shortBump_eq_zero hδ (fun h => by linarith [h.1, hu.2])
    simp [this]
  exact (mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hzero (by linarith))

theorem integral_shortBump_ge {δ : ℝ} (hδ : 0 < δ) : δ / 4 ≤ ∫ u, shortBump δ u := by
  have hint : Integrable (shortBump δ) := by
    have hcs : HasCompactSupport (shortBump δ) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := 1) (b := 1 + δ)) ?_
      intro u hu
      exact shortBump_eq_zero hδ (fun h => hu ⟨h.1.le, h.2.le⟩)
    exact (continuous_shortBump δ).integrable_of_hasCompactSupport hcs
  calc δ / 4 = ∫ _u in Icc (1 + 3 * δ / 8) (1 + 5 * δ / 8), (1 : ℝ) := by
        simp; ring_nf
        rw [max_eq_left (by linarith)]
    _ = ∫ u in Icc (1 + 3 * δ / 8) (1 + 5 * δ / 8), shortBump δ u := by
        refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
        exact (shortBump_eq_one hδ hu).symm
    _ ≤ ∫ u, shortBump δ u :=
        setIntegral_le_integral hint (Eventually.of_forall fun u => shortBump_nonneg δ u)

/-- The scaled Lorentzian `δ / (1 + δ² y²)` is integrable. -/
theorem integrable_lorentz {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    Integrable fun y : ℝ => C * δ / (1 + δ ^ 2 * y ^ 2) := by
  have h := (integrable_inv_one_add_sq.comp_mul_left' hδ.ne').const_mul (C * δ)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [mul_pow]
  field_simp

theorem continuous_mellin_shortBump_line {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) :
    Continuous fun y : ℝ => mellin (fun u => (shortBump δ u : ℂ)) (σ + y * I) :=
  (differentiable_mellin_shortBump hδ).continuous.comp (by fun_prop)

theorem integrable_mellin_shortBump_line {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {σ : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 2) :
    Integrable fun y : ℝ => mellin (fun u => (shortBump δ u : ℂ)) (σ + y * I) := by
  obtain ⟨M, -, hM⟩ := exists_bound_deriv_deriv_shortBumpProfile
  refine (integrable_lorentz hδ (4 + 16 * M)).mono'
    (continuous_mellin_shortBump_line hδ σ).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  exact norm_mellin_shortBump_le_lorentz hδ hδ1 hM hσ hσ2

/-- Mellin inversion for the short bump on the line `Re s = 2`. -/
theorem shortBump_eq_mellinInv {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {u : ℝ} (hu : 0 < u) :
    ((shortBump δ u : ℝ) : ℂ) = (1 / (2 * (Real.pi : ℂ))) *
      ∫ y : ℝ, (u : ℂ) ^ (-((2 : ℂ) + y * I)) * mellin (fun u => (shortBump δ u : ℂ)) (2 + y * I) := by
  have hinv := mellinInv_mellin_eq (2 : ℝ) (fun u => (shortBump δ u : ℂ)) hu
    (by simpa using mellinConvergent_shortBump hδ (2 : ℂ))
    (by simpa [VerticalIntegrable] using
      integrable_mellin_shortBump_line hδ hδ1 (σ := 2) (by norm_num) le_rfl)
    ((Complex.continuous_ofReal.comp (continuous_shortBump δ)).continuousAt)
  rw [← hinv, mellinInv, Complex.real_smul]
  push_cast
  congr 1

/-- `(a/b)^{-w} = b^w / a^w` for positive reals. -/
theorem ofReal_div_cpow_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℂ) :
    ((a / b : ℝ) : ℂ) ^ (-w) = (b : ℂ) ^ w / (a : ℂ) ^ w := by
  rw [div_eq_mul_inv a b, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hb.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hb.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg, Complex.cpow_neg, inv_inv, div_eq_mul_inv, mul_comm]

theorem norm_ofReal_cpow_two_add {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖(x : ℂ) ^ ((2 : ℂ) + y * I)‖ = x ^ (2 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp

/-- **Mellin representation of the smoothed weighted sum.**  For `x > 0`,
`Σ_n lam(n) φ_δ(n/x) = (1/2π) ∫ x^{2+iy} 𝓜φ_δ(2+iy) D(2+iy) dy`, with `D` the Dirichlet series of
`lam`. -/
theorem tsum_mul_shortBump_eq_integral {lam : ℕ → ℝ}
    (hsum : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ (2 : ℝ))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx : 0 < x) :
    ((∑' n : ℕ, lam n * shortBump δ (n / x) : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ, (x : ℂ) ^ ((2 : ℂ) + y * I) *
        mellin (fun u => (shortBump δ u : ℂ)) (2 + y * I) *
          LSeries (fun n => (lam n : ℂ)) (2 + y * I) := by
  set M : ℂ → ℂ := mellin (fun u => (shortBump δ u : ℂ))
  set F : ℕ → ℝ → ℂ := fun n y => (x : ℂ) ^ ((2 : ℂ) + y * I) * M (2 + y * I) *
    LSeries.term (fun n => (lam n : ℂ)) (2 + y * I) n
  have hMint : Integrable fun y : ℝ => M (2 + y * I) := by
    simpa using integrable_mellin_shortBump_line hδ hδ1 (σ := 2) (by norm_num) le_rfl
  have hMcont : Continuous fun y : ℝ => M (2 + y * I) := by
    simpa using continuous_mellin_shortBump_line hδ 2
  have hnormF : ∀ n y, ‖F n y‖ = x ^ (2 : ℝ) * (|lam n| / (n : ℝ) ^ (2 : ℝ)) * ‖M (2 + y * I)‖ := by
    intro n y
    simp only [F, norm_mul, norm_ofReal_cpow_two_add hx, LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, Complex.norm_real]; ring
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    refine (hMint.norm.const_mul (x ^ (2 : ℝ) * (|lam n| / (n : ℝ) ^ (2 : ℝ)))).mono' ?_
      (Eventually.of_forall fun y => (hnormF n y).le)
    have hterm : Continuous fun y : ℝ => LSeries.term (fun n => (lam n : ℂ)) (2 + y * I) n := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero]; exact continuous_const
      · simp only [LSeries.term_of_ne_zero hn]
        have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        have hn0' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        exact continuous_const.div (continuous_const.cpow (by fun_prop)
          (fun _ => Or.inl (by simpa using hn0')))
          (fun y => Complex.cpow_ne_zero_iff.mpr (Or.inl hn'))
    have hxpow : Continuous fun y : ℝ => (x : ℂ) ^ ((2 : ℂ) + y * I) :=
      continuous_const.cpow (by fun_prop) (fun _ => Or.inl (by simpa using hx))
    exact ((hxpow.mul hMcont).mul hterm).aestronglyMeasurable
  have hFsum : Summable fun n => ∫ y, ‖F n y‖ := by
    simp_rw [hnormF, integral_const_mul]
    exact (hsum.mul_left (x ^ (2 : ℝ))).mul_right _
  have hFn : ∀ n, ∫ y, F n y = 2 * (Real.pi : ℂ) * ((lam n * shortBump δ (n / x) : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have : shortBump δ 0 = 0 := shortBump_eq_zero hδ (by simp)
      simp [F, this]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hinv := shortBump_eq_mellinInv hδ hδ1 (div_pos hn0 hx)
      have hre : ∀ y : ℝ, F n y = (lam n : ℂ) *
          ((((n : ℝ) / x : ℝ) : ℂ) ^ (-((2 : ℂ) + y * I)) * M (2 + y * I)) := by
        intro y
        simp only [F, LSeries.term_of_ne_zero hn, ofReal_div_cpow_neg hn0 hx,
          Complex.ofReal_natCast]
        ring
      simp_rw [hre, integral_const_mul]
      rw [Complex.ofReal_mul, hinv]
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      rw [show ∀ Z : ℂ, 2 * (Real.pi : ℂ) * ((lam n : ℂ) * (1 / (2 * (Real.pi : ℂ)) * Z))
        = (lam n : ℂ) * Z from fun Z => by field_simp]
  have hsumF : ∀ y, ∑' n, F n y = (x : ℂ) ^ ((2 : ℂ) + y * I) * M (2 + y * I) *
      LSeries (fun n => (lam n : ℂ)) (2 + y * I) := by
    intro y
    simp only [F, LSeries]
    exact tsum_mul_left
  calc ((∑' n : ℕ, lam n * shortBump δ (n / x) : ℝ) : ℂ)
      = (1 / (2 * (Real.pi : ℂ))) * ∑' n, ∫ y, F n y := by
        have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        simp_rw [hFn]
        rw [tsum_mul_left, Complex.ofReal_tsum]
        field_simp
    _ = (1 / (2 * (Real.pi : ℂ))) * ∫ y, ∑' n, F n y := by
        rw [integral_tsum_of_summable_integral_norm hFint hFsum]
    _ = _ := by simp_rw [hsumF]

/-- `∫_{u>1} u^{-w} du = 1/(w − 1)` for `Re w > 1`. -/
theorem integral_Ioi_one_cpow_neg {w : ℂ} (hw : 1 < w.re) :
    ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (-w) = 1 / (w - 1) := by
  rw [integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
  simp only [Complex.ofReal_one, one_cpow]
  have : -w + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have : w - 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring

/-- **The pole term.**  For `x ≥ 1`,
`x ∫ φ_δ = (1/2π) ∫ x^{2+iy} 𝓜φ_δ(2+iy) / (1 + iy) dy`. -/
theorem integral_shortBump_eq_pole_integral {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    ((x * ∫ u, shortBump δ u : ℝ) : ℂ) = (1 / (2 * (Real.pi : ℂ))) *
      ∫ y : ℝ, (x : ℂ) ^ ((2 : ℂ) + y * I) * mellin (fun u => (shortBump δ u : ℂ)) (2 + y * I) *
        (1 / ((2 : ℂ) + y * I - 1)) := by
  have hx0 : 0 < x := by linarith
  set M : ℂ → ℂ := mellin (fun u => (shortBump δ u : ℂ))
  have hMint : Integrable fun y : ℝ => M (2 + y * I) := by
    simpa using integrable_mellin_shortBump_line hδ hδ1 (σ := 2) (by norm_num) le_rfl
  have hMcont : Continuous fun y : ℝ => M (2 + y * I) := by
    simpa using continuous_mellin_shortBump_line hδ 2
  -- step 1: `x ∫ φ_δ = ∫_{u > 1} φ_δ(u/x) du`
  have h1 : x * ∫ u, shortBump δ u = ∫ u in Ioi (1 : ℝ), shortBump δ (u / x) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, Measure.integral_comp_div,
      abs_of_pos hx0, smul_eq_mul]
    intro u hu
    apply shortBump_eq_zero hδ
    rintro ⟨h, -⟩
    simp only [mem_Ioi, not_lt] at hu
    rw [lt_div_iff₀ hx0] at h
    linarith
  -- step 2: Mellin inversion under the integral
  set f : ℝ → ℝ → ℂ := fun u y => (x : ℂ) ^ ((2 : ℂ) + y * I) * M (2 + y * I) *
    (u : ℂ) ^ (-((2 : ℂ) + y * I))
  have hpt : ∀ u ∈ Ioi (1 : ℝ), ((shortBump δ (u / x) : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ y, f u y := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu
    rw [shortBump_eq_mellinInv hδ hδ1 (div_pos hu0 hx0)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [f, ofReal_div_cpow_neg hu0 hx0]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
    ring
  -- step 3: Fubini
  have hnorm : ∀ u ∈ Ioi (1 : ℝ), ∀ y : ℝ, ‖f u y‖ = x ^ (2 : ℝ) * u ^ (-2 : ℝ) * ‖M (2 + y * I)‖ := by
    intro u hu y
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu
    simp only [f, norm_mul, norm_ofReal_cpow_two_add hx0,
      Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    simp; ring
  have hmeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Ioi (1 : ℝ))).prod volume) := by
    have hc : Continuous fun p : ℝ × ℝ => (x : ℂ) ^ ((2 : ℂ) + p.2 * I) * M (2 + p.2 * I) := by
      have hxpow : Continuous fun y : ℝ => (x : ℂ) ^ ((2 : ℂ) + y * I) :=
        continuous_const.cpow (by fun_prop) (fun _ => Or.inl (by simpa using hx0))
      exact (hxpow.mul hMcont).comp continuous_snd
    have hm : Measurable fun p : ℝ × ℝ => (p.1 : ℂ) ^ (-((2 : ℂ) + p.2 * I)) := by
      apply Measurable.pow
      · exact Complex.measurable_ofReal.comp measurable_fst
      · exact (measurable_const.add ((Complex.measurable_ofReal.comp measurable_snd).mul
          measurable_const)).neg
    exact (hc.aestronglyMeasurable.mul hm.aestronglyMeasurable)
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Ioi (1 : ℝ))).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℝ => (x ^ (2 : ℝ) * p.1 ^ (-2 : ℝ)) * ‖M (2 + p.2 * I)‖)
        ((volume.restrict (Ioi (1 : ℝ))).prod volume) := by
      refine Integrable.mul_prod (f := fun u : ℝ => x ^ (2 : ℝ) * u ^ (-2 : ℝ))
        (g := fun y : ℝ => ‖M (2 + y * I)‖) ?_ hMint.norm
      exact (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _
    refine hg.mono' hmeas ?_
    have hprod : (volume.restrict (Ioi (1 : ℝ))).prod (volume : Measure ℝ)
        = ((volume : Measure ℝ).prod volume).restrict (Ioi (1 : ℝ) ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hprod]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
    simp only [Function.uncurry]
    rw [hnorm p.1 hp.1 p.2]
  -- step 4: inner integral in `u`
  have hinner : ∀ y : ℝ, ∫ u in Ioi (1 : ℝ), f u y =
      (x : ℂ) ^ ((2 : ℂ) + y * I) * M (2 + y * I) * (1 / ((2 : ℂ) + y * I - 1)) := by
    intro y
    simp only [f]
    rw [integral_const_mul, integral_Ioi_one_cpow_neg (by simp)]
  -- assemble
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h1, ← integral_complex_ofReal]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  congr 1
  rw [integral_integral_swap hint]
  simp_rw [hinner]

/-- The constant `∫ (|v| + 3)^{1/2} / (1 + v²) dv`. -/
noncomputable def lorentzHalfConst : ℝ := ∫ v : ℝ, (|v| + 3) ^ (1 / 2 : ℝ) / (1 + v ^ 2)

theorem integrable_rpow_half_div_one_add_sq : Integrable fun v : ℝ => (|v| + 3) ^ (1 / 2 : ℝ) / (1 + v ^ 2) := by
  have hbase : Integrable fun v : ℝ => (1 + ‖v‖) ^ (-(3 / 2 : ℝ)) :=
    integrable_one_add_norm (by simp; norm_num)
  have hc : Continuous fun v : ℝ => (|v| + 3) ^ (1 / 2 : ℝ) / (1 + v ^ 2) :=
    ((continuous_abs.add continuous_const).rpow_const (fun _ => Or.inr (by norm_num))).div
      (by fun_prop) (fun v => by positivity)
  refine (hbase.const_mul 4).mono' hc.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  have h1 : 0 < 1 + |v| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs]
  have hA : (|v| + 3) ^ (1 / 2 : ℝ) ≤ 2 * (1 + |v|) ^ (1 / 2 : ℝ) := by
    have : |v| + 3 ≤ 2 ^ (2 : ℝ) * (1 + |v|) := by norm_num; linarith [abs_nonneg v]
    calc (|v| + 3) ^ (1 / 2 : ℝ) ≤ (2 ^ (2 : ℝ) * (1 + |v|)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) this (by norm_num)
      _ = 2 * (1 + |v|) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by positivity) h1.le, ← Real.rpow_mul (by norm_num)]; norm_num
  have hB : 1 / (1 + v ^ 2) ≤ 2 * (1 + |v|) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg h1.le, Real.rpow_two, ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_abs v, abs_nonneg v, sq_nonneg (|v| - 1)]
  calc (|v| + 3) ^ (1 / 2 : ℝ) / (1 + v ^ 2) = (|v| + 3) ^ (1 / 2 : ℝ) * (1 / (1 + v ^ 2)) := by
        ring
    _ ≤ (2 * (1 + |v|) ^ (1 / 2 : ℝ)) * (2 * (1 + |v|) ^ (-(2 : ℝ))) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = 4 * (1 + |v|) ^ (-(3 / 2 : ℝ)) := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_mul_mul_comm, ← Real.rpow_add h1]; norm_num

/-- **Lorentzian against a small power.**  For `0 < δ ≤ 1` and `0 < κ ≤ 1/2`:
`∫ δ/(1 + δ²y²) (|y| + 3)^κ dy ≤ δ^{-κ} · lorentzHalfConst`. -/
theorem integral_lorentz_rpow_le {δ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 < κ)
    (hκ2 : κ ≤ 1 / 2) :
    Integrable (fun y : ℝ => δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ κ) ∧
      ∫ y : ℝ, δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ κ ≤ δ ^ (-κ) * lorentzHalfConst := by
  set g : ℝ → ℝ := fun v => (|v| + 3) ^ (1 / 2 : ℝ) / (1 + v ^ 2)
  have hg : Integrable g := integrable_rpow_half_div_one_add_sq
  have hgδ : Integrable fun y : ℝ => δ ^ (-κ) * δ * g (δ * y) :=
    (hg.comp_mul_left' hδ.ne').const_mul _
  have hpt : ∀ y : ℝ, δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ κ ≤ δ ^ (-κ) * δ * g (δ * y) := by
    intro y
    have hy1 : |y| + 3 ≤ (|δ * y| + 3) / δ := by
      rw [le_div_iff₀ hδ, abs_mul, abs_of_pos hδ]; nlinarith [abs_nonneg y]
    have hpow1 : (|y| + 3) ^ κ ≤ ((|δ * y| + 3) / δ) ^ κ :=
      Real.rpow_le_rpow (by positivity) hy1 hκ.le
    have hpow2 : ((|δ * y| + 3) / δ) ^ κ = δ ^ (-κ) * (|δ * y| + 3) ^ κ := by
      rw [Real.div_rpow (by positivity) hδ.le, Real.rpow_neg hδ.le]; ring
    have hpow3 : (|δ * y| + 3) ^ κ ≤ (|δ * y| + 3) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (δ * y)]) hκ2
    have hden : 1 + δ ^ 2 * y ^ 2 = 1 + (δ * y) ^ 2 := by ring
    simp only [g]
    rw [hden]
    calc δ / (1 + (δ * y) ^ 2) * (|y| + 3) ^ κ
        ≤ δ / (1 + (δ * y) ^ 2) * (δ ^ (-κ) * (|δ * y| + 3) ^ (1 / 2 : ℝ)) := by
          gcongr
          calc (|y| + 3) ^ κ ≤ ((|δ * y| + 3) / δ) ^ κ := hpow1
            _ = δ ^ (-κ) * (|δ * y| + 3) ^ κ := hpow2
            _ ≤ δ ^ (-κ) * (|δ * y| + 3) ^ (1 / 2 : ℝ) := by gcongr
      _ = δ ^ (-κ) * δ * ((|δ * y| + 3) ^ (1 / 2 : ℝ) / (1 + (δ * y) ^ 2)) := by ring
  have hint : Integrable (fun y : ℝ => δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ κ) :=
    hgδ.mono' (by fun_prop) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt y)
  refine ⟨hint, ?_⟩
  calc ∫ y : ℝ, δ / (1 + δ ^ 2 * y ^ 2) * (|y| + 3) ^ κ ≤ ∫ y : ℝ, δ ^ (-κ) * δ * g (δ * y) :=
        integral_mono hint hgδ hpt
    _ = δ ^ (-κ) * lorentzHalfConst := by
        rw [integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hδ),
          smul_eq_mul, lorentzHalfConst]
        field_simp
        rfl

/-- `log z ≤ z^κ / κ` on `z = |y| + 3`. -/
theorem log_abs_add_three_le_rpow {κ : ℝ} (hκ : 0 < κ) (y : ℝ) :
    Real.log (|y| + 3) ≤ (|y| + 3) ^ κ / κ :=
  Real.log_le_rpow_div (by positivity) hκ

/-- **Pointwise bound on the shifted integrand.**  With `G(s) = x^s 𝓜φ_δ(s) E(s)`,
`‖G(σ + iy)‖ ≤ x^σ (4 + 16M) C δ/(1 + δ²y²) · log(|y| + 3)/(σ − 1/2)`. -/
theorem norm_shiftedIntegrand_le {E : ℂ → ℂ} {C M : ℝ}
    (hE : ∀ σ t : ℝ, 1 / 2 < σ → σ ≤ 2 → ‖E (σ + t * I)‖ ≤ C * Real.log (|t| + 3) / (σ - 1 / 2))
    (hM : ∀ v, |deriv (deriv shortBumpProfile) v| ≤ M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ2 : σ ≤ 2) (y : ℝ) :
    ‖(x : ℂ) ^ ((σ : ℂ) + y * I) * mellin (fun u => (shortBump δ u : ℂ)) (σ + y * I) *
        E (σ + y * I)‖ ≤
      x ^ σ * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) * (C * Real.log (|y| + 3) / (σ - 1 / 2)) := by
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have h1 := norm_mellin_shortBump_le_lorentz hδ hδ1 hM (σ := σ) (t := y) (by linarith) hσ2
  have h2 := hE σ y hσ hσ2
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero, zero_mul,
    add_zero]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hpos : 0 ≤ x ^ σ * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) := by positivity
  calc x ^ σ * ‖mellin (fun u => (shortBump δ u : ℂ)) (σ + y * I)‖ * ‖E (σ + y * I)‖
      ≤ x ^ σ * ((4 + 16 * M) * δ / (1 + δ ^ 2 * y ^ 2)) * ‖E (σ + y * I)‖ := by gcongr
    _ ≤ _ := by gcongr

end GaloisForLFunctions.HTGeometry
