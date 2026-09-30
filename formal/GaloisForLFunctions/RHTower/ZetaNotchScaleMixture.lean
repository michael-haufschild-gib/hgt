import GaloisForLFunctions.RHTower.ZetaNotchDualOscillation
import GaloisForLFunctions.HTGeometry.StripSquareMeanConvexity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# A Gaussian mixture of notch windows

Let `B(s) = ω_1(s)` be the notch profile, so that the notch window at scale `u > 0` is
`ω_u(t) = B(t/u)` (`notchWindow_eq_notchProfile`), and let `ρ_L(u) = e^{−(u−L)²}`. The mixed window

`Ω_L(z) = ∫_{2/5}^{2} B(1/r) r^{−1} e^{−(zr − L)²} dr`

is entire (`differentiable_mixWindow`), real and nonnegative on the real line, and there it is the
Gaussian mixture of notch windows over the scale (`mixWindowReal_eq_integral_scale`):

`Ω_L(t) = ∫_0^∞ ρ_L(u) u^{−1} ω_u(t) du`  for `t > 0`,

by the substitution `u = tr`. On horizontal lines `‖Ω_L(x + iy)‖ ≤ e^{4y²} Ω_L(x)`
(`norm_mixWindow_le`); on the negative half-line `Ω_L = O(e^{−L²})`
(`mixWindowReal_le_of_nonpos`); and `Ω_L(x) ≤ 4 e^{L²} e^{−2x²/25}` (`mixWindowReal_le_gauss`).

Integrals against the mixture split into scale integrals of notch-window integrals
(`integral_Ioi_mixWindowReal_mul`), so every estimate for the notch window at a single scale
transfers to the mixture, while the analyticity of `Ω_L` gives exponential decay of transforms.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.ZetaNotch

/-! ## The notch profile -/

/-- The notch profile `B = ω_1`: `1` on `[1, 2]`, `0` outside `[1/2, 5/2]`. -/
def notchProfile (s : ℝ) : ℝ := blockWindow 1 2 (1 / 2) s

theorem notchProfile_nonneg (s : ℝ) : 0 ≤ notchProfile s := blockWindow_nonneg _ _ _ _

theorem notchProfile_le_one (s : ℝ) : notchProfile s ≤ 1 := blockWindow_le_one _ _ _ _

theorem continuous_notchProfile : Continuous notchProfile :=
  (contDiff_blockWindow 1 2 (1 / 2)).continuous

theorem notchProfile_eq_zero_of_le {s : ℝ} (hs : s ≤ 1 / 2) : notchProfile s = 0 :=
  blockWindow_eq_zero_of_le (by norm_num) (by linarith)

theorem notchProfile_eq_zero_of_ge {s : ℝ} (hs : 5 / 2 ≤ s) : notchProfile s = 0 :=
  blockWindow_eq_zero_of_ge (by norm_num) (by linarith)

/-- The notch window is the dilated profile: `ω_u(t) = B(t/u)`. -/
theorem notchWindow_eq_notchProfile {u : ℝ} (hu : 0 < u) (t : ℝ) :
    notchWindow u t = ((notchProfile (t / u) : ℝ) : ℂ) := by
  unfold notchWindow blockWindowC notchProfile blockWindow smoothWeight
  have e1 : (u / 2)⁻¹ * (t + -(u - u / 2)) = (1 / 2 : ℝ)⁻¹ * (t / u + -(1 - 1 / 2)) := by
    field_simp
  have e2 : (u / 2)⁻¹ * (t + -(2 * u)) = (1 / 2 : ℝ)⁻¹ * (t / u + -2) := by
    field_simp
  rw [e1, e2]

/-! ## The mixture coefficient -/

/-- The coefficient `B(1/r) r^{−1}` of the mixture in the inverse scale `r`. -/
def mixCoeff (r : ℝ) : ℝ := notchProfile r⁻¹ * r⁻¹

theorem mixCoeff_eq_zero_of_le {r : ℝ} (hr : r ≤ 2 / 5) : mixCoeff r = 0 := by
  unfold mixCoeff
  rcases le_or_gt r 0 with h0 | h0
  · rw [notchProfile_eq_zero_of_le (by linarith [inv_nonpos.mpr h0]), zero_mul]
  · have : 5 / 2 ≤ r⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) h0]; linarith
    rw [notchProfile_eq_zero_of_ge this, zero_mul]

theorem mixCoeff_eq_zero_of_ge {r : ℝ} (hr : 2 ≤ r) : mixCoeff r = 0 := by
  unfold mixCoeff
  have : r⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  rw [notchProfile_eq_zero_of_le this, zero_mul]

theorem mixCoeff_nonneg (r : ℝ) : 0 ≤ mixCoeff r := by
  rcases le_or_gt r (2 / 5) with h | h
  · rw [mixCoeff_eq_zero_of_le h]
  · exact mul_nonneg (notchProfile_nonneg _) (inv_nonneg.mpr (by linarith))

theorem mixCoeff_le {r : ℝ} (hr : 2 / 5 ≤ r) : mixCoeff r ≤ 5 / 2 := by
  unfold mixCoeff
  have hr0 : 0 < r := by linarith
  have h1 : r⁻¹ ≤ 5 / 2 := by rw [inv_le_comm₀ hr0 (by norm_num)]; linarith
  calc notchProfile r⁻¹ * r⁻¹ ≤ 1 * r⁻¹ :=
        mul_le_mul_of_nonneg_right (notchProfile_le_one _) (inv_nonneg.mpr hr0.le)
    _ ≤ 5 / 2 := by linarith

theorem continuous_mixCoeff : Continuous mixCoeff := by
  rw [continuous_iff_continuousAt]
  intro r
  rcases lt_or_ge r (2 / 5) with h | h
  · have hev : mixCoeff =ᶠ[𝓝 r] fun _ => (0 : ℝ) :=
      Filter.mem_of_superset (Iio_mem_nhds h) fun x hx => mixCoeff_eq_zero_of_le (le_of_lt hx)
    exact (continuousAt_const).congr hev.symm
  · have hr0 : r ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    exact (continuous_notchProfile.continuousAt.comp (continuousAt_inv₀ hr0)).mul
      (continuousAt_inv₀ hr0)

/-! ## The mixed window -/

/-- The scale weight `ρ_L(u) = e^{−(u−L)²}`. -/
def scaleWeight (L u : ℝ) : ℝ := Real.exp (-(u - L) ^ 2)

theorem scaleWeight_pos (L u : ℝ) : 0 < scaleWeight L u := Real.exp_pos _

theorem scaleWeight_le_one (L u : ℝ) : scaleWeight L u ≤ 1 :=
  Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (u - L)])

/-- The mixed window `Ω_L(z) = ∫_{2/5}^{2} B(1/r) r^{−1} e^{−(zr − L)²} dr`. -/
def mixWindow (L : ℝ) (z : ℂ) : ℂ :=
  ∫ r in (2 / 5 : ℝ)..2, (mixCoeff r : ℂ) * Complex.exp (-(z * r - L) ^ 2)

/-- The mixed window on the real line. -/
def mixWindowReal (L t : ℝ) : ℝ := ∫ r in (2 / 5 : ℝ)..2, mixCoeff r * scaleWeight L (t * r)

theorem mixWindow_ofReal (L t : ℝ) : mixWindow L t = (mixWindowReal L t : ℂ) := by
  unfold mixWindow mixWindowReal scaleWeight
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun r _ => ?_
  push_cast
  rfl

theorem continuous_mixIntegrand (L : ℝ) :
    Continuous fun q : ℝ × ℂ => (mixCoeff q.1 : ℂ) * Complex.exp (-(q.2 * q.1 - L) ^ 2) :=
  (Complex.continuous_ofReal.comp (continuous_mixCoeff.comp continuous_fst)).mul
    (by fun_prop)

/-- **The mixed window is entire.** -/
theorem differentiable_mixWindow (L : ℝ) : Differentiable ℂ (mixWindow L) := by
  have h := differentiableOn_intervalIntegral_of_continuousOn_prod (a := 2 / 5) (b := 2)
    isOpen_univ (F := fun r z => (mixCoeff r : ℂ) * Complex.exp (-(z * r - L) ^ 2))
    (continuous_mixIntegrand L).continuousOn
    (fun r => (Differentiable.differentiableOn (by fun_prop)))
  intro z
  exact (h z (mem_univ z)).differentiableAt univ_mem

theorem mixWindowReal_nonneg (L t : ℝ) : 0 ≤ mixWindowReal L t :=
  intervalIntegral.integral_nonneg (by norm_num) fun r _ =>
    mul_nonneg (mixCoeff_nonneg r) (scaleWeight_pos L _).le

theorem continuous_mixWindowReal (L : ℝ) : Continuous (mixWindowReal L) := by
  have h : (mixWindowReal L) = fun t : ℝ => (mixWindow L (t : ℂ)).re := by
    funext t; rw [mixWindow_ofReal, Complex.ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp
    ((differentiable_mixWindow L).continuous.comp Complex.continuous_ofReal)

/-! ## Bounds on horizontal lines -/

theorem re_neg_sq_mix (x y r L : ℝ) :
    (-(((x : ℂ) + y * I) * r - L) ^ 2).re = -(x * r - L) ^ 2 + (y * r) ^ 2 := by
  simp only [sq, Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem norm_mixIntegrand_le (L x y : ℝ) {r : ℝ} (hr : r ≤ 2) (hr0 : 0 ≤ r) :
    ‖(mixCoeff r : ℂ) * Complex.exp (-(((x : ℂ) + y * I) * r - L) ^ 2)‖ ≤
      Real.exp (4 * y ^ 2) * (mixCoeff r * scaleWeight L (x * r)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mixCoeff_nonneg r),
    Complex.norm_exp, re_neg_sq_mix]
  have hle : -(x * r - L) ^ 2 + (y * r) ^ 2 ≤ 4 * y ^ 2 + -(x * r - L) ^ 2 := by
    have : (y * r) ^ 2 ≤ 4 * y ^ 2 := by
      have hr2 : r ^ 2 ≤ 4 := by nlinarith
      rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_left hr2 (sq_nonneg y)]
    linarith
  calc mixCoeff r * Real.exp (-(x * r - L) ^ 2 + (y * r) ^ 2)
      ≤ mixCoeff r * Real.exp (4 * y ^ 2 + -(x * r - L) ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (mixCoeff_nonneg r)
    _ = Real.exp (4 * y ^ 2) * (mixCoeff r * scaleWeight L (x * r)) := by
        rw [Real.exp_add, scaleWeight]; ring

theorem intervalIntegrable_mixReal (L x : ℝ) :
    IntervalIntegrable (fun r => mixCoeff r * scaleWeight L (x * r)) volume (2 / 5) 2 :=
  (continuous_mixCoeff.mul (Real.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _

/-- **Horizontal lines**: `‖Ω_L(x + iy)‖ ≤ e^{4y²} Ω_L(x)`. -/
theorem norm_mixWindow_le (L x y : ℝ) :
    ‖mixWindow L ((x : ℂ) + y * I)‖ ≤ Real.exp (4 * y ^ 2) * mixWindowReal L x := by
  unfold mixWindow mixWindowReal
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Eventually.of_forall fun r hr => norm_mixIntegrand_le L x y hr.2 (by linarith [hr.1]))
    ((intervalIntegrable_mixReal L x).const_mul _)

theorem integral_mixCoeff_le : ∫ r in (2 / 5 : ℝ)..2, mixCoeff r ≤ 4 := by
  calc ∫ r in (2 / 5 : ℝ)..2, mixCoeff r ≤ ∫ _ in (2 / 5 : ℝ)..2, (5 / 2 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (continuous_mixCoeff.intervalIntegrable _ _) intervalIntegrable_const
          fun r hr => mixCoeff_le hr.1
    _ = 4 := by rw [intervalIntegral.integral_const]; norm_num

/-- If `ρ_L(xr) ≤ M` for `r ∈ [2/5, 2]` then `Ω_L(x) ≤ 4M`. -/
theorem mixWindowReal_le_of_forall {L x M : ℝ}
    (hM : ∀ r, 2 / 5 ≤ r → r ≤ 2 → scaleWeight L (x * r) ≤ M) : mixWindowReal L x ≤ 4 * M := by
  have hM0 : 0 ≤ M := (scaleWeight_pos L _).le.trans (hM 1 (by norm_num) (by norm_num))
  unfold mixWindowReal
  calc ∫ r in (2 / 5 : ℝ)..2, mixCoeff r * scaleWeight L (x * r)
      ≤ ∫ r in (2 / 5 : ℝ)..2, mixCoeff r * M :=
        intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_mixReal L x)
          ((continuous_mixCoeff.intervalIntegrable _ _).mul_const M)
          fun r hr => mul_le_mul_of_nonneg_left (hM r hr.1 hr.2) (mixCoeff_nonneg r)
    _ = (∫ r in (2 / 5 : ℝ)..2, mixCoeff r) * M := intervalIntegral.integral_mul_const _ _
    _ ≤ 4 * M := mul_le_mul_of_nonneg_right integral_mixCoeff_le hM0

/-- **Gaussian decay**: `Ω_L(x) ≤ 4 e^{L²} e^{−2x²/25}`. -/
theorem mixWindowReal_le_gauss (L x : ℝ) :
    mixWindowReal L x ≤ 4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * x ^ 2)) := by
  refine mixWindowReal_le_of_forall fun r hr1 hr2 => ?_
  rw [scaleWeight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hr : (4 / 25 : ℝ) ≤ r ^ 2 := by nlinarith
  nlinarith [sq_nonneg (x * r - 2 * L), sq_nonneg x, mul_le_mul_of_nonneg_left hr (sq_nonneg x)]

/-- **The negative half-line**: for `L ≥ 0`, `x ≤ 0`, `Ω_L(x) ≤ 4 e^{−L²} e^{−4x²/25}`. -/
theorem mixWindowReal_le_of_nonpos {L x : ℝ} (hL : 0 ≤ L) (hx : x ≤ 0) :
    mixWindowReal L x ≤ 4 * (Real.exp (-L ^ 2) * Real.exp (-(4 / 25) * x ^ 2)) := by
  refine mixWindowReal_le_of_forall fun r hr1 hr2 => ?_
  rw [scaleWeight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hr : (4 / 25 : ℝ) ≤ r ^ 2 := by nlinarith
  have hxr : x * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg x), mul_nonneg (neg_nonneg.mpr hxr) hL]

/-! ## The scale superposition -/

/-- **The mixture over scales**: for `t > 0`, `Ω_L(t) = ∫_0^∞ ρ_L(u) u^{−1} B(t/u) du`. -/
theorem mixWindowReal_eq_integral_scale (L : ℝ) {t : ℝ} (ht : 0 < t) :
    mixWindowReal L t = ∫ u in Ioi 0, scaleWeight L u / u * notchProfile (t / u) := by
  unfold mixWindowReal
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun r hr => show (0 : ℝ) < r by linarith [hr.1]) (fun r hr => ?_)]
  · set g : ℝ → ℝ := fun u => mixCoeff (u / t) * scaleWeight L u with hg
    have hcomp : ∀ r, mixCoeff r * scaleWeight L (t * r) = g (t * r) := by
      intro r
      simp only [hg]
      rw [mul_div_cancel_left₀ r ht.ne']
    simp_rw [hcomp]
    rw [integral_comp_mul_left_Ioi g 0 ht, mul_zero, smul_eq_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    simp only [hg, mixCoeff, inv_div]
    field_simp
  · rcases hr with ⟨hr0, hrI⟩
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hrI
    rcases hrI with h | h
    · rw [mixCoeff_eq_zero_of_le h, zero_mul]
    · rw [mixCoeff_eq_zero_of_ge h.le, zero_mul]

theorem notchWindow_eq_zero_of_nonpos {u t : ℝ} (hu : 0 < u) (ht : t ≤ 0) :
    notchProfile (t / u) = 0 :=
  notchProfile_eq_zero_of_le ((div_nonpos_of_nonpos_of_nonneg ht hu.le).trans (by norm_num))

theorem hasCompactSupport_notchWindow' {u : ℝ} (hu : 0 < u) : HasCompactSupport (notchWindow u) :=
  HasCompactSupport.intro isCompact_Icc fun _ ht => notchWindow_eq_zero hu ht

/-- The scale integrand `ρ_L(u) u^{−1} B(t/u) F(t)`. -/
def scaleIntegrand (L : ℝ) (F : ℝ → ℂ) (u t : ℝ) : ℂ :=
  ((scaleWeight L u / u * notchProfile (t / u) : ℝ) : ℂ) * F t

theorem continuousOn_scaleIntegrand (L : ℝ) {F : ℝ → ℂ} (hF : Continuous F) :
    ContinuousOn (Function.uncurry (scaleIntegrand L F)) (Ioi 0 ×ˢ univ) := by
  have hu : ContinuousOn (fun p : ℝ × ℝ => p.1) (Ioi 0 ×ˢ univ) := continuous_fst.continuousOn
  have hne : ∀ p ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), p.1 ≠ 0 := fun p hp => (mem_Ioi.mp hp.1).ne'
  have h1 : ContinuousOn (fun p : ℝ × ℝ => scaleWeight L p.1 / p.1) (Ioi 0 ×ˢ univ) :=
    ((Real.continuous_exp.comp (by fun_prop)).continuousOn).div hu hne
  have h2 : ContinuousOn (fun p : ℝ × ℝ => notchProfile (p.2 / p.1)) (Ioi 0 ×ˢ univ) :=
    continuous_notchProfile.comp_continuousOn (continuous_snd.continuousOn.div hu hne)
  exact (Complex.continuous_ofReal.comp_continuousOn (h1.mul h2)).mul
    (hF.comp continuous_snd).continuousOn

theorem integrable_scaleWeight_mul_quadratic (L a b c : ℝ) :
    Integrable (fun u => scaleWeight L u * (a + b * u + c * u ^ 2)) := by
  have h0 : Integrable (fun w : ℝ => Real.exp (-w ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) one_pos
  have h1 : Integrable (fun w : ℝ => w * Real.exp (-w ^ 2)) := by
    simpa using integrable_mul_exp_neg_mul_sq (b := 1) one_pos
  have h2 : Integrable (fun w : ℝ => w ^ 2 * Real.exp (-w ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (2 : ℕ)) (by norm_num)
    simpa [Real.rpow_natCast] using this
  have hG := ((h0.const_mul (a + b * L + c * L ^ 2)).add (h1.const_mul (b + 2 * c * L))).add
    (h2.const_mul c)
  refine (hG.comp_sub_right L).congr (Eventually.of_forall fun u => ?_)
  simp only [scaleWeight, Pi.add_apply]
  ring

/-- **The scale integrand is integrable** on `(0, ∞) × ℝ` for polynomially bounded `F`. -/
theorem integrable_scaleIntegrand (L : ℝ) {F : ℝ → ℂ} (hF : Continuous F) {C : ℝ}
    (hC : ∀ t, ‖F t‖ ≤ C * (1 + |t|) ^ 2) :
    Integrable (Function.uncurry (scaleIntegrand L F))
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg (F 0)).trans (hC 0)
    simp at this
    exact this
  have hμ : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) =
      ((volume : Measure ℝ).prod volume).restrict (Ioi 0 ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEStronglyMeasurable (Function.uncurry (scaleIntegrand L F))
      ((volume.restrict (Ioi 0)).prod volume) := by
    rw [hμ]
    exact (continuousOn_scaleIntegrand L hF).aestronglyMeasurable
      (measurableSet_Ioi.prod MeasurableSet.univ)
  rw [integrable_prod_iff hmeas]
  constructor
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have e : (fun t => Function.uncurry (scaleIntegrand L F) (u, t)) =
        fun t => ((scaleWeight L u / u : ℝ) : ℂ) * (notchWindow u t * F t) := by
      funext t
      simp only [Function.uncurry_apply_pair, scaleIntegrand]
      rw [notchWindow_eq_notchProfile hu0]
      push_cast
      ring
    rw [e]
    exact (((continuous_notchWindow u).mul hF).integrable_of_hasCompactSupport
      ((hasCompactSupport_notchWindow' hu0).mul_right)).const_mul _
  · refine Integrable.mono' ((integrable_scaleWeight_mul_quadratic L 1 5 (25 / 4)).const_mul
      (2 * C)).integrableOn hmeas.norm.integral_prod_right' ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    set K : ℝ := scaleWeight L u / u * (C * (1 + 5 / 2 * u) ^ 2) with hK
    have hK0 : 0 ≤ K := by
      have := scaleWeight_pos L u
      positivity
    have hpt : ∀ t, ‖Function.uncurry (scaleIntegrand L F) (u, t)‖ ≤
        (Icc (u / 2) (5 / 2 * u)).indicator (fun _ => K) t := by
      intro t
      simp only [Function.uncurry_apply_pair, scaleIntegrand, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hw0 : 0 ≤ scaleWeight L u / u := (div_pos (scaleWeight_pos L u) hu0).le
      by_cases ht : t ∈ Icc (u / 2) (5 / 2 * u)
      · rw [indicator_of_mem ht, hK, abs_of_nonneg hw0, abs_of_nonneg (notchProfile_nonneg _)]
        have hB := notchProfile_le_one (t / u)
        have ht0 : 0 ≤ t := by linarith [ht.1]
        have hFt : ‖F t‖ ≤ C * (1 + 5 / 2 * u) ^ 2 := by
          refine (hC t).trans (mul_le_mul_of_nonneg_left ?_ hC0)
          rw [abs_of_nonneg ht0]
          exact pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2
        calc scaleWeight L u / u * notchProfile (t / u) * ‖F t‖
            ≤ scaleWeight L u / u * 1 * (C * (1 + 5 / 2 * u) ^ 2) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hB hw0) hFt (norm_nonneg _) (by positivity)
          _ = K := by rw [hK]; ring
      · rw [indicator_of_notMem ht]
        simp only [mem_Icc, not_and_or, not_le] at ht
        have hB : notchProfile (t / u) = 0 := by
          rcases ht with h | h
          · exact notchProfile_eq_zero_of_le (by rw [div_le_iff₀ hu0]; linarith)
          · exact notchProfile_eq_zero_of_ge (by rw [le_div_iff₀ hu0]; linarith)
        rw [hB, abs_zero, mul_zero, zero_mul]
    have hint : ∫ t, ‖Function.uncurry (scaleIntegrand L F) (u, t)‖ ≤
        ∫ t, (Icc (u / 2) (5 / 2 * u)).indicator (fun _ => K) t :=
      integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
        ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
        (Eventually.of_forall hpt)
    rw [integral_indicator_const K measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
      smul_eq_mul] at hint
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    refine hint.trans (le_of_eq ?_)
    rw [hK]
    field_simp
    ring

/-- **Integrals against the mixture are scale integrals of notch-window integrals.** For
continuous `F` with `‖F(t)‖ ≤ C(1 + |t|)²`,

`∫_{t>0} Ω_L(t) F(t) dt = ∫_0^∞ ρ_L(u) u^{−1} (∫ ω_u(t) F(t) dt) du`. -/
theorem integral_Ioi_mixWindowReal_mul (L : ℝ) {F : ℝ → ℂ} (hF : Continuous F) {C : ℝ}
    (hC : ∀ t, ‖F t‖ ≤ C * (1 + |t|) ^ 2) :
    ∫ t in Ioi 0, (mixWindowReal L t : ℂ) * F t =
      ∫ u in Ioi 0, ((scaleWeight L u / u : ℝ) : ℂ) * ∫ t, notchWindow u t * F t := by
  have hR : (∫ u in Ioi 0, ((scaleWeight L u / u : ℝ) : ℂ) * ∫ t, notchWindow u t * F t) =
      ∫ u in Ioi 0, ∫ t, scaleIntegrand L F u t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [scaleIntegrand, notchWindow_eq_notchProfile hu0]
    push_cast
    ring
  have hL : (∫ t in Ioi 0, (mixWindowReal L t : ℂ) * F t) =
      ∫ t, ∫ u in Ioi 0, scaleIntegrand L F u t := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht]
      have ht0 : (0 : ℝ) < t := ht
      simp only [scaleIntegrand]
      rw [integral_mul_const, integral_complex_ofReal, mixWindowReal_eq_integral_scale L ht0]
    · rw [indicator_of_notMem ht]
      have ht0 : t ≤ 0 := not_lt.mp ht
      have hz : ∀ u ∈ Ioi (0 : ℝ), scaleIntegrand L F u t = 0 := by
        intro u hu
        rw [scaleIntegrand, notchWindow_eq_zero_of_nonpos hu ht0]
        simp
      rw [setIntegral_congr_fun measurableSet_Ioi hz, integral_zero]
  rw [hL, hR]
  exact (integral_integral_swap (integrable_scaleIntegrand L hF hC)).symm

/-! ## Gaussian moment bounds -/

theorem sq_mul_exp_neg_le (b x : ℝ) (hb : 0 < b) :
    x ^ 2 * Real.exp (-(b * x ^ 2)) ≤ b⁻¹ * Real.exp (-(b / 2 * x ^ 2)) := by
  have hX : 0 ≤ b * x ^ 2 := by positivity
  have h1 : b * x ^ 2 ≤ Real.exp (b * x ^ 2 / 2) := by
    have := Real.add_one_le_exp (b * x ^ 2 / 4)
    have h2 : Real.exp (b * x ^ 2 / 2) = Real.exp (b * x ^ 2 / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h2]
    nlinarith [sq_nonneg (b * x ^ 2 / 4 - 1)]
  have h3 : x ^ 2 ≤ b⁻¹ * Real.exp (b * x ^ 2 / 2) := by
    rw [le_inv_mul_iff₀ hb]; exact h1
  calc x ^ 2 * Real.exp (-(b * x ^ 2)) ≤ b⁻¹ * Real.exp (b * x ^ 2 / 2) * Real.exp (-(b * x ^ 2)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = b⁻¹ * Real.exp (-(b / 2 * x ^ 2)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem integrable_exp_neg_mul_sq' {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-(b * x ^ 2))) := by
  simpa [neg_mul] using integrable_exp_neg_mul_sq hb

/-- `∫ ρ_L(u) (1 + 5u/2)² du ≤ C (1 + L²)`. -/
theorem exists_integral_scaleWeight_mul_sq_le :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ,
      ∫ u, scaleWeight L u * (1 + 5 * u + 25 / 4 * u ^ 2) ≤ C * (1 + L ^ 2) := by
  set A₀ : ℝ := ∫ w : ℝ, Real.exp (-(1 * w ^ 2)) with hA₀
  set A₁ : ℝ := ∫ w : ℝ, Real.exp (-(1 / 2 * w ^ 2)) with hA₁
  have hA₀0 : 0 ≤ A₀ := integral_nonneg fun _ => (Real.exp_pos _).le
  have hA₁0 : 0 ≤ A₁ := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨27 * A₀ + 25 * A₁, by positivity, fun L => ?_⟩
  have hi0 := integrable_exp_neg_mul_sq' (b := 1) one_pos
  have hi1 := integrable_exp_neg_mul_sq' (b := 1 / 2) (by norm_num)
  set g : ℝ → ℝ := fun w => (2 + 25 * L ^ 2) * Real.exp (-(1 * w ^ 2)) +
    25 * Real.exp (-(1 / 2 * w ^ 2)) with hg
  have hgi : Integrable g := (hi0.const_mul _).add (hi1.const_mul _)
  have hpt : ∀ u, scaleWeight L u * (1 + 5 * u + 25 / 4 * u ^ 2) ≤ g (u - L) := by
    intro u
    have hq : 1 + 5 * u + 25 / 4 * u ^ 2 ≤ 2 + 25 * L ^ 2 + 25 * (u - L) ^ 2 := by
      nlinarith [sq_nonneg (5 / 2 * u - 1), sq_nonneg (u - 2 * L), sq_nonneg (u - L)]
    have hs := sq_mul_exp_neg_le 1 (u - L) one_pos
    have he : scaleWeight L u = Real.exp (-(1 * (u - L) ^ 2)) := by rw [scaleWeight, one_mul]
    rw [he, hg]
    simp only
    have hpos := Real.exp_pos (-(1 * (u - L) ^ 2))
    calc Real.exp (-(1 * (u - L) ^ 2)) * (1 + 5 * u + 25 / 4 * u ^ 2)
        ≤ Real.exp (-(1 * (u - L) ^ 2)) * (2 + 25 * L ^ 2 + 25 * (u - L) ^ 2) :=
          mul_le_mul_of_nonneg_left hq hpos.le
      _ = (2 + 25 * L ^ 2) * Real.exp (-(1 * (u - L) ^ 2)) +
            25 * ((u - L) ^ 2 * Real.exp (-(1 * (u - L) ^ 2))) := by ring
      _ ≤ (2 + 25 * L ^ 2) * Real.exp (-(1 * (u - L) ^ 2)) +
            25 * ((1 : ℝ)⁻¹ * Real.exp (-(1 / 2 * (u - L) ^ 2))) := by linarith
      _ = _ := by rw [inv_one, one_mul, one_mul]
  have hq_int : Integrable (fun u => scaleWeight L u * (1 + 5 * u + 25 / 4 * u ^ 2)) :=
    integrable_scaleWeight_mul_quadratic L 1 5 (25 / 4)
  calc ∫ u, scaleWeight L u * (1 + 5 * u + 25 / 4 * u ^ 2) ≤ ∫ u, g (u - L) :=
        integral_mono hq_int (hgi.comp_sub_right L) hpt
    _ = ∫ w, g w := integral_sub_right_eq_self g L
    _ = (2 + 25 * L ^ 2) * A₀ + 25 * A₁ := by
        rw [hg, integral_add (hi0.const_mul _) (hi1.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ (27 * A₀ + 25 * A₁) * (1 + L ^ 2) := by nlinarith [sq_nonneg L]

/-! ## Polynomial moments of the mixed window -/

/-- A notch-window integral of a function bounded by `K` on `[u/2, 5u/2]` is at most `2uK`. -/
theorem integral_notchProfile_mul_le {u : ℝ} (hu : 0 < u) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t)
    {K : ℝ} (hK : ∀ t ∈ Icc (u / 2) (5 / 2 * u), f t ≤ K) :
    ∫ t, notchProfile (t / u) * f t ≤ 2 * u * K := by
  have hK0 : 0 ≤ K := (hf0 u).trans (hK u ⟨by linarith, by linarith⟩)
  have hpt : ∀ t, notchProfile (t / u) * f t ≤ (Icc (u / 2) (5 / 2 * u)).indicator (fun _ => K) t := by
    intro t
    by_cases ht : t ∈ Icc (u / 2) (5 / 2 * u)
    · rw [indicator_of_mem ht]
      calc notchProfile (t / u) * f t ≤ 1 * K :=
            mul_le_mul (notchProfile_le_one _) (hK t ht) (hf0 t) zero_le_one
        _ = K := one_mul K
    · rw [indicator_of_notMem ht]
      simp only [mem_Icc, not_and_or, not_le] at ht
      have hB : notchProfile (t / u) = 0 := by
        rcases ht with h | h
        · exact notchProfile_eq_zero_of_le (by rw [div_le_iff₀ hu]; linarith)
        · exact notchProfile_eq_zero_of_ge (by rw [le_div_iff₀ hu]; linarith)
      rw [hB, zero_mul]
  have h := integral_mono_of_nonneg
    (Eventually.of_forall fun t => mul_nonneg (notchProfile_nonneg (t / u)) (hf0 t))
    ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
    (Eventually.of_forall hpt)
  rw [integral_indicator_const K measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
    smul_eq_mul] at h
  linarith

theorem integrable_sq_mul_exp_neg {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(b * x ^ 2))) := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := b) hb (s := (2 : ℕ)) (by norm_num)
  simpa [Real.rpow_natCast, neg_mul] using this

theorem one_add_abs_sq_le (x : ℝ) : (1 + |x|) ^ 2 ≤ 2 + 2 * x ^ 2 := by
  have := sq_abs x
  nlinarith [sq_nonneg (|x| - 1)]

theorem integrable_mixWindowReal_mul_sq (L : ℝ) :
    Integrable (fun x => mixWindowReal L x * (1 + |x|) ^ 2) := by
  have hb : (0 : ℝ) < 2 / 25 := by norm_num
  have hg : Integrable (fun x : ℝ => 4 * Real.exp (L ^ 2) *
      (2 * Real.exp (-(2 / 25 * x ^ 2)) + 2 * (x ^ 2 * Real.exp (-(2 / 25 * x ^ 2))))) :=
    (((integrable_exp_neg_mul_sq' hb).const_mul 2).add
      ((integrable_sq_mul_exp_neg hb).const_mul 2)).const_mul _
  refine hg.mono' ((continuous_mixWindowReal L).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mixWindowReal_nonneg L x) (by positivity))]
  have h1 := mixWindowReal_le_gauss L x
  have h2 := one_add_abs_sq_le x
  have he : Real.exp (-(2 / 25) * x ^ 2) = Real.exp (-(2 / 25 * x ^ 2)) := by ring_nf
  rw [he] at h1
  have hpos := Real.exp_pos (-(2 / 25 * x ^ 2))
  calc mixWindowReal L x * (1 + |x|) ^ 2
      ≤ (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25 * x ^ 2)))) * (2 + 2 * x ^ 2) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by ring

/-- **The quadratic moment of the mixed window on the negative half-line** is `O(e^{−L²})`. -/
theorem exists_integral_Iic_mixWindowReal_mul_sq_le :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L →
      ∫ x in Iic 0, mixWindowReal L x * (1 + |x|) ^ 2 ≤ C * Real.exp (-L ^ 2) := by
  have hb : (0 : ℝ) < 4 / 25 := by norm_num
  set g : ℝ → ℝ := fun x => 2 * Real.exp (-(4 / 25 * x ^ 2)) +
    2 * (x ^ 2 * Real.exp (-(4 / 25 * x ^ 2))) with hgdef
  have hgi : Integrable g :=
    ((integrable_exp_neg_mul_sq' hb).const_mul 2).add ((integrable_sq_mul_exp_neg hb).const_mul 2)
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rw [hgdef]; positivity
  have hgint : 0 ≤ ∫ x, g x := integral_nonneg (fun x => hg0 x : 0 ≤ g)
  refine ⟨4 * ∫ x, g x, by positivity, fun L hL => ?_⟩
  have hpt : ∀ x ∈ Iic (0 : ℝ), mixWindowReal L x * (1 + |x|) ^ 2 ≤
      Real.exp (-L ^ 2) * (4 * g x) := by
    intro x hx
    have h1 := mixWindowReal_le_of_nonpos hL (mem_Iic.mp hx)
    have h2 := one_add_abs_sq_le x
    have he : Real.exp (-(4 / 25) * x ^ 2) = Real.exp (-(4 / 25 * x ^ 2)) := by ring_nf
    rw [he] at h1
    calc mixWindowReal L x * (1 + |x|) ^ 2
        ≤ (4 * (Real.exp (-L ^ 2) * Real.exp (-(4 / 25 * x ^ 2)))) * (2 + 2 * x ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Real.exp (-L ^ 2) * (4 * g x) := by rw [hgdef]; ring
  calc ∫ x in Iic 0, mixWindowReal L x * (1 + |x|) ^ 2
      ≤ ∫ x in Iic 0, Real.exp (-L ^ 2) * (4 * g x) :=
        setIntegral_mono_on (integrable_mixWindowReal_mul_sq L).integrableOn
          ((hgi.const_mul 4).const_mul _).integrableOn measurableSet_Iic hpt
    _ ≤ ∫ x, Real.exp (-L ^ 2) * (4 * g x) :=
        setIntegral_le_integral ((hgi.const_mul 4).const_mul _)
          (Eventually.of_forall fun x => by have := hg0 x; positivity)
    _ = 4 * (∫ x, g x) * Real.exp (-L ^ 2) := by
        rw [integral_const_mul, integral_const_mul]; ring

/-- The positive half-line moment as a scale integral. -/
theorem integral_Ioi_mixWindowReal_mul_sq_eq (L : ℝ) :
    ∫ x in Ioi 0, mixWindowReal L x * (1 + |x|) ^ 2 =
      ∫ u in Ioi 0, scaleWeight L u / u * ∫ t, notchProfile (t / u) * (1 + |t|) ^ 2 := by
  have h := integral_Ioi_mixWindowReal_mul L (F := fun t => (((1 + |t|) ^ 2 : ℝ) : ℂ))
    (by fun_prop) (C := 1) (fun t => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul])
  have hL : ∫ t in Ioi 0, (mixWindowReal L t : ℂ) * (((1 + |t|) ^ 2 : ℝ) : ℂ) =
      ((∫ x in Ioi 0, mixWindowReal L x * (1 + |x|) ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    rfl
  have hR : ∫ u in Ioi 0, ((scaleWeight L u / u : ℝ) : ℂ) *
      ∫ t, notchWindow u t * (((1 + |t|) ^ 2 : ℝ) : ℂ) =
      ((∫ u in Ioi 0, scaleWeight L u / u * ∫ t, notchProfile (t / u) * (1 + |t|) ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hin : ∫ t, notchWindow u t * (((1 + |t|) ^ 2 : ℝ) : ℂ) =
        ((∫ t, notchProfile (t / u) * (1 + |t|) ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext t
      rw [notchWindow_eq_notchProfile hu0]
      push_cast
      ring
    rw [hin]
    push_cast
    ring
  rw [hL, hR] at h
  exact_mod_cast h

/-- **The quadratic moment of the mixed window is polynomial in `L`**:
`∫ Ω_L(x)(1 + |x|)² dx ≤ C (1 + L²)`. -/
theorem exists_integral_mixWindowReal_mul_sq_le :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ x, mixWindowReal L x * (1 + |x|) ^ 2 ≤ C * (1 + L ^ 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_integral_scaleWeight_mul_sq_le
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_integral_Iic_mixWindowReal_mul_sq_le
  refine ⟨2 * C₁ + C₂, by positivity, fun L hL => ?_⟩
  have hi := integrable_mixWindowReal_mul_sq L
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hi, compl_Ioi]
  have hpos : ∫ x in Ioi 0, mixWindowReal L x * (1 + |x|) ^ 2 ≤ 2 * C₁ * (1 + L ^ 2) := by
    rw [integral_Ioi_mixWindowReal_mul_sq_eq]
    have hqi := integrable_scaleWeight_mul_quadratic L 1 5 (25 / 4)
    have hpt : ∀ u ∈ Ioi (0 : ℝ), scaleWeight L u / u * ∫ t, notchProfile (t / u) * (1 + |t|) ^ 2 ≤
        2 * (scaleWeight L u * (1 + 5 * u + 25 / 4 * u ^ 2)) := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu
      have hb := integral_notchProfile_mul_le hu0 (f := fun t => (1 + |t|) ^ 2)
        (fun t => by positivity) (K := (1 + 5 / 2 * u) ^ 2) (fun t ht => by
          have ht0 : 0 ≤ t := by linarith [ht.1]
          rw [abs_of_nonneg ht0]
          exact pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2)
      have hw : 0 ≤ scaleWeight L u / u := (div_pos (scaleWeight_pos L u) hu0).le
      calc scaleWeight L u / u * ∫ t, notchProfile (t / u) * (1 + |t|) ^ 2
          ≤ scaleWeight L u / u * (2 * u * (1 + 5 / 2 * u) ^ 2) :=
            mul_le_mul_of_nonneg_left hb hw
        _ = 2 * (scaleWeight L u * (1 + 5 * u + 25 / 4 * u ^ 2)) := by
            field_simp
            ring
    have hint : IntegrableOn (fun u => scaleWeight L u / u *
        ∫ t, notchProfile (t / u) * (1 + |t|) ^ 2) (Ioi 0) := by
      refine (hqi.const_mul 2).integrableOn.mono' ?_ ?_
      · have hm : Measurable (Function.uncurry fun (u t : ℝ) => notchProfile (t / u) * (1 + |t|) ^ 2) :=
          (continuous_notchProfile.measurable.comp (measurable_snd.div measurable_fst)).mul
            (by fun_prop)
        exact (((Real.continuous_exp.comp (by fun_prop)).measurable.div measurable_id).mul
          hm.stronglyMeasurable.integral_prod_right.measurable).aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun u hu => ?_
        have hu0 : (0 : ℝ) < u := hu
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_pos (scaleWeight_pos L u) hu0).le
          (integral_nonneg fun t => mul_nonneg (notchProfile_nonneg _) (by positivity)))]
        exact hpt u hu
    calc ∫ u in Ioi 0, scaleWeight L u / u * ∫ t, notchProfile (t / u) * (1 + |t|) ^ 2
        ≤ ∫ u in Ioi 0, 2 * (scaleWeight L u * (1 + 5 * u + 25 / 4 * u ^ 2)) :=
          setIntegral_mono_on hint (hqi.const_mul 2).integrableOn measurableSet_Ioi hpt
      _ ≤ ∫ u, 2 * (scaleWeight L u * (1 + 5 * u + 25 / 4 * u ^ 2)) :=
          setIntegral_le_integral (hqi.const_mul 2) (Eventually.of_forall fun u => by
            have := scaleWeight_pos L u
            have : 0 ≤ 1 + 5 * u + 25 / 4 * u ^ 2 := by nlinarith [sq_nonneg (5 / 2 * u + 1)]
            positivity)
      _ = 2 * ∫ u, scaleWeight L u * (1 + 5 * u + 25 / 4 * u ^ 2) := integral_const_mul _ _
      _ ≤ 2 * (C₁ * (1 + L ^ 2)) := by linarith [hC₁ L]
      _ = 2 * C₁ * (1 + L ^ 2) := by ring
  have hneg := hC₂ L hL
  have he : Real.exp (-L ^ 2) ≤ 1 + L ^ 2 := by
    have : Real.exp (-L ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg L])
    nlinarith [sq_nonneg L]
  nlinarith [mul_le_mul_of_nonneg_left he hC₂0]

end RHTower.ZetaNotch
