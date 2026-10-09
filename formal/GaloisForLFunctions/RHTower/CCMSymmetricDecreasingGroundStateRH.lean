import GaloisForLFunctions.RHTower.CCMEigenvectorLowFrequencyMassBound

/-!
# Nonnegative symmetric-decreasing ground states force RH

The low-frequency content of a transform `F(z) = ∫ conj(f(t)) e^{izt} dt` at width `σ` is a mass of
`f` against a positive kernel:

  `I_σ(F) = √(π/σ) ∫ conj(f(t)) k_σ(t) dt`,  `k_σ(t) = ∫ b(x) e^{-(t-x)²/4σ} dx`,

where `b ≥ 0` is the bump of `lowFrequencyMass` (`lowFrequencyMass_conjTransform_eq`).

If `f` is real, nonnegative, supported in `[-A, A]` and symmetric-decreasing (`f(t) ≤ f(s)` whenever
`|s| ≤ |t|`), the mass in `[-r, r]` is at least `r/(r+A)` of the total. Since `k_σ ≥ b̂(0)e^{-(r+1)²/4σ}`
there, `|I_σ(F)| ≥ √(π/σ) b̂(0) e^{-(r+1)²/4σ} (r/(r+A)) ‖f‖₁` (`norm_lowFrequencyMass_ge`). At
`σ = A/40` and `r = √σ`, the share `|I_σ(F)|/‖f‖₁` is at least a constant over `A`. That is far
above the `e^{-A}` required by `riemannHypothesis_of_fullGrounds_lowFrequencyMass`.

* `riemannHypothesis_of_fullGrounds_symmDecreasing`: if nonzero full ground states at apertures
  `a_j → ∞` are nonnegative and symmetric-decreasing, the Riemann hypothesis holds.

The truncated Riemann kernel `Φ·1_{[-a,a]}`, the conjectured shape of the ground states under RH,
has exactly this shape.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

open RHTower.CCMFullGroundEigen

noncomputable section

/-! ## The Gaussian Fourier integral and the time-domain kernel -/

/-- `∫ e^{isy} e^{-σs²} ds = √(π/σ) e^{-y²/4σ}`. -/
theorem integral_cexp_mul_gaussian {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    ∫ s : ℝ, cexp (I * (s : ℂ) * (y : ℂ)) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2) =
      ((Real.sqrt (Real.pi / σ) * Real.exp (-(y ^ 2) / (4 * σ)) : ℝ) : ℂ) := by
  have hσ' : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have hbre : (-(σ : ℂ)).re < 0 := by simp [hσ]
  have key := integral_cexp_quadratic hbre (I * (y : ℂ)) 0
  have hpt : ∀ s : ℝ, cexp (I * (s : ℂ) * (y : ℂ)) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2) =
      cexp (-(σ : ℂ) * (s : ℂ) ^ 2 + I * (y : ℂ) * s + 0) := by
    intro s
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), key]
  have hpow : ((Real.pi : ℂ) / -(-(σ : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / σ) : ℝ) : ℂ) := by
    rw [neg_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity), ofReal_div]
    norm_num
  have hexp : cexp (0 - (I * (y : ℂ)) ^ 2 / (4 * -(σ : ℂ))) =
      ((Real.exp (-(y ^ 2) / (4 * σ)) : ℝ) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hpow, hexp]
  push_cast
  ring

/-- The positive time-domain kernel `k_σ(t) = ∫ b(x) e^{-(t-x)²/4σ} dx`. -/
def lowFrequencyKernel (σ t : ℝ) : ℝ := ∫ x : ℝ, posBump x * Real.exp (-((t - x) ^ 2) / (4 * σ))

theorem exp_neg_sq_div_le_one {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    Real.exp (-(y ^ 2) / (4 * σ)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg y]) (by linarith)

theorem posBump_mul_exp_le {σ : ℝ} (hσ : 0 < σ) (t x : ℝ) :
    posBump x * Real.exp (-((t - x) ^ 2) / (4 * σ)) ≤ posBump x := by
  calc posBump x * Real.exp (-((t - x) ^ 2) / (4 * σ)) ≤ posBump x * 1 :=
        mul_le_mul_of_nonneg_left (exp_neg_sq_div_le_one hσ (t - x)) (posBump.nonneg' x)
    _ = posBump x := mul_one _

theorem integrable_lowFrequencyKernel_integrand {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    Integrable fun x : ℝ => posBump x * Real.exp (-((t - x) ^ 2) / (4 * σ)) := by
  have hb : Continuous fun x : ℝ => posBump x := posBump.continuous
  refine integrable_posBump.mono' (hb.mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (posBump.nonneg' x) (Real.exp_pos _).le)]
  exact posBump_mul_exp_le hσ t x

theorem lowFrequencyKernel_nonneg (σ t : ℝ) : 0 ≤ lowFrequencyKernel σ t :=
  integral_nonneg fun x => mul_nonneg (posBump.nonneg' x) (Real.exp_pos _).le

theorem lowFrequencyKernel_le {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : lowFrequencyKernel σ t ≤ posBumpMass :=
  integral_mono (integrable_lowFrequencyKernel_integrand hσ t) integrable_posBump
    fun x => posBump_mul_exp_le hσ t x

theorem continuous_lowFrequencyKernel {σ : ℝ} (hσ : 0 < σ) : Continuous (lowFrequencyKernel σ) := by
  have hb : Continuous fun x : ℝ => posBump x := posBump.continuous
  refine continuous_of_dominated (bound := fun x => posBump x)
    (fun t => (hb.mul (by fun_prop)).aestronglyMeasurable) (fun t => ae_of_all _ fun x => ?_)
    integrable_posBump (ae_of_all _ fun x => continuous_const.mul (by fun_prop))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (posBump.nonneg' x) (Real.exp_pos _).le)]
  exact posBump_mul_exp_le hσ t x

/-- The frequency weight `e^{-σs²} b̂(-s)` integrates against `e^{ist}` to `√(π/σ) k_σ(t)`. -/
theorem integral_cexp_mul_lowFrequencyWeight {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ∫ s : ℝ, cexp (I * (s : ℂ) * (t : ℂ)) *
        (cexp (-(σ : ℂ) * (s : ℂ) ^ 2) * suzukiSmoothFourier posBumpTest (-(s : ℂ))) =
      ((Real.sqrt (Real.pi / σ) * lowFrequencyKernel σ t : ℝ) : ℂ) := by
  set H : ℝ → ℝ → ℂ := fun s x => cexp (I * (s : ℂ) * (t : ℂ)) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2) *
    (((posBump x : ℝ) : ℂ) * cexp (I * (-(s : ℂ)) * (x : ℂ))) with hH
  have hrw : ∀ s : ℝ, cexp (I * (s : ℂ) * (t : ℂ)) *
      (cexp (-(σ : ℂ) * (s : ℂ) ^ 2) * suzukiSmoothFourier posBumpTest (-(s : ℂ))) =
      ∫ x : ℝ, H s x := by
    intro s
    have hb : suzukiSmoothFourier posBumpTest (-(s : ℂ)) =
        ∫ x : ℝ, ((posBump x : ℝ) : ℂ) * cexp (I * (-(s : ℂ)) * (x : ℂ)) := rfl
    rw [hb, ← mul_assoc, ← integral_const_mul]
  rw [integral_congr_ae (ae_of_all _ hrw)]
  have hb : Continuous fun x : ℝ => posBump x := posBump.continuous
  have hint : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-σ * p.1 ^ 2) * posBump p.2)
        (volume.prod volume) :=
      (integrable_exp_neg_mul_sq hσ).mul_prod integrable_posBump
    refine hdom.mono' ?_ (ae_of_all _ fun p => ?_)
    · have hc : Continuous (Function.uncurry H) := by
        simp only [hH]
        have h2 : Continuous fun p : ℝ × ℝ => ((posBump p.2 : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp (hb.comp continuous_snd)
        refine Continuous.mul (by fun_prop) (h2.mul (by fun_prop))
      exact hc.aestronglyMeasurable
    · obtain ⟨s, x⟩ := p
      simp only [Function.uncurry_apply_pair, hH, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (posBump.nonneg' x)]
      rw [norm_cexp_neg_ofReal_mul_sq]
      have h1 : ‖cexp (I * (s : ℂ) * (t : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      have h2 : ‖cexp (I * (-(s : ℂ)) * (x : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [h1, h2]
      simp only [ofReal_re, ofReal_im, one_mul, mul_one]
      have : -(σ * (s ^ 2 - 0 ^ 2)) = -σ * s ^ 2 := by ring
      rw [this]
  rw [integral_integral_swap hint]
  have hinner : ∀ x : ℝ, ∫ s : ℝ, H s x =
      ((posBump x * (Real.sqrt (Real.pi / σ) * Real.exp (-((t - x) ^ 2) / (4 * σ))) : ℝ) : ℂ) := by
    intro x
    have h1 : ∀ s : ℝ, H s x = ((posBump x : ℝ) : ℂ) *
        (cexp (I * (s : ℂ) * ((t - x : ℝ) : ℂ)) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2)) := by
      intro s
      have he : cexp (I * (s : ℂ) * (t : ℂ)) * cexp (I * (-(s : ℂ)) * (x : ℂ)) =
          cexp (I * (s : ℂ) * ((t - x : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      simp only [hH]
      rw [← he]
      ring
    rw [integral_congr_ae (ae_of_all _ h1), integral_const_mul, integral_cexp_mul_gaussian hσ]
    push_cast
    ring
  rw [integral_congr_ae (ae_of_all _ hinner), integral_complex_ofReal]
  congr 1
  rw [lowFrequencyKernel, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  ring

/-- **The time-domain form of the low-frequency content.**
`I_σ(F) = √(π/σ) ∫ conj(f(t)) k_σ(t) dt` for `F = conjTransform f`. -/
theorem lowFrequencyMass_conjTransform_eq {σ : ℝ} (hσ : 0 < σ) {f : ℝ → ℂ} (hf : Integrable f) :
    lowFrequencyMass (conjTransform f) σ = ((Real.sqrt (Real.pi / σ) : ℝ) : ℂ) *
      ∫ t : ℝ, (starRingEnd ℂ) (f t) * ((lowFrequencyKernel σ t : ℝ) : ℂ) := by
  set G : ℝ → ℂ := fun s => cexp (-(σ : ℂ) * (s : ℂ) ^ 2) *
    suzukiSmoothFourier posBumpTest (-(s : ℂ)) with hG
  set H : ℝ → ℝ → ℂ := fun s t => (starRingEnd ℂ) (f t) * (cexp (I * (s : ℂ) * (t : ℂ)) * G s)
    with hH
  have hrw : ∀ s : ℝ, conjTransform f (s : ℂ) * cexp (-(σ : ℂ) * (s : ℂ) ^ 2) *
      suzukiSmoothFourier posBumpTest (-(s : ℂ)) = ∫ t : ℝ, H s t := by
    intro s
    rw [conjTransform, mul_assoc, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hH, hG]
    ring
  rw [lowFrequencyMass, integral_congr_ae (ae_of_all _ hrw)]
  have hbc : Continuous fun s : ℝ => suzukiSmoothFourier posBumpTest (-(s : ℂ)) :=
    (differentiable_suzukiSmoothFourier zero_le_one posBumpTest).continuous.comp (by fun_prop)
  have hGc : Continuous G := by simp only [hG]; exact (by fun_prop : Continuous fun s : ℝ =>
    cexp (-(σ : ℂ) * (s : ℂ) ^ 2)).mul hbc
  have hGle : ∀ s : ℝ, ‖G s‖ ≤ posBumpMass * Real.exp (-σ * s ^ 2) := by
    intro s
    simp only [hG]
    rw [norm_mul, norm_cexp_neg_ofReal_mul_sq]
    have h1 := norm_suzukiSmoothFourier_posBumpTest_le (-(s : ℂ))
    have h2 : |(-(s : ℂ)).im| = 0 := by simp
    rw [h2, Real.exp_zero, mul_one] at h1
    simp only [ofReal_re, ofReal_im]
    have : -(σ * (s ^ 2 - 0 ^ 2)) = -σ * s ^ 2 := by ring
    rw [this]
    calc Real.exp (-σ * s ^ 2) * ‖suzukiSmoothFourier posBumpTest (-(s : ℂ))‖
        ≤ Real.exp (-σ * s ^ 2) * posBumpMass := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = posBumpMass * Real.exp (-σ * s ^ 2) := mul_comm _ _
  have hint : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => (posBumpMass * Real.exp (-σ * p.1 ^ 2)) * ‖f p.2‖)
        (volume.prod volume) :=
      ((integrable_exp_neg_mul_sq hσ).const_mul posBumpMass).mul_prod hf.norm
    refine hdom.mono' ?_ (ae_of_all _ fun p => ?_)
    · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (starRingEnd ℂ) (f p.2))
          (volume.prod volume) := hf.aestronglyMeasurable.star.comp_snd
      have h2 : Continuous fun p : ℝ × ℝ => cexp (I * (p.1 : ℂ) * (p.2 : ℂ)) * G p.1 :=
        (by fun_prop : Continuous fun p : ℝ × ℝ => cexp (I * (p.1 : ℂ) * (p.2 : ℂ))).mul
          (hGc.comp continuous_fst)
      exact h1.mul h2.aestronglyMeasurable
    · obtain ⟨s, t⟩ := p
      simp only [Function.uncurry_apply_pair, hH, norm_mul, Complex.norm_conj]
      have h1 : ‖cexp (I * (s : ℂ) * (t : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [h1, one_mul]
      calc ‖f t‖ * ‖G s‖ ≤ ‖f t‖ * (posBumpMass * Real.exp (-σ * s ^ 2)) :=
            mul_le_mul_of_nonneg_left (hGle s) (norm_nonneg _)
        _ = posBumpMass * Real.exp (-σ * s ^ 2) * ‖f t‖ := by ring
  rw [integral_integral_swap hint, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [hH]
  rw [integral_const_mul]
  have := integral_cexp_mul_lowFrequencyWeight hσ t
  simp only [hG]
  rw [this]
  push_cast
  ring

/-! ## Symmetric-decreasing functions keep their mass near the centre -/

/-- `k_σ(t) ≥ b̂(0) e^{-(r+1)²/4σ}` for `|t| ≤ r`. -/
theorem lowFrequencyKernel_ge {σ r t : ℝ} (hσ : 0 < σ) (ht : |t| ≤ r) :
    posBumpMass * Real.exp (-((r + 1) ^ 2) / (4 * σ)) ≤ lowFrequencyKernel σ t := by
  rw [lowFrequencyKernel, posBumpMass, ← integral_mul_const]
  refine integral_mono (integrable_posBump.mul_const _) (integrable_lowFrequencyKernel_integrand hσ t)
    fun x => ?_
  by_cases hx : 1 < |x|
  · rw [posBump_eq_zero_of_one_lt_abs hx, zero_mul, zero_mul]
  · push Not at hx
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (posBump.nonneg' x)
    have htx : |t - x| ≤ r + 1 := (abs_sub _ _).trans (by linarith)
    have hsq : (t - x) ^ 2 ≤ (r + 1) ^ 2 := by
      rw [← sq_abs (t - x)]
      exact pow_le_pow_left₀ (abs_nonneg _) htx 2
    have h4 : 0 < 4 * σ := by positivity
    rw [div_le_div_iff_of_pos_right h4]
    linarith

/-- **Central mass of a symmetric-decreasing function.** If `g ≥ 0` is integrable, vanishes
outside `[-A, A]` and `g(t) ≤ g(s)` whenever `|s| ≤ |t|`, then for `0 < r` the mass in `[-r, r]` is
at least `r/(r + A)` of the total. -/
theorem integral_le_mul_setIntegral_of_symmDecreasing {g : ℝ → ℝ} {A r : ℝ} (hr : 0 < r)
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t) (hsupp : ∀ t, A < |t| → g t = 0)
    (hdec : ∀ s t, |s| ≤ |t| → g t ≤ g s) :
    r * ∫ t : ℝ, g t ≤ (r + A) * ∫ t in Icc (-r) r, g t := by
  have hA : 0 ≤ A ∨ A < 0 := le_or_gt 0 A
  have hsplit := integral_add_compl (measurableSet_Icc (a := -r) (b := r)) hg
  -- the outer part is at most `2A g(r)`
  have hout : ∫ t in (Icc (-r) r)ᶜ, g t ≤ max (2 * A) 0 * g r := by
    have hind : Integrable ((Icc (-A) A).indicator fun _ => g r) :=
      (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
    calc ∫ t in (Icc (-r) r)ᶜ, g t
        ≤ ∫ t in (Icc (-r) r)ᶜ, (Icc (-A) A).indicator (fun _ => g r) t := by
          refine setIntegral_mono_on hg.integrableOn hind.integrableOn measurableSet_Icc.compl
            fun t ht => ?_
          have hrt : r < |t| := by
            by_contra h
            push Not at h
            exact ht (abs_le.mp h)
          by_cases htA : |t| ≤ A
          · rw [indicator_of_mem (show t ∈ Icc (-A) A from abs_le.mp htA)]
            exact hdec r t (by rw [abs_of_pos hr]; exact hrt.le)
          · push Not at htA
            rw [hsupp t htA]
            exact indicator_nonneg (fun _ _ => hg0 r) t
      _ ≤ ∫ t, (Icc (-A) A).indicator (fun _ => g r) t :=
          setIntegral_le_integral hind (ae_of_all _ fun t => indicator_nonneg (fun _ _ => hg0 r) t)
      _ = max (2 * A) 0 * g r := by
          rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul]
          congr 2
          ring
  -- the inner part is at least `2r g(r)`
  have hin : 2 * r * g r ≤ ∫ t in Icc (-r) r, g t := by
    have h1 : ∫ t in Icc (-r) r, g r ≤ ∫ t in Icc (-r) r, g t := by
      refine setIntegral_mono_on continuous_const.integrableOn_Icc hg.integrableOn
        measurableSet_Icc fun t ht => ?_
      exact hdec t r (by rw [abs_of_pos hr]; exact abs_le.mpr ht)
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at h1
    linarith
  have hgr := hg0 r
  have hinner0 : 0 ≤ ∫ t in Icc (-r) r, g t := setIntegral_nonneg measurableSet_Icc fun t _ => hg0 t
  rcases hA with hA | hA
  · rw [max_eq_left (by linarith)] at hout
    -- `∫ g ≤ ∫_in + 2A g(r)` and `2r g(r) ≤ ∫_in`
    have h2 : r * (2 * A * g r) ≤ A * ∫ t in Icc (-r) r, g t := by nlinarith
    nlinarith
  · rw [max_eq_right (by linarith)] at hout
    have h0 : ∫ t in Icc (-r) r, g t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t _ =>
        hsupp t (lt_of_lt_of_le hA (abs_nonneg t))
    rw [h0] at hsplit ⊢
    have hle : ∫ t : ℝ, g t ≤ 0 := by linarith
    nlinarith

/-- **Low-frequency share of a symmetric-decreasing function.** If `f = g` is real, nonnegative,
vanishes outside `[-A, A]` and is symmetric-decreasing, then for `0 < r`
`√(π/σ) b̂(0) e^{-(r+1)²/4σ} · r ‖f‖₁ ≤ (r + A) |I_σ(F)|`. -/
theorem norm_lowFrequencyMass_ge {σ r A : ℝ} (hσ : 0 < σ) (hr : 0 < r) (hA : 0 ≤ A)
    {f : ℝ → ℂ} (hf : Integrable f) {g : ℝ → ℝ} (hfg : ∀ t, f t = (g t : ℂ))
    (hg0 : ∀ t, 0 ≤ g t) (hsupp : ∀ t, A < |t| → g t = 0)
    (hdec : ∀ s t, |s| ≤ |t| → g t ≤ g s) :
    Real.sqrt (Real.pi / σ) * (posBumpMass * Real.exp (-((r + 1) ^ 2) / (4 * σ))) *
        (r * ∫ t : ℝ, g t) ≤
      (r + A) * ‖lowFrequencyMass (conjTransform f) σ‖ := by
  have hnorm : ∀ t, ‖f t‖ = g t := fun t => by
    rw [hfg t, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 t)]
  have hg : Integrable g := hf.norm.congr (ae_of_all _ hnorm)
  set K : ℝ → ℝ := lowFrequencyKernel σ with hK
  have hKc : Continuous K := continuous_lowFrequencyKernel hσ
  have hgK : Integrable fun t => g t * K t := by
    refine (hg.mul_const posBumpMass).mono' (hg.aestronglyMeasurable.mul hKc.aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 t) (lowFrequencyKernel_nonneg σ t))]
    exact mul_le_mul_of_nonneg_left (lowFrequencyKernel_le hσ t) (hg0 t)
  -- the time-domain identity
  have hI : lowFrequencyMass (conjTransform f) σ =
      ((Real.sqrt (Real.pi / σ) * ∫ t : ℝ, g t * K t : ℝ) : ℂ) := by
    rw [lowFrequencyMass_conjTransform_eq hσ hf]
    have hpt : ∀ t, (starRingEnd ℂ) (f t) * ((lowFrequencyKernel σ t : ℝ) : ℂ) =
        ((g t * K t : ℝ) : ℂ) := fun t => by
      rw [hfg t, Complex.conj_ofReal, hK]; push_cast; ring
    rw [integral_congr_ae (ae_of_all _ hpt), integral_complex_ofReal]
    push_cast
    ring
  have hgK0 : 0 ≤ ∫ t : ℝ, g t * K t :=
    integral_nonneg fun t => mul_nonneg (hg0 t) (lowFrequencyKernel_nonneg σ t)
  have hIn : ‖lowFrequencyMass (conjTransform f) σ‖ =
      Real.sqrt (Real.pi / σ) * ∫ t : ℝ, g t * K t := by
    rw [hI, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- the kernel is large on `[-r, r]`
  set Kmin : ℝ := posBumpMass * Real.exp (-((r + 1) ^ 2) / (4 * σ)) with hKmin
  have hKmin0 : 0 ≤ Kmin := mul_nonneg posBumpMass_pos.le (Real.exp_pos _).le
  have hcentre : Kmin * ∫ t in Icc (-r) r, g t ≤ ∫ t : ℝ, g t * K t := by
    calc Kmin * ∫ t in Icc (-r) r, g t = ∫ t in Icc (-r) r, g t * Kmin := by
          rw [integral_mul_const, mul_comm]
      _ ≤ ∫ t in Icc (-r) r, g t * K t := by
          refine setIntegral_mono_on (hg.integrableOn.mul_const _) hgK.integrableOn measurableSet_Icc
            fun t ht => ?_
          exact mul_le_mul_of_nonneg_left (lowFrequencyKernel_ge hσ (abs_le.mpr ht)) (hg0 t)
      _ ≤ ∫ t : ℝ, g t * K t :=
          setIntegral_le_integral hgK (ae_of_all _ fun t =>
            mul_nonneg (hg0 t) (lowFrequencyKernel_nonneg σ t))
  have hmass := integral_le_mul_setIntegral_of_symmDecreasing hr hg hg0 hsupp hdec
  have hrA : 0 ≤ r + A := by linarith
  have hsq : 0 ≤ Real.sqrt (Real.pi / σ) := Real.sqrt_nonneg _
  rw [hIn]
  calc Real.sqrt (Real.pi / σ) * Kmin * (r * ∫ t : ℝ, g t)
      ≤ Real.sqrt (Real.pi / σ) * Kmin * ((r + A) * ∫ t in Icc (-r) r, g t) :=
        mul_le_mul_of_nonneg_left hmass (mul_nonneg hsq hKmin0)
    _ = (r + A) * (Real.sqrt (Real.pi / σ) * (Kmin * ∫ t in Icc (-r) r, g t)) := by ring
    _ ≤ (r + A) * (Real.sqrt (Real.pi / σ) * ∫ t : ℝ, g t * K t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcentre hsq) hrA

section Capstone

open GaloisForLFunctions.HTGeometry
open RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

/-- **Nonnegative symmetric-decreasing ground states force RH.** Let `u_j` be nonzero full ground
states of the restricted Weil form at apertures `a_j → ∞`, whose physical functions are real,
nonnegative and symmetric-decreasing (`f_j(t) ≤ f_j(s)` whenever `|s| ≤ |t|`). Then the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_fullGrounds_symmDecreasing
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hne : ∀ j, ccmArchimedeanFormToAperture (a j) (u j) ≠ 0)
    (hreal : ∀ j t, (timeRep (a j) (u j) t).im = 0)
    (hnonneg : ∀ j t, 0 ≤ (timeRep (a j) (u j) t).re)
    (hdec : ∀ j s t, |s| ≤ |t| → (timeRep (a j) (u j) t).re ≤ (timeRep (a j) (u j) s).re) :
    RiemannHypothesis := by
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (ha.eventually_ge_atTop 40)
  have ha' : Tendsto (fun j => (a (j + J)).1) atTop atTop :=
    ha.comp (tendsto_add_atTop_nat J)
  set P : ℝ := Real.sqrt Real.pi * posBumpMass * Real.exp (-1) with hP
  have hP0 : 0 < P := by
    have := posBumpMass_pos
    have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  refine riemannHypothesis_of_fullGrounds_lowFrequencyMass (M := 2 / P) (fun j => a (j + J)) ha'
    (fun j => u (j + J)) (fun j => hground _) (fun j => hne _) (fun j => ?_)
  set x : ℝ := (a (j + J)).1 with hx
  have hx40 : 40 ≤ x := hJ (j + J) (by omega)
  set f : ℝ → ℂ := timeRep (a (j + J)) (u (j + J)) with hf
  set g : ℝ → ℝ := fun t => (f t).re with hg
  have hfg : ∀ t, f t = (g t : ℂ) := fun t =>
    Complex.ext (by simp [hg]) (by simp [hg, hf, hreal (j + J) t])
  have hg0 : ∀ t, 0 ≤ g t := fun t => hnonneg (j + J) t
  have hsupp : ∀ t, x < |t| → g t = 0 := by
    intro t ht
    have hs := bound_support_of_supportedIn (supportedIn_timeRep (a (j + J)) (u (j + J)))
    by_contra h
    have hne0 : f t ≠ 0 := by
      intro h0
      apply h
      simp [hg, h0]
    have := hs t hne0
    linarith
  have hdec' : ∀ s t, |s| ≤ |t| → g t ≤ g s := fun s t h => hdec (j + J) s t h
  set σ : ℝ := x / 40 with hσdef
  have hσ1 : 1 ≤ σ := by rw [hσdef]; linarith
  have hσ : 0 < σ := by linarith
  set r : ℝ := Real.sqrt σ with hrdef
  have hr1 : 1 ≤ r := by rw [hrdef, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hσ1
  have hr0 : 0 < r := by linarith
  have hrsq : r ^ 2 = σ := Real.sq_sqrt hσ.le
  have hrx : r ≤ x := by nlinarith
  have hx0 : 0 ≤ x := by linarith
  have key := norm_lowFrequencyMass_ge hσ hr0 hx0 (integrable_timeRep _ _) hfg hg0 hsupp hdec'
  set Iv : ℝ := ‖lowFrequencyMass (conjTransform f) σ‖ with hIv
  have hN : ∫ t : ℝ, ‖timeRep (a (j + J)) (u (j + J)) t‖ = ∫ t : ℝ, g t := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    show ‖f t‖ = g t
    rw [hfg t, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 t)]
  rw [hN]
  set N : ℝ := ∫ t : ℝ, g t with hNdef
  have hN0 : 0 ≤ N := integral_nonneg hg0
  have hsr : Real.sqrt (Real.pi / σ) * r = Real.sqrt Real.pi := by
    rw [hrdef, ← Real.sqrt_mul (div_nonneg Real.pi_pos.le hσ.le)]
    congr 1
    field_simp
  have hexp : Real.exp (-1) ≤ Real.exp (-((r + 1) ^ 2) / (4 * σ)) := by
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hstep : P * N ≤ 2 * x * Iv := by
    have hIv0 : 0 ≤ Iv := norm_nonneg _
    calc P * N = Real.sqrt Real.pi * posBumpMass * Real.exp (-1) * N := by rw [hP]
      _ ≤ Real.sqrt Real.pi * posBumpMass * Real.exp (-((r + 1) ^ 2) / (4 * σ)) * N := by
          have := posBumpMass_pos
          have : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
          gcongr
      _ = Real.sqrt (Real.pi / σ) * (posBumpMass * Real.exp (-((r + 1) ^ 2) / (4 * σ))) *
            (r * N) := by rw [← hsr]; ring
      _ ≤ (r + x) * Iv := key
      _ ≤ 2 * x * Iv := mul_le_mul_of_nonneg_right (by linarith) hIv0
  have hxe : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hIv0 : 0 ≤ Iv := norm_nonneg _
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hP0]
  calc N * P = P * N := mul_comm _ _
    _ ≤ 2 * x * Iv := hstep
    _ ≤ 2 * Real.exp x * Iv := by gcongr

end Capstone

end

end RHTower
