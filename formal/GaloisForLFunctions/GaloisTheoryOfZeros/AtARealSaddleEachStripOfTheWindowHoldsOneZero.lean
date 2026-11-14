import GaloisForLFunctions.GaloisTheoryOfZeros.ASignedLoopOfSaddlesExchangesTheZerosOfTwoAdjacentStrips

/-!
# At a real saddle each strip of the window holds one zero

At a real saddle `σ` the time `τ(σ) = πe^{2σ}/σ` is real, and far out the bulk term is at most a
quarter of the saddle term (`|B₀| ≤ |Φ(0)|`, `|S₀| ≥ e^{7σ/2}`): the cosine term dominates.

**Theorem** (`exists_zero_mem_cosStrip`). Far out in the wide region, where `4|B₀| ≤ |S₀|`, each
strip of the window holds a zero.

**Theorem** (`exists_simplyJoined_to_cosineSide`). Far out, a zero of a strip of the window at a
real saddle is joined through simple zeros to a zero of the same strip at every saddle of the wide
region on the cosine side: along the real saddles to `Re a`, then up the vertical segment to `a`.

Proof. Minimum modulus on the disc of radius `1/2` around `θ + π/2`, where the model is
`B₀ − 2S₀ cos θ sin(ζ − θ − π/2)` and `|sin w| ≥ 9/20` on the circle. On the vertical segment
`|Q| = (64π⁴/Φ(0)²) e^{9σ + 2 Re f}/|2a − 1|` decreases in `η = Im a`:
`Re f = πe^{2σ}(cos 2η (σ − 1) − η sin 2η)` decreases and `|2a − 1|` increases, while the cosine
side is `1 ≤ (97/100)²|Q|`. Along both segments a zero of a strip stays in its strip.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The squared ratio and the cosine side -/

/-- `|Q(a)| = (64π⁴/Φ(0)²) e^{9σ + 2 Re f(a)}/|2a − 1|`. -/
theorem norm_saddleRatioSq_eq (a : ℂ) :
    ‖saddleRatioSq a‖ = 64 * π ^ 4 / ‖kernelC 0‖ ^ 2 *
      Real.exp (9 * a.re + 2 * (saddlePhaseValue a).re) / ‖2 * a - 1‖ := by
  have h1 : ‖-(64 * (π : ℂ) ^ 4)‖ = 64 * π ^ 4 := by
    rw [norm_neg, show (64 : ℂ) * (π : ℂ) ^ 4 = ((64 * π ^ 4 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : (9 * a + 2 * saddlePhaseValue a).re = 9 * a.re + 2 * (saddlePhaseValue a).re := by
    simp
  rw [saddleRatioSq, norm_div, norm_mul, norm_mul, norm_pow, h1, Complex.norm_exp, h2]
  ring

theorem WideRegion.two_mul_sub_one_ne_zero {a : ℂ} (h : WideRegion a) : 2 * a - 1 ≠ 0 := by
  intro h0
  have hre : (2 * a - 1).re = 2 * a.re - 1 := by simp
  rw [h0, Complex.zero_re] at hre
  linarith [h.1]

theorem WideRegion.bulkTerm_ne_zero {a : ℂ} (h : WideRegion a) : bulkTerm a ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le (mul_pos (norm_pos_iff.mpr kernelC_zero_ne_zero)
    (Real.exp_pos _)) h.le_norm_bulkTerm)

/-- `|2S₀|² = |Q||B₀|²`. -/
theorem norm_two_mul_saddleTerm_sq {a : ℂ} (h : WideRegion a) :
    ‖2 * saddleTerm a‖ ^ 2 = ‖saddleRatioSq a‖ * ‖bulkTerm a‖ ^ 2 := by
  have e := congrArg norm (two_mul_saddleTerm_sq h.ne_zero h.two_mul_sub_one_ne_zero)
  simp only [norm_pow, norm_mul] at e ⊢
  exact e

/-- **The cosine side passes to a saddle with a larger squared ratio.** The cosine side is
`1 ≤ (97/100)²|Q|`. -/
theorem cosineSide_of_norm_saddleRatioSq_le {a a' : ℂ} (ha : WideRegion a) (ha' : WideRegion a')
    (h' : CosineSide a') (hQ : ‖saddleRatioSq a'‖ ≤ ‖saddleRatioSq a‖) : CosineSide a := by
  have hB2 : 0 < ‖bulkTerm a'‖ ^ 2 := by
    have := norm_pos_iff.mpr ha'.bulkTerm_ne_zero
    positivity
  have h1 : ‖bulkTerm a'‖ ^ 2 ≤ (97 / 100) ^ 2 * ‖2 * saddleTerm a'‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) h' 2
    rwa [mul_pow] at h
  rw [norm_two_mul_saddleTerm_sq ha'] at h1
  have h2 : 1 ≤ (97 / 100) ^ 2 * ‖saddleRatioSq a'‖ := by
    by_contra hcon
    push Not at hcon
    have h3 := mul_pos (sub_pos.mpr hcon) hB2
    nlinarith
  have h4 : 1 ≤ (97 / 100) ^ 2 * ‖saddleRatioSq a‖ :=
    h2.trans (mul_le_mul_of_nonneg_left hQ (by norm_num))
  have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖bulkTerm a‖)
  have h6 : ‖bulkTerm a‖ ^ 2 ≤ (97 / 100 * ‖2 * saddleTerm a‖) ^ 2 := by
    rw [mul_pow, norm_two_mul_saddleTerm_sq ha]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h6

/-- Where `4|B₀| ≤ |S₀|` the cosine term dominates. -/
theorem cosineSide_of_dominance {a : ℂ} (h : 4 * ‖bulkTerm a‖ ≤ ‖saddleTerm a‖) :
    CosineSide a := by
  unfold CosineSide
  rw [norm_mul, Complex.norm_ofNat]
  linarith [norm_nonneg (bulkTerm a)]

/-! ## Up a vertical segment the squared ratio decreases -/

theorem re_saddlePhaseValue_le_of_im_le {σ η η' : ℝ} (hσ : 1 ≤ σ) (h0 : 0 ≤ η) (hη : η ≤ η')
    (hη' : η' ≤ π / 4) :
    (saddlePhaseValue ((σ : ℂ) + η' * I)).re ≤ (saddlePhaseValue ((σ : ℂ) + η * I)).re := by
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t => by simp
  have him : ∀ t : ℝ, ((σ : ℂ) + t * I).im = t := fun t => by simp
  have hπ := Real.pi_pos
  rw [saddlePhaseValue_re, saddlePhaseValue_re, hre, hre, him, him]
  have hc : Real.cos (2 * η') ≤ Real.cos (2 * η) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hs : Real.sin (2 * η) ≤ Real.sin (2 * η') :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hs0 : 0 ≤ Real.sin (2 * η) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have h1 := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ σ - 1)
  have h2 := mul_le_mul hs hη h0 (hs0.trans hs)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith

theorem norm_two_mul_sub_one_le_of_im_le {σ η η' : ℝ} (h0 : 0 ≤ η) (hη : η ≤ η') :
    ‖2 * ((σ : ℂ) + η * I) - 1‖ ≤ ‖2 * ((σ : ℂ) + η' * I) - 1‖ := by
  have e : ∀ t : ℝ, 2 * ((σ : ℂ) + t * I) - 1 = ((2 * σ - 1 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    intro t
    push_cast
    ring
  rw [e, e, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]
  nlinarith [mul_le_mul hη hη h0 (h0.trans hη)]

/-- `|Q(σ + iη)|` decreases in `η ∈ [0, π/4]`. -/
theorem norm_saddleRatioSq_le_of_im_le {σ η η' : ℝ} (hσ : 1 ≤ σ) (h0 : 0 ≤ η) (hη : η ≤ η')
    (hη' : η' ≤ π / 4) :
    ‖saddleRatioSq ((σ : ℂ) + η' * I)‖ ≤ ‖saddleRatioSq ((σ : ℂ) + η * I)‖ := by
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t => by simp
  rw [norm_saddleRatioSq_eq, norm_saddleRatioSq_eq, hre, hre]
  have hf := re_saddlePhaseValue_le_of_im_le hσ h0 hη hη'
  have hn := norm_two_mul_sub_one_le_of_im_le (σ := σ) h0 hη
  have hn0 : 0 < ‖2 * ((σ : ℂ) + η * I) - 1‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have hre2 : (2 * ((σ : ℂ) + η * I) - 1).re = 2 * σ - 1 := by simp
    rw [h, Complex.zero_re] at hre2
    linarith
  have hc : 0 < 64 * π ^ 4 / ‖kernelC 0‖ ^ 2 := by
    have := norm_pos_iff.mpr kernelC_zero_ne_zero
    positivity
  have hE : Real.exp (9 * σ + 2 * (saddlePhaseValue ((σ : ℂ) + η' * I)).re) ≤
      Real.exp (9 * σ + 2 * (saddlePhaseValue ((σ : ℂ) + η * I)).re) :=
    Real.exp_le_exp.mpr (by linarith)
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hE hc.le) hn0 hn

/-! ## Real saddles -/

/-- The time of a real saddle: `τ(σ) = πe^{2σ}/σ`. -/
def realSaddleTime (σ : ℝ) : ℝ := π * Real.exp (2 * σ) / σ

theorem saddleTime_ofReal (σ : ℝ) : saddleTime (σ : ℂ) = (realSaddleTime σ : ℂ) := by
  simp [saddleTime, saddleP, realSaddleTime]

theorem eighth_le_realSaddleTime {σ : ℝ} (hσ : 1 ≤ σ) : 1 / 8 ≤ realSaddleTime σ := by
  rw [realSaddleTime, le_div_iff₀ (by linarith)]
  have h := Real.add_one_le_exp (2 * σ)
  have h2 := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos (2 * σ)).le
  linarith

theorem wideRegion_ofReal {σ : ℝ} (hσ : 50 ≤ σ) : WideRegion (σ : ℂ) := by
  refine ⟨by simpa using hσ, by simp, ?_⟩
  simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  have h1 : 1 / (4 * σ) ≤ 1 / 200 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith [Real.pi_gt_three]

/-- **Far out at a real saddle the bulk term is at most a quarter of the saddle term.** -/
theorem exists_real_dominance : ∃ σ₁ : ℝ, 50 ≤ σ₁ ∧ ∀ σ : ℝ, σ₁ ≤ σ →
    4 * ‖bulkTerm (σ : ℂ)‖ ≤ ‖saddleTerm (σ : ℂ)‖ := by
  refine ⟨max 50 (Real.log (4 * ‖kernelC 0‖)), le_max_left _ _, fun σ hσ => ?_⟩
  have h50 : 50 ≤ σ := (le_max_left _ _).trans hσ
  have hlog : Real.log (4 * ‖kernelC 0‖) ≤ σ := (le_max_right _ _).trans hσ
  have hW := wideRegion_ofReal h50
  have hB := hW.norm_bulkTerm_le
  have hS := hW.le_norm_saddleTerm
  have hf := hW.phase_re_nonneg (by norm_num)
  have hK : 0 < 4 * ‖kernelC 0‖ := by
    have := norm_pos_iff.mpr kernelC_zero_ne_zero
    positivity
  have h1 : 4 * ‖kernelC 0‖ ≤
      Real.exp (7 * (σ : ℂ).re / 2 + (saddlePhaseValue (σ : ℂ)).re) := by
    rw [Complex.ofReal_re]
    calc 4 * ‖kernelC 0‖ = Real.exp (Real.log (4 * ‖kernelC 0‖)) := (Real.exp_log hK).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

/-! ## A zero in each strip -/

/-- `|sin w| ≥ 9/20` on the circle `|w| = 1/2`. -/
theorem le_norm_sin_of_norm_eq_half {w : ℂ} (hw : ‖w‖ = 1 / 2) : 9 / 20 ≤ ‖Complex.sin w‖ := by
  have hsin := Complex.sin_bound (x := w) (by rw [hw]; norm_num)
  have h3 : ‖w ^ 3 / 6‖ = 1 / 48 := by
    rw [norm_div, norm_pow, hw, Complex.norm_ofNat]
    norm_num
  have h5 : ‖w‖ ^ 5 / 100 = 1 / 3200 := by
    rw [hw]
    norm_num
  rw [h5] at hsin
  have e : w = Complex.sin w - (Complex.sin w - (w - w ^ 3 / 6)) + w ^ 3 / 6 := by ring
  have h1 : ‖w‖ ≤ ‖Complex.sin w‖ + ‖Complex.sin w - (w - w ^ 3 / 6)‖ + ‖w ^ 3 / 6‖ := by
    calc ‖w‖ = ‖Complex.sin w - (Complex.sin w - (w - w ^ 3 / 6)) + w ^ 3 / 6‖ := by rw [← e]
      _ ≤ ‖Complex.sin w - (Complex.sin w - (w - w ^ 3 / 6))‖ + ‖w ^ 3 / 6‖ := norm_add_le _ _
      _ ≤ ‖Complex.sin w‖ + ‖Complex.sin w - (w - w ^ 3 / 6)‖ + ‖w ^ 3 / 6‖ := by
          gcongr
          exact norm_sub_le _ _
  rw [hw, h3] at h1
  linarith

/-- `cos(θ + π/2 + w) = −cos θ sin w` for `θ ∈ πℤ`. -/
theorem cos_add_pi_div_two_add {θ : ℝ} (hθ : Real.sin θ = 0) (w : ℂ) :
    Complex.cos ((θ : ℂ) + ((π / 2 : ℝ) : ℂ) + w) = -(Real.cos θ : ℂ) * Complex.sin w := by
  have hs : Complex.sin (θ : ℂ) = 0 := by rw [← Complex.ofReal_sin, hθ, Complex.ofReal_zero]
  have e : (θ : ℂ) + ((π / 2 : ℝ) : ℂ) + w = ((θ : ℂ) + w) + (π : ℂ) / 2 := by
    push_cast
    ring
  rw [e, Complex.cos_add_pi_div_two, Complex.sin_add, hs, zero_mul, zero_add, Complex.ofReal_cos]
  ring

/-- **A zero in each strip.** Far out in the wide region, where `4|B₀| ≤ |S₀|`, each strip of the
window holds a zero: by the minimum modulus principle on the disc of radius `1/2` around
`θ + π/2`, where the model is `B₀ − 2S₀ cos θ sin(ζ − θ − π/2)`. -/
theorem exists_zero_mem_cosStrip (R : ℝ) : ∃ σ₀ : ℝ, ∀ a : ℂ, WideRegion a → σ₀ ≤ a.re →
    4 * ‖bulkTerm a‖ ≤ ‖saddleTerm a‖ → ∀ θ : ℝ, Real.sin θ = 0 → |θ| + π + 2 ≤ R →
    ∃ z : ℂ, complexHeat (saddleTime a) z = 0 ∧ a * z ∈ cosStrip θ := by
  obtain ⟨σ₀, hσ₀⟩ := exists_forall_norm_complexHeat_sub_wide_model_le R (ε := 1 / 100)
    (by norm_num)
  refine ⟨σ₀, fun a ha hσ hdom θ hθ hθR => ?_⟩
  have hπ := Real.pi_gt_three
  have ha0 := ha.ne_zero
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hS : 0 < ‖saddleTerm a‖ := lt_of_lt_of_le (Real.exp_pos _) ha.le_norm_saddleTerm
  have hB := norm_nonneg (bulkTerm a)
  have hcθ := norm_ofReal_cos_eq_one hθ
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (θ : ℂ) + ((π / 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hcn : ‖c‖ ≤ |θ| + π / 2 := by
    rw [hc]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < π / 2)]
  have hscale : ∀ z : ℂ, a * z / a = z := fun z => mul_div_cancel_left₀ z ha0
  -- the model around the centre
  have hmodel : ∀ ζ : ℂ, ‖ζ - c‖ ≤ 1 / 2 →
      ‖complexHeat (saddleTime a) (ζ / a) -
        (bulkTerm a - 2 * saddleTerm a * (Real.cos θ : ℂ) * Complex.sin (ζ - c))‖ ≤
        1 / 100 * (‖bulkTerm a‖ + ‖saddleTerm a‖) := by
    intro ζ hζ
    have h1 := hσ₀ a ha hσ ζ (by
      have h2 := norm_add_le (ζ - c) c
      rw [sub_add_cancel] at h2
      linarith)
    have e : Complex.cos ζ = -(Real.cos θ : ℂ) * Complex.sin (ζ - c) := by
      rw [← cos_add_pi_div_two_add hθ, ← hc, add_sub_cancel]
    rw [e] at h1
    have e2 : complexHeat (saddleTime a) (ζ / a) - bulkTerm a -
        2 * saddleTerm a * (-(Real.cos θ : ℂ) * Complex.sin (ζ - c)) =
        complexHeat (saddleTime a) (ζ / a) -
          (bulkTerm a - 2 * saddleTerm a * (Real.cos θ : ℂ) * Complex.sin (ζ - c)) := by ring
    rwa [e2] at h1
  have hshift : ∀ z : ℂ, a * z - c = a * (z - c / a) := by
    intro z
    rw [mul_sub, mul_div_cancel₀ _ ha0]
  obtain ⟨z₀, hz₀r, hz₀⟩ := RigidArithmeticOfCuts.exists_zero_of_norm_center_lt
    (differentiable_complexHeat (saddleTime a)) (c := c / a) (r := 1 / 2 / ‖a‖)
    (μ := ‖saddleTerm a‖ / 2) (div_pos (by norm_num) han) (by positivity) (by
      have h1 := hmodel c (by rw [sub_self, norm_zero]; norm_num)
      rw [sub_self, Complex.sin_zero, mul_zero, sub_zero] at h1
      have h2 := norm_sub_norm_le (complexHeat (saddleTime a) (c / a)) (bulkTerm a)
      linarith) (by
      intro z hz
      have hw : ‖a * z - c‖ = 1 / 2 := by
        rw [hshift, norm_mul, hz, mul_div_cancel₀ _ han.ne']
      have h1 := hmodel (a * z) hw.le
      rw [hscale] at h1
      have hsin := le_norm_sin_of_norm_eq_half hw
      have h2 : ‖2 * saddleTerm a * (Real.cos θ : ℂ) * Complex.sin (a * z - c)‖ =
          2 * ‖saddleTerm a‖ * ‖Complex.sin (a * z - c)‖ := by
        rw [norm_mul, norm_mul, norm_mul, hcθ, Complex.norm_ofNat, mul_one]
      have h3 := norm_sub_norm_le (bulkTerm a -
        2 * saddleTerm a * (Real.cos θ : ℂ) * Complex.sin (a * z - c))
        (complexHeat (saddleTime a) z)
      rw [norm_sub_rev _ (complexHeat (saddleTime a) z)] at h3
      have h4 := norm_sub_norm_le (2 * saddleTerm a * (Real.cos θ : ℂ) * Complex.sin (a * z - c))
        (bulkTerm a)
      rw [norm_sub_rev, h2] at h4
      have h5 : 2 * ‖saddleTerm a‖ * (9 / 20) ≤ 2 * ‖saddleTerm a‖ * ‖Complex.sin (a * z - c)‖ :=
        mul_le_mul_of_nonneg_left hsin (by positivity)
      linarith)
  refine ⟨z₀, hz₀, ?_⟩
  have hd : ‖a * z₀ - c‖ < 1 / 2 := by
    rw [hshift, norm_mul]
    rw [lt_div_iff₀ han] at hz₀r
    linarith [mul_comm ‖a‖ ‖z₀ - c / a‖]
  have e : a * z₀ - (θ : ℂ) - ((π / 2 : ℝ) : ℂ) = a * z₀ - c := by
    rw [hc]
    ring
  exact mem_cosStrip_of_norm_sub_le (c := π / 2) (r := 1 / 2) (by rw [e]; exact hd.le)
    (by linarith) (by linarith) (by norm_num)

/-! ## From a real saddle to a saddle of the cosine side -/

/-- The clamp of `ℝ` onto `[0, 1]`. -/
def clampUnit (s : ℝ) : ℝ := max 0 (min s 1)

theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clampUnit_nonneg (s : ℝ) : 0 ≤ clampUnit s := le_max_left _ _

theorem clampUnit_le_one (s : ℝ) : clampUnit s ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem clampUnit_zero : clampUnit 0 = 0 := by
  rw [clampUnit, min_eq_left zero_le_one, max_self]

theorem clampUnit_one : clampUnit 1 = 1 := by
  rw [clampUnit, min_self, max_eq_right zero_le_one]

/-- The real saddles from `σ` to `σ'`. -/
def realSaddlePath (σ σ' : ℝ) (s : ℝ) : ℂ := ((σ + clampUnit s * (σ' - σ) : ℝ) : ℂ)

/-- The vertical segment of saddles from `Re a` up to `a`. -/
def verticalSaddlePath (a : ℂ) (s : ℝ) : ℂ := (a.re : ℂ) + ((clampUnit s * a.im : ℝ) : ℂ) * I

theorem continuous_realSaddlePath (σ σ' : ℝ) : Continuous (realSaddlePath σ σ') :=
  Complex.continuous_ofReal.comp (continuous_const.add (continuous_clampUnit.mul continuous_const))

theorem continuous_verticalSaddlePath (a : ℂ) : Continuous (verticalSaddlePath a) :=
  continuous_const.add
    ((Complex.continuous_ofReal.comp (continuous_clampUnit.mul continuous_const)).mul
      continuous_const)

theorem realSaddlePath_zero (σ σ' : ℝ) : realSaddlePath σ σ' 0 = (σ : ℂ) := by
  rw [realSaddlePath, clampUnit_zero, zero_mul, add_zero]

theorem realSaddlePath_one (σ σ' : ℝ) : realSaddlePath σ σ' 1 = (σ' : ℂ) := by
  rw [realSaddlePath, clampUnit_one, one_mul, add_sub_cancel]

theorem verticalSaddlePath_zero (a : ℂ) : verticalSaddlePath a 0 = (a.re : ℂ) := by
  rw [verticalSaddlePath, clampUnit_zero, zero_mul, Complex.ofReal_zero, zero_mul, add_zero]

theorem verticalSaddlePath_one (a : ℂ) : verticalSaddlePath a 1 = a := by
  rw [verticalSaddlePath, clampUnit_one, one_mul, Complex.re_add_im]

/-- **The saddles from a real saddle to the cosine side carry the strip facts.** Far out, for a
real saddle `σ` and a saddle `a` of the wide region on the cosine side: the real saddles from `σ`
to `Re a`, where `4|B₀| ≤ |S₀|`, and the vertical segment up to `a`, where `|Q|` is at least
`|Q(a)|`, lie in the wide region and have the strip facts. -/
theorem exists_stripFacts_to_cosineSide (R : ℝ) : ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
    ∀ a : ℂ, WideRegion a → σ₀ ≤ a.re → CosineSide a →
    (∀ s, WideRegion (realSaddlePath σ a.re s)) ∧ (∀ s, StripFacts R (realSaddlePath σ a.re s)) ∧
      (∀ s, WideRegion (verticalSaddlePath a s)) ∧ ∀ s, StripFacts R (verticalSaddlePath a s) := by
  obtain ⟨σ₁, h50, hdom⟩ := exists_real_dominance
  obtain ⟨σ₂, hfacts⟩ := exists_stripFacts R
  refine ⟨max σ₁ σ₂, fun σ hσ a ha haσ hside => ?_⟩
  have hσ₁ : σ₁ ≤ σ := (le_max_left _ _).trans hσ
  have hσ₂ : σ₂ ≤ σ := (le_max_right _ _).trans hσ
  have haσ₁ : σ₁ ≤ a.re := (le_max_left _ _).trans haσ
  have haσ₂ : σ₂ ≤ a.re := (le_max_right _ _).trans haσ
  -- the real saddles
  have hlow : ∀ s, σ₁ ≤ σ + clampUnit s * (a.re - σ) ∧ σ₂ ≤ σ + clampUnit s * (a.re - σ) := by
    intro s
    have h0 := clampUnit_nonneg s
    have h1 := clampUnit_le_one s
    have e : σ + clampUnit s * (a.re - σ) =
        (1 - clampUnit s) * σ + clampUnit s * a.re := by ring
    rw [e]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hσ₁),
        mul_nonneg h0 (sub_nonneg.mpr haσ₁)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hσ₂),
        mul_nonneg h0 (sub_nonneg.mpr haσ₂)]
  have hWr : ∀ s, WideRegion (realSaddlePath σ a.re s) := fun s =>
    wideRegion_ofReal (h50.trans (hlow s).1)
  have hFr : ∀ s, StripFacts R (realSaddlePath σ a.re s) := fun s =>
    hfacts _ (hWr s) (by rw [realSaddlePath, Complex.ofReal_re]; exact (hlow s).2)
      (cosineSide_of_dominance (hdom _ (hlow s).1))
  -- the vertical segment
  have hη0 := ha.2.1
  have hηπ := ha.im_lt
  have hσ1 : 1 ≤ a.re := by linarith [ha.1]
  have hre : ∀ s, (verticalSaddlePath a s).re = a.re := fun s => by simp [verticalSaddlePath]
  have him : ∀ s, (verticalSaddlePath a s).im = clampUnit s * a.im := fun s => by
    simp [verticalSaddlePath]
  have hle : ∀ s, clampUnit s * a.im ≤ a.im := fun s =>
    mul_le_of_le_one_left hη0 (clampUnit_le_one s)
  have hge : ∀ s, 0 ≤ clampUnit s * a.im := fun s => mul_nonneg (clampUnit_nonneg s) hη0
  have hWv : ∀ s, WideRegion (verticalSaddlePath a s) := fun s => by
    refine ⟨by rw [hre]; exact ha.1, by rw [him]; exact hge s, ?_⟩
    rw [hre, him]
    linarith [ha.2.2, hle s]
  refine ⟨hWr, hFr, hWv, fun s => ?_⟩
  refine hfacts _ (hWv s) (by rw [hre]; exact haσ₂)
    (cosineSide_of_norm_saddleRatioSq_le (hWv s) ha hside ?_)
  have e : verticalSaddlePath a s = (a.re : ℂ) + ((clampUnit s * a.im : ℝ) : ℂ) * I := rfl
  conv_lhs => rw [← Complex.re_add_im a]
  rw [e]
  exact norm_saddleRatioSq_le_of_im_le hσ1 (hge s) (hle s) hηπ.le

/-- **A zero of a strip at a real saddle reaches the cosine side.** Far out, a zero of
`H_{τ(σ)}` in a strip of the window is joined through simple zeros to a zero of `H_{τ(a)}` in the
same open strip, for every saddle `a` of the wide region on the cosine side: along the real saddles
from `σ` to `Re a` and up the vertical segment to `a`. -/
theorem exists_simplyJoined_to_cosineSide (R : ℝ) : ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
    ∀ a : ℂ, WideRegion a → σ₀ ≤ a.re → CosineSide a → ∀ θ : ℝ, Real.sin θ = 0 →
    |θ| + π + 2 ≤ R → ∀ z : ℂ, complexHeat (saddleTime (σ : ℂ)) z = 0 →
    (σ : ℂ) * z ∈ cosStrip θ → ∃ z' : ℂ, SimplyJoined (saddleTime (σ : ℂ)) z (saddleTime a) z' ∧
      complexHeat (saddleTime a) z' = 0 ∧ a * z' ∈ openCosStrip θ := by
  obtain ⟨σ₀, h₀⟩ := exists_stripFacts_to_cosineSide R
  refine ⟨σ₀, fun σ hσ a ha haσ hside θ hθ hθR z hz hzθ => ?_⟩
  obtain ⟨hWr, hFr, hWv, hFv⟩ := h₀ σ hσ a ha haσ hside
  obtain ⟨z₁, hj₁, hz₁, hd₁⟩ := exists_simplyJoined_of_stripFacts
    (continuous_realSaddlePath σ a.re) hWr hFr hθ hθR (z₀ := z)
    (by rw [realSaddlePath_zero]; exact hz) (by rw [realSaddlePath_zero]; exact hzθ)
  rw [realSaddlePath_zero, realSaddlePath_one] at hj₁
  rw [realSaddlePath_one] at hz₁ hd₁
  obtain ⟨z₂, hj₂, hz₂, hd₂⟩ := exists_simplyJoined_of_stripFacts
    (continuous_verticalSaddlePath a) hWv hFv hθ hθR (z₀ := z₁)
    (by rw [verticalSaddlePath_zero]; exact hz₁)
    (by rw [verticalSaddlePath_zero]; exact openCosStrip_subset θ hd₁)
  rw [verticalSaddlePath_zero, verticalSaddlePath_one] at hj₂
  rw [verticalSaddlePath_one] at hz₂ hd₂
  exact ⟨z₂, hj₁.trans hj₂, hz₂, hd₂⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
