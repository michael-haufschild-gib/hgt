import GaloisForLFunctions.RHTower.Sieve.UnitBlockPoissonKernel
import GaloisForLFunctions.HTGeometry.MonotonePhaseFirstDerivativeTest

/-!
# Bounds for the Fourier coefficients of the smoothed unit block

The coefficient `ubFreq N N' t k = ∫_N^{N'+1} φ(x) x^{-1} e^{iΘ_k(x)} dx`, `Θ_k = 2πkx − t log x`,
has a monotone phase derivative `Θ_k' = 2πk − t/x`.  Two estimates follow from the tests of
`MonotonePhaseFirstDerivativeTest`, with the amplitude `φ(x)/x` of size `1/N` and variation `3/N`:

* **non-stationary:** if `|2πk − t/x| ≥ λ` on `[N, N' + 1]` then `‖ubFreq k‖ ≤ 4/(Nλ)`
  (`norm_ubFreq_le_of_nonstationary`);
* **stationary:** if `k ≥ 1`, `k > t/(2π(N'+1)) − 1`, `1 ≤ t ≤ N²` and `N' ≤ 2N`, then
  `‖ubFreq k‖ ≤ 218/√t` (`norm_ubFreq_le_stationary`).

The same second-derivative test bounds the model integral
`ubJ t = ∫_{3/4}^{5/4} ψ(y) y^{-1} e^{it(y − log y)} dy` by `23/√t` (`norm_ubJ_le`); it carries the
common factor of every reflected frequency.
-/

open Complex Set MeasureTheory intervalIntegral
open GaloisForLFunctions.HTGeometry
open scoped Real

namespace RHTower.Sieve

noncomputable section

/-! ## Amplitudes `w(x)/x` -/

theorem hasDerivAt_div_self {w : ℝ → ℝ} {w' x : ℝ} (hw : HasDerivAt w w' x) (hx : x ≠ 0) :
    HasDerivAt (fun y => w y / y) (w' / x - w x / x ^ 2) x := by
  refine (hw.div (hasDerivAt_id' x) hx).congr_deriv ?_
  field_simp

/-- `∫_u^v 1/x² ≤ 1/u`. -/
theorem intervalIntegral_one_div_sq_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∫ x in u..v, 1 / x ^ 2 ≤ 1 / u := by
  have hpos : ∀ x ∈ uIcc u v, 0 < x := fun x hx => by
    rw [uIcc_of_le huv] at hx; linarith [hx.1]
  have hF : ∀ x ∈ uIcc u v, HasDerivAt (fun y => -(1 / y)) (1 / x ^ 2) x := by
    intro x hx
    have h := ((hasDerivAt_id' x).inv (hpos x hx).ne').neg
    refine (h.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun y => by simp [one_div]
  have hc : ContinuousOn (fun x : ℝ => 1 / x ^ 2) (uIcc u v) :=
    continuousOn_const.div (continuousOn_id.pow 2) fun x hx => pow_ne_zero 2 (hpos x hx).ne'
  rw [integral_eq_sub_of_hasDerivAt hF hc.intervalIntegrable]
  have : 0 < 1 / v := by have := hu.trans_le huv; positivity
  linarith

/-- The variation of an amplitude `w(x)/x` with `|w| ≤ 1`. -/
theorem integral_abs_deriv_div_self_le {w w' : ℝ → ℝ} {u v W : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hwc : ContinuousOn w (Icc u v)) (hw'c : ContinuousOn w' (Icc u v))
    (hw1 : ∀ x ∈ Icc u v, |w x| ≤ 1) (hW : ∫ x in u..v, |w' x| ≤ W) :
    ∫ x in u..v, |w' x / x - w x / x ^ 2| ≤ W / u + 1 / u := by
  have hpos : ∀ x ∈ Icc u v, 0 < x := fun x hx => hu.trans_le hx.1
  have hc1 : ContinuousOn (fun x => |w' x / x - w x / x ^ 2|) (Icc u v) :=
    ((hw'c.div continuousOn_id fun x hx => (hpos x hx).ne').sub
      (hwc.div (continuousOn_id.pow 2) fun x hx => pow_ne_zero 2 (hpos x hx).ne')).abs
  have hc2 : ContinuousOn (fun x => |w' x| / u + 1 / x ^ 2) (Icc u v) :=
    (hw'c.abs.div_const u).add (continuousOn_const.div (continuousOn_id.pow 2)
      fun x hx => pow_ne_zero 2 (hpos x hx).ne')
  have hmono : ∫ x in u..v, |w' x / x - w x / x ^ 2| ≤ ∫ x in u..v, (|w' x| / u + 1 / x ^ 2) := by
    refine integral_mono_on huv (hc1.intervalIntegrable_of_Icc huv)
      (hc2.intervalIntegrable_of_Icc huv) fun x hx => ?_
    have hx0 := hpos x hx
    refine le_trans (abs_sub _ _) (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos hx0]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hu hx.1
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
      exact div_le_div_of_nonneg_right (hw1 x hx) (by positivity)
  have hi1 : IntervalIntegrable (fun x => |w' x| / u) volume u v :=
    (hw'c.abs.div_const u).intervalIntegrable_of_Icc huv
  have hi2 : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume u v :=
    (continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
      pow_ne_zero 2 (hpos x hx).ne').intervalIntegrable_of_Icc huv
  rw [integral_add hi1 hi2, intervalIntegral.integral_div] at hmono
  have h1 : (∫ x in u..v, |w' x|) / u ≤ W / u := div_le_div_of_nonneg_right hW hu.le
  have h2 := intervalIntegral_one_div_sq_le hu huv
  linarith

/-- **First-derivative test with a real amplitude `w(x)/x`.**  If `|w| ≤ 1`, `w` vanishes at both
ends, `∫|w'| ≤ W`, and the phase has `Θ'' ≥ 0`, `|Θ'| ≥ λ` on `[u, v] ⊂ (0, ∞)`, then
`‖∫_u^v (w(x)/x) e^{iΘ}‖ ≤ (W + 2)/(uλ)`. -/
theorem norm_integral_div_self_mul_exp_le {w w' : ℝ → ℝ} {Θ Θ' Θ'' : ℝ → ℝ}
    {u v lam W : ℝ} (hu : 0 < u) (huv : u ≤ v) (hlam : 0 < lam)
    (hw : ∀ x ∈ Icc u v, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Icc u v))
    (hw1 : ∀ x ∈ Icc u v, |w x| ≤ 1) (hW : ∫ x in u..v, |w' x| ≤ W)
    (hwu : w u = 0) (hwv : w v = 0)
    (hΘ : ∀ x ∈ Icc u v, HasDerivAt Θ (Θ' x) x)
    (hΘ' : ∀ x ∈ Icc u v, HasDerivAt Θ' (Θ'' x) x) (hΘ'' : ContinuousOn Θ'' (Icc u v))
    (hpos : ∀ x ∈ Icc u v, 0 ≤ Θ'' x) (hlow : ∀ x ∈ Icc u v, lam ≤ |Θ' x|) :
    ‖∫ x in u..v, ((w x / x : ℝ) : ℂ) * Complex.exp ((Θ x : ℂ) * I)‖ ≤ (W + 2) / (u * lam) := by
  have hxpos : ∀ x ∈ Icc u v, 0 < x := fun x hx => hu.trans_le hx.1
  have hwc : ContinuousOn w (Icc u v) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hg : ∀ x ∈ Icc u v, HasDerivAt (fun y => ((w y / y : ℝ) : ℂ))
      (((w' x / x - w x / x ^ 2 : ℝ) : ℂ)) x :=
    fun x hx => (hasDerivAt_div_self (hw x hx) (hxpos x hx).ne').ofReal_comp
  have hg'c : ContinuousOn (fun x => ((w' x / x - w x / x ^ 2 : ℝ) : ℂ)) (Icc u v) :=
    Complex.continuous_ofReal.comp_continuousOn ((hw'c.div continuousOn_id fun x hx =>
      (hxpos x hx).ne').sub (hwc.div (continuousOn_id.pow 2) fun x hx =>
        pow_ne_zero 2 (hxpos x hx).ne'))
  have hG : ∀ x ∈ Icc u v, ‖((w x / x : ℝ) : ℂ)‖ ≤ 1 / u := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (hxpos x hx)]
    exact le_trans (div_le_div_of_nonneg_right (hw1 x hx) (hxpos x hx).le)
      (div_le_div_of_nonneg_left zero_le_one hu hx.1)
  have hV : ∫ x in u..v, ‖((w' x / x - w x / x ^ 2 : ℝ) : ℂ)‖ ≤ W / u + 1 / u := by
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact integral_abs_deriv_div_self_le hu huv hwc hw'c hw1 hW
  have h := norm_integral_mul_exp_le_of_monotone_phase huv hlam hg hg'c hΘ hΘ' hΘ'' hpos hlow hG hV
  rw [hwu, hwv, zero_div, Complex.ofReal_zero, norm_zero, zero_div, Complex.ofReal_zero,
    norm_zero] at h
  refine le_trans h (le_of_eq ?_)
  field_simp
  ring

/-- **Second-derivative test with a real amplitude `w(x)/x`.** -/
theorem norm_integral_div_self_mul_exp_le_stationary {w w' : ℝ → ℝ} {Θ Θ' Θ'' : ℝ → ℝ}
    {u v c μ δ W : ℝ} (hu : 0 < u) (huv : u ≤ v) (hμ : 0 < μ) (hδ : 0 < δ)
    (hw : ∀ x ∈ Icc u v, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Icc u v))
    (hw1 : ∀ x ∈ Icc u v, |w x| ≤ 1) (hW : ∫ x in u..v, |w' x| ≤ W)
    (hΘ : ∀ x ∈ Icc u v, HasDerivAt Θ (Θ' x) x)
    (hΘ' : ∀ x ∈ Icc u v, HasDerivAt Θ' (Θ'' x) x) (hΘ'' : ContinuousOn Θ'' (Icc u v))
    (hpos : ∀ x ∈ Icc u v, 0 ≤ Θ'' x) (hlow : ∀ x ∈ Icc u v, μ * |x - c| ≤ |Θ' x|) :
    ‖∫ x in u..v, ((w x / x : ℝ) : ℂ) * Complex.exp ((Θ x : ℂ) * I)‖ ≤
      2 * δ / u + (2 * W + 8) / (u * (μ * δ)) := by
  have hxpos : ∀ x ∈ Icc u v, 0 < x := fun x hx => hu.trans_le hx.1
  have hwc : ContinuousOn w (Icc u v) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hg : ∀ x ∈ Icc u v, HasDerivAt (fun y => ((w y / y : ℝ) : ℂ))
      (((w' x / x - w x / x ^ 2 : ℝ) : ℂ)) x :=
    fun x hx => (hasDerivAt_div_self (hw x hx) (hxpos x hx).ne').ofReal_comp
  have hg'c : ContinuousOn (fun x => ((w' x / x - w x / x ^ 2 : ℝ) : ℂ)) (Icc u v) :=
    Complex.continuous_ofReal.comp_continuousOn ((hw'c.div continuousOn_id fun x hx =>
      (hxpos x hx).ne').sub (hwc.div (continuousOn_id.pow 2) fun x hx =>
        pow_ne_zero 2 (hxpos x hx).ne'))
  have hG : ∀ x ∈ Icc u v, ‖((w x / x : ℝ) : ℂ)‖ ≤ 1 / u := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (hxpos x hx)]
    exact le_trans (div_le_div_of_nonneg_right (hw1 x hx) (hxpos x hx).le)
      (div_le_div_of_nonneg_left zero_le_one hu hx.1)
  have hV : ∫ x in u..v, ‖((w' x / x - w x / x ^ 2 : ℝ) : ℂ)‖ ≤ W / u + 1 / u := by
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact integral_abs_deriv_div_self_le hu huv hwc hw'c hw1 hW
  refine le_trans (norm_integral_mul_exp_le_of_stationary huv hμ hδ hg hg'c hΘ hΘ' hΘ'' hpos
    hlow hG hV) (le_of_eq ?_)
  field_simp
  ring

/-! ## The phases -/

theorem hasDerivAt_ubPhase (t : ℝ) (k : ℤ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (ubPhase t k) (2 * π * k - t / x) x := by
  have h := ((hasDerivAt_id' x).const_mul (2 * π * k)).sub ((Real.hasDerivAt_log hx).const_mul t)
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_ubPhaseDeriv (t : ℝ) (k : ℤ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => 2 * π * k - t / y) (t / x ^ 2) x := by
  have h := (((hasDerivAt_id' x).inv hx).const_mul t).const_sub (2 * π * k)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · field_simp
  · exact Filter.Eventually.of_forall fun y => by simp [div_eq_mul_inv]

/-! ## The window -/

theorem hasDerivAt_ubWindow {N N' : ℕ} (x : ℝ) :
    HasDerivAt (ubWindow N N')
      (smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x) x :=
  hasDerivAt_smoothPlateau x

theorem continuous_ubWindowDeriv {N N' : ℕ} :
    Continuous (smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2)) :=
  continuous_smoothPlateauDeriv

theorem abs_ubWindow_le {N N' : ℕ} (x : ℝ) : |ubWindow N N' x| ≤ 1 := by
  unfold ubWindow
  rw [abs_of_nonneg (smoothPlateau_nonneg x)]; exact smoothPlateau_le_one x

/-! ## The non-stationary bound -/

variable {N N' : ℕ}

/-- **Non-stationary frequencies.**  If `|2πk − t/x| ≥ λ` on `[N, N' + 1]` then
`‖ubFreq k‖ ≤ 4/(Nλ)`. -/
theorem norm_ubFreq_le_of_nonstationary (hN : 1 ≤ N) (hNN' : N < N') {t lam : ℝ} (ht : 0 ≤ t)
    (hlam : 0 < lam) (k : ℤ)
    (hlow : ∀ x ∈ Icc (N : ℝ) ((N' : ℝ) + 1), lam ≤ |2 * π * k - t / x|) :
    ‖ubFreq N N' t k‖ ≤ 4 / (N * lam) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNN'r : (N : ℝ) ≤ (N' : ℝ) + 1 := by
    have : (N : ℝ) < N' := by exact_mod_cast hNN'
    linarith
  have hxpos : ∀ x ∈ Icc (N : ℝ) ((N' : ℝ) + 1), x ≠ 0 := fun x hx => (hN0.trans_le hx.1).ne'
  have h := norm_integral_div_self_mul_exp_le (w := ubWindow N N')
    (Θ := ubPhase t k) (Θ' := fun x => 2 * π * k - t / x) (Θ'' := fun x => t / x ^ 2)
    (W := 2) hN0 hNN'r hlam (fun x _ => hasDerivAt_ubWindow x)
    continuous_ubWindowDeriv.continuousOn (fun x _ => abs_ubWindow_le x)
    (integral_abs_smoothPlateauDeriv_le (by norm_num) hNN'r)
    (ubWindow_eq_zero_of_le (by linarith)) (ubWindow_eq_zero_of_ge (by linarith))
    (fun x hx => hasDerivAt_ubPhase t k (hxpos x hx))
    (fun x hx => hasDerivAt_ubPhaseDeriv t k (hxpos x hx))
    (continuousOn_const.div (continuousOn_id.pow 2) fun x hx => pow_ne_zero 2 (hxpos x hx))
    (fun x _ => by positivity) hlow
  rw [ubFreq]
  refine le_trans (le_of_eq ?_) (le_trans h (le_of_eq (by ring)))
  rfl

/-- Frequencies `k ≤ t/(2π(N'+1)) − 1`. -/
theorem norm_ubFreq_le_low (hN : 1 ≤ N) (hNN' : N < N') {t : ℝ} (ht : 0 ≤ t) (k : ℤ)
    (hk : (k : ℝ) + 1 ≤ t / (2 * π * ((N' : ℝ) + 1))) :
    ‖ubFreq N N' t k‖ ≤ 4 / (N * (2 * π * (t / (2 * π * ((N' : ℝ) + 1)) - k))) := by
  have hN'1 : (0 : ℝ) < (N' : ℝ) + 1 := by positivity
  refine norm_ubFreq_le_of_nonstationary hN hNN' ht (by nlinarith [Real.pi_pos]) k
    fun x hx => ?_
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by exact_mod_cast hN) hx.1
  have h1 : t / ((N' : ℝ) + 1) ≤ t / x := div_le_div_of_nonneg_left ht hx0 hx.2
  have h2 : 2 * π * (t / (2 * π * ((N' : ℝ) + 1))) = t / ((N' : ℝ) + 1) := by
    field_simp
  rw [abs_of_neg (by nlinarith [Real.pi_pos])]
  nlinarith [Real.pi_pos]

/-- Frequencies `k ≥ t/(2πN) + 1`. -/
theorem norm_ubFreq_le_high (hN : 1 ≤ N) (hNN' : N < N') {t : ℝ} (ht : 0 ≤ t) (k : ℤ)
    (hk : t / (2 * π * N) + 1 ≤ (k : ℝ)) :
    ‖ubFreq N N' t k‖ ≤ 4 / (N * (2 * π * (k - t / (2 * π * N)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine norm_ubFreq_le_of_nonstationary hN hNN' ht (by nlinarith [Real.pi_pos]) k
    fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hN0.trans_le hx.1
  have h1 : t / x ≤ t / N := div_le_div_of_nonneg_left ht hN0 hx.1
  have h2 : 2 * π * (t / (2 * π * N)) = t / N := by field_simp
  rw [abs_of_pos (by nlinarith [Real.pi_pos])]
  nlinarith [Real.pi_pos]

/-- Nonpositive frequencies, `k ≤ 0`, for `t > 0`. -/
theorem norm_ubFreq_le_nonpos (hN : 1 ≤ N) (hNN' : N < N') {t : ℝ} (ht : 0 < t) (k : ℤ)
    (hk : k ≤ 0) : ‖ubFreq N N' t k‖ ≤ 4 * ((N' : ℝ) + 1) / (N * t) := by
  have hN'1 : (0 : ℝ) < (N' : ℝ) + 1 := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast hk
  have h := norm_ubFreq_le_of_nonstationary hN hNN' ht.le (lam := t / ((N' : ℝ) + 1))
    (by positivity) k fun x hx => by
      have hx0 : (0 : ℝ) < x := hN0.trans_le hx.1
      have h1 : t / ((N' : ℝ) + 1) ≤ t / x := div_le_div_of_nonneg_left ht.le hx0 hx.2
      have h2 : 0 < t / x := by positivity
      rw [abs_of_neg (by nlinarith [Real.pi_pos])]
      nlinarith [Real.pi_pos]
  refine le_trans h (le_of_eq ?_)
  field_simp

/-! ## The stationary bound -/

/-- **Stationary frequencies.**  For `k ≥ 1` and every `δ > 0`,
`‖ubFreq k‖ ≤ 2δ/N + 12(N'+1)/(2πk·N·δ)`. -/
theorem norm_ubFreq_le_stationary_delta (hN : 1 ≤ N) (hNN' : N < N') {t δ : ℝ} (ht : 0 ≤ t)
    (hδ : 0 < δ) {k : ℤ} (hk : 1 ≤ k) :
    ‖ubFreq N N' t k‖ ≤ 2 * δ / N + 12 * ((N' : ℝ) + 1) / (2 * π * k * N * δ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hN'1 : (0 : ℝ) < (N' : ℝ) + 1 := by positivity
  have hNN'r : (N : ℝ) ≤ (N' : ℝ) + 1 := by
    have : (N : ℝ) < N' := by exact_mod_cast hNN'
    linarith
  have hxpos : ∀ x ∈ Icc (N : ℝ) ((N' : ℝ) + 1), x ≠ 0 := fun x hx => (hN0.trans_le hx.1).ne'
  have hμ : 0 < 2 * π * k / ((N' : ℝ) + 1) := by positivity
  have h := norm_integral_div_self_mul_exp_le_stationary (w := ubWindow N N')
    (Θ := ubPhase t k) (Θ' := fun x => 2 * π * k - t / x) (Θ'' := fun x => t / x ^ 2)
    (c := t / (2 * π * k)) (W := 2) hN0 hNN'r hμ hδ (fun x _ => hasDerivAt_ubWindow x)
    continuous_ubWindowDeriv.continuousOn (fun x _ => abs_ubWindow_le x)
    (integral_abs_smoothPlateauDeriv_le (by norm_num) hNN'r)
    (fun x hx => hasDerivAt_ubPhase t k (hxpos x hx))
    (fun x hx => hasDerivAt_ubPhaseDeriv t k (hxpos x hx))
    (continuousOn_const.div (continuousOn_id.pow 2) fun x hx => pow_ne_zero 2 (hxpos x hx))
    (fun x _ => by positivity) fun x hx => by
      have hx0 : (0 : ℝ) < x := hN0.trans_le hx.1
      have hid : 2 * π * k - t / x = (2 * π * k / x) * (x - t / (2 * π * k)) := by
        field_simp
      rw [hid, abs_mul, abs_of_pos (by positivity : 0 < 2 * π * k / x)]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hx0 hx.2)
        (abs_nonneg _)
  rw [ubFreq]
  refine le_trans h (le_of_eq ?_)
  field_simp
  ring

/-- **Stationary frequencies, explicit.**  If `k ≥ 1`, `k > t/(2π(N'+1)) − 1`, `1 ≤ t ≤ N²` and
`N' ≤ 2N`, then `‖ubFreq k‖ ≤ 218/√t`. -/
theorem norm_ubFreq_le_stationary (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N) {t : ℝ}
    (ht : 1 ≤ t) {k : ℤ} (hk : 1 ≤ k) (hk0 : t / (2 * π * ((N' : ℝ) + 1)) < (k : ℝ) + 1) :
    ‖ubFreq N N' t k‖ ≤ 218 / Real.sqrt t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hN'r : (N' : ℝ) + 1 ≤ 3 * N := by
    have : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
  -- `1/(kN) ≤ 12π/t`
  have hkey : 1 / ((k : ℝ) * N) ≤ 12 * π / t := by
    rw [div_le_div_iff₀ (by positivity) (by linarith), one_mul]
    have hpos2 : (0 : ℝ) < 2 * π * ((N' : ℝ) + 1) := by positivity
    have hm : 4 * π * ((N' : ℝ) + 1) * k ≤ 12 * π * (k * N) := by
      have := mul_le_mul_of_nonneg_left hN'r (by positivity : (0 : ℝ) ≤ 4 * π * k)
      nlinarith
    have hm2 : 12 * π * N ≤ 12 * π * (k * N) := by
      have := mul_le_mul_of_nonneg_left hk1 (by positivity : (0 : ℝ) ≤ 12 * π * N)
      nlinarith
    by_cases hcase : t / (2 * π * ((N' : ℝ) + 1)) ≤ 2 * k
    · have h2 : t ≤ 4 * π * ((N' : ℝ) + 1) * k := by
        rw [div_le_iff₀ hpos2] at hcase; linarith
      linarith
    · push Not at hcase
      have h2 : t < 4 * π * ((N' : ℝ) + 1) := by
        have : t / (2 * π * ((N' : ℝ) + 1)) < 2 := by linarith
        rw [div_lt_iff₀ hpos2] at this; linarith
      have h3 : 4 * π * ((N' : ℝ) + 1) ≤ 12 * π * N := by
        have := mul_le_mul_of_nonneg_left hN'r (by positivity : (0 : ℝ) ≤ 4 * π)
        linarith
      linarith
  have h := norm_ubFreq_le_stationary_delta (t := t) hN hNN' (by linarith)
    (δ := N / Real.sqrt t) (by positivity) hk
  refine le_trans h ?_
  have e1 : 2 * (N / Real.sqrt t) / N = 2 / Real.sqrt t := by field_simp
  have e2 : 12 * ((N' : ℝ) + 1) / (2 * π * k * N * (N / Real.sqrt t)) =
      (6 / π) * (((N' : ℝ) + 1) / N) * Real.sqrt t * (1 / ((k : ℝ) * N)) := by
    field_simp
    norm_num
  rw [e1, e2]
  have h3 : ((N' : ℝ) + 1) / N ≤ 3 := by rw [div_le_iff₀ hN0]; linarith
  have h4 : (6 / π) * (((N' : ℝ) + 1) / N) * Real.sqrt t * (1 / ((k : ℝ) * N)) ≤
      (6 / π) * 3 * Real.sqrt t * (12 * π / t) := by
    gcongr
  have h6 : Real.sqrt t / t = 1 / Real.sqrt t := by
    rw [div_eq_div_iff (by positivity) hst.ne', one_mul]; exact hsq
  have h7 : (6 / π) * 3 * Real.sqrt t * (12 * π / t) = 216 * (Real.sqrt t / t) := by
    field_simp; ring
  have h5 : (6 / π) * 3 * Real.sqrt t * (12 * π / t) = 216 / Real.sqrt t := by
    rw [h7, h6]; ring
  have h8 : 218 / Real.sqrt t = 2 / Real.sqrt t + 216 / Real.sqrt t := by ring
  linarith

/-! ## The model integral -/

/-- The model window `ψ`, a plateau around `1`. -/
def ubModelWindow (y : ℝ) : ℝ := smoothPlateau (3 / 4) (5 / 4) (1 / 8) y

/-- The model integral `∫_{3/4}^{5/4} ψ(y) y^{-1} e^{it(y − log y)} dy`. -/
def ubJ (t : ℝ) : ℂ :=
  ∫ y in (3 / 4 : ℝ)..(5 / 4), ((ubModelWindow y / y : ℝ) : ℂ) *
    Complex.exp (((t * (y - Real.log y)) : ℝ) * I)

/-- **The model integral is `O(t^{-1/2})`.** -/
theorem norm_ubJ_le {t : ℝ} (ht : 0 < t) : ‖ubJ t‖ ≤ 23 / Real.sqrt t := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hpos : ∀ y ∈ Icc (3 / 4 : ℝ) (5 / 4), y ≠ 0 := fun y hy => by linarith [hy.1]
  have hΘ : ∀ y ∈ Icc (3 / 4 : ℝ) (5 / 4), HasDerivAt (fun y => t * (y - Real.log y))
      (t * (1 - 1 / y)) y := by
    intro y hy
    exact (((hasDerivAt_id' y).sub (Real.hasDerivAt_log (hpos y hy))).const_mul t).congr_deriv
      (by rw [one_div])
  have hΘ' : ∀ y ∈ Icc (3 / 4 : ℝ) (5 / 4), HasDerivAt (fun y => t * (1 - 1 / y))
      (t / y ^ 2) y := by
    intro y hy
    have h := ((((hasDerivAt_id' y).inv (hpos y hy)).const_sub 1).const_mul t)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · field_simp
    · exact Filter.Eventually.of_forall fun z => by simp [one_div]
  have h := norm_integral_div_self_mul_exp_le_stationary (w := ubModelWindow)
    (Θ := fun y => t * (y - Real.log y)) (Θ' := fun y => t * (1 - 1 / y))
    (Θ'' := fun y => t / y ^ 2) (c := 1) (μ := 4 * t / 5) (δ := 1 / Real.sqrt t) (W := 2)
    (by norm_num) (by norm_num) (by positivity) (by positivity)
    (fun y _ => hasDerivAt_smoothPlateau y) continuous_smoothPlateauDeriv.continuousOn
    (fun y _ => by
      unfold ubModelWindow
      rw [abs_of_nonneg (smoothPlateau_nonneg y)]; exact smoothPlateau_le_one y)
    (integral_abs_smoothPlateauDeriv_le (by norm_num) (by norm_num)) hΘ hΘ'
    (continuousOn_const.div (continuousOn_id.pow 2) fun y hy => pow_ne_zero 2 (hpos y hy))
    (fun y _ => by positivity) fun y hy => by
      have hy0 : (0 : ℝ) < y := by linarith [hy.1]
      have hid : t * (1 - 1 / y) = (t / y) * (y - 1) := by field_simp
      rw [hid, abs_mul, abs_of_pos (by positivity : 0 < t / y)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [le_div_iff₀ hy0]; nlinarith [hy.2]
  unfold ubJ
  refine le_trans h ?_
  have h6 : Real.sqrt t / t = 1 / Real.sqrt t := by
    rw [div_eq_div_iff (by positivity) hst.ne', one_mul]; exact hsq
  have h7 : (2 * 2 + 8) / (3 / 4 * (4 * t / 5 * (1 / Real.sqrt t))) =
      20 * (Real.sqrt t / t) := by
    field_simp; ring
  have e : 2 * (1 / Real.sqrt t) / (3 / 4) + (2 * 2 + 8) / (3 / 4 * (4 * t / 5 *
      (1 / Real.sqrt t))) = (8 / 3 + 20) / Real.sqrt t := by
    rw [h7, h6]; ring
  rw [e]
  exact div_le_div_of_nonneg_right (by norm_num) hst.le

end

end RHTower.Sieve
