import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialSpanTestMellinLowFrequency
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeAdmission

/-!
# Critical Mellin readout and low-frequency exclusion

The critical source `g(x) = e^{x/2} B_b(e^{-x}) 1_{x ≤ 0}` of a real phase combination has Fourier
readout `ĝ(t) = ∫_1^∞ v^{-3/2} B_b(v) e^{-it log v} dv`. The nonstationary phase bound
`‖∫_1^∞ v^{-p} e^{i(ωv - t log v)} dv‖ ≤ 5/|ω|` (for `|t| ≤ |ω|/2`) holds for every power
amplitude with `p > 1`, by one integration by parts against `v^{-p}/(ω - t/v)`. Expanding
`B_b` into harmonic layers of frequencies `2πkλ_{n+1} ≥ 2πk(n+1)` gives the same low-frequency
exclusion as for the canonical tail envelope: `‖ĝ(t)‖ ≤ D ∑ |b_n|/(n+1)` with `D = 15/π³`
whenever `|t| ≤ π(n+1)` on the support, hence `‖ĝ(t)‖² ≤ (2D²/M) ∑ b_n²` on `|t| ≤ πM` for
families supported on scales `n+1 ≥ M`.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.Zeta23

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The amplitude divided by the phase derivative, `h(v) = v^{-p} / (ω - t/v)`. -/
def rpowPhaseAmplitude (p ω t v : ℝ) : ℝ :=
  v ^ (-p) / (ω - t / v)

/-- The derivative of `rpowPhaseAmplitude` in `v`. -/
def rpowPhaseAmplitudeDeriv (p ω t v : ℝ) : ℝ :=
  (-p) * v ^ (-p - 1) / (ω - t / v) - v ^ (-p) * (t / v ^ 2) / (ω - t / v) ^ 2

/-- Derivative of the power amplitude over the phase derivative. -/
theorem hasDerivAt_rpowPhaseAmplitude (p : ℝ) {ω t v : ℝ} (hv : 0 < v) (hne : ω - t / v ≠ 0) :
    HasDerivAt (rpowPhaseAmplitude p ω t) (rpowPhaseAmplitudeDeriv p ω t v) v := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-p)) ((-p) * v ^ (-p - 1)) v :=
    Real.hasDerivAt_rpow_const (p := -p) (x := v) (Or.inl hv.ne')
  have h2 : HasDerivAt (fun x : ℝ => ω - t / x) (t / v ^ 2) v := by
    have h := ((hasDerivAt_inv hv.ne').const_mul t).const_sub ω
    simp only [div_eq_mul_inv]
    exact h.congr_deriv (by ring)
  have h := h1.div h2 hne
  unfold rpowPhaseAmplitude rpowPhaseAmplitudeDeriv
  refine h.congr_deriv ?_
  field_simp

/-- On `v ≥ 1` with `|t| ≤ |ω|/2`, `|h(v)| ≤ (2/|ω|) v^{-p}`. -/
theorem abs_rpowPhaseAmplitude_le {p ω t v : ℝ} (hω : ω ≠ 0) (hv : 1 ≤ v)
    (ht : |t| ≤ |ω| / 2) :
    |rpowPhaseAmplitude p ω t v| ≤ 2 / |ω| * v ^ (-p) := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hω0 : 0 < |ω| := abs_pos.mpr hω
  have hd := half_abs_le_abs_phase_deriv hv ht
  have hd0 : 0 < |ω - t / v| := lt_of_lt_of_le (by positivity) hd
  unfold rpowPhaseAmplitude
  rw [abs_div, abs_of_nonneg (Real.rpow_nonneg hv0.le _), div_le_iff₀ hd0]
  have hp : 0 ≤ v ^ (-p) := Real.rpow_nonneg hv0.le _
  calc v ^ (-p) = 2 / |ω| * v ^ (-p) * (|ω| / 2) := by field_simp
    _ ≤ 2 / |ω| * v ^ (-p) * |ω - t / v| := mul_le_mul_of_nonneg_left hd (by positivity)

/-- On `v ≥ 1` with `|t| ≤ |ω|/2`, `|h'(v)| ≤ (2/|ω|) p v^{-p-1} + (4|t|/|ω|²) v^{-p-2}`. -/
theorem abs_rpowPhaseAmplitudeDeriv_le {p ω t v : ℝ} (hp : 0 ≤ p) (hω : ω ≠ 0) (hv : 1 ≤ v)
    (ht : |t| ≤ |ω| / 2) :
    |rpowPhaseAmplitudeDeriv p ω t v| ≤
      2 / |ω| * (p * v ^ (-p - 1)) + 4 * |t| / |ω| ^ 2 * v ^ (-p - 2) := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hω0 : 0 < |ω| := abs_pos.mpr hω
  have hd := half_abs_le_abs_phase_deriv hv ht
  have hd0 : 0 < |ω - t / v| := lt_of_lt_of_le (by positivity) hd
  have hp1 : 0 ≤ v ^ (-p - 1) := Real.rpow_nonneg hv0.le _
  have hp0 : 0 ≤ v ^ (-p) := Real.rpow_nonneg hv0.le _
  have h2 : v ^ (-p) / v ^ 2 = v ^ (-p - 2) := by
    rw [show (-p - 2 : ℝ) = (-p) - (2 : ℕ) by norm_num, Real.rpow_sub_natCast hv0.ne']
  have hinv : 1 / |ω - t / v| ≤ 2 / |ω| := by
    rw [div_le_div_iff₀ hd0 hω0]
    linarith
  have hinv2 : 1 / |ω - t / v| ^ 2 ≤ 4 / |ω| ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hinv 2
    rw [div_pow, div_pow, one_pow] at h
    calc 1 / |ω - t / v| ^ 2 ≤ 2 ^ 2 / |ω| ^ 2 := h
      _ = 4 / |ω| ^ 2 := by norm_num
  unfold rpowPhaseAmplitudeDeriv
  refine (abs_sub _ _).trans ?_
  have hA : |(-p) * v ^ (-p - 1) / (ω - t / v)| ≤ 2 / |ω| * (p * v ^ (-p - 1)) := by
    rw [abs_div, abs_mul, abs_of_nonneg hp1, abs_neg, abs_of_nonneg hp]
    calc p * v ^ (-p - 1) / |ω - t / v| = (p * v ^ (-p - 1)) * (1 / |ω - t / v|) := by ring
      _ ≤ (p * v ^ (-p - 1)) * (2 / |ω|) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hB : |v ^ (-p) * (t / v ^ 2) / (ω - t / v) ^ 2| ≤ 4 * |t| / |ω| ^ 2 * v ^ (-p - 2) := by
    rw [abs_div, abs_mul, abs_of_nonneg hp0, abs_div, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2),
      abs_pow]
    calc v ^ (-p) * (|t| / v ^ 2) / |ω - t / v| ^ 2 =
          (|t| * (v ^ (-p) / v ^ 2)) * (1 / |ω - t / v| ^ 2) := by ring
      _ ≤ (|t| * (v ^ (-p) / v ^ 2)) * (4 / |ω| ^ 2) :=
          mul_le_mul_of_nonneg_left hinv2 (by positivity)
      _ = 4 * |t| / |ω| ^ 2 * v ^ (-p - 2) := by rw [h2]; ring
  linarith

/-- The derivative of the amplitude is continuous on `[1, ∞)`. -/
theorem continuousOn_rpowPhaseAmplitudeDeriv (p : ℝ) {ω t : ℝ} (hω : ω ≠ 0) (ht : |t| ≤ |ω| / 2) :
    ContinuousOn (rpowPhaseAmplitudeDeriv p ω t) (Ici 1) := by
  have hne : ∀ v ∈ Ici (1 : ℝ), ω - t / v ≠ 0 := fun v hv => by
    have hd := half_abs_le_abs_phase_deriv (mem_Ici.mp hv) ht
    have hω0 : 0 < |ω| := abs_pos.mpr hω
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hd)
  have hpos : ∀ v ∈ Ici (1 : ℝ), v ≠ 0 := fun v hv => (lt_of_lt_of_le one_pos hv).ne'
  have hrp (q : ℝ) : ContinuousOn (fun v : ℝ => v ^ q) (Ici 1) :=
    continuousOn_id.rpow_const fun v hv => Or.inl (hpos v hv)
  have hden : ContinuousOn (fun v : ℝ => ω - t / v) (Ici 1) :=
    continuousOn_const.sub (continuousOn_const.div continuousOn_id hpos)
  unfold rpowPhaseAmplitudeDeriv
  refine ContinuousOn.sub ((continuousOn_const.mul (hrp _)).div hden hne) ?_
  refine ((hrp _).mul (continuousOn_const.div (continuousOn_id.pow 2)
    fun v hv => pow_ne_zero 2 (hpos v hv))).div (hden.pow 2) fun v hv => pow_ne_zero 2 (hne v hv)

/-- **Nonstationary Mellin bound for a general power amplitude.** For `p > 1`, `ω ≠ 0` and
`|t| ≤ |ω|/2`, `‖∫_1^∞ v^{-p} e^{i(ωv - t log v)} dv‖ ≤ 5/|ω|`. -/
theorem norm_integral_Ioi_one_rpow_mul_cexp_phase_le_of_one_lt {p ω t : ℝ} (hp : 1 < p)
    (hω : ω ≠ 0) (ht : |t| ≤ |ω| / 2) :
    IntegrableOn (fun v : ℝ => ((v ^ (-p) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((ω * v - t * Real.log v : ℝ) : ℂ))) (Ioi 1) ∧
    ‖∫ v in Ioi (1 : ℝ), ((v ^ (-p) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((ω * v - t * Real.log v : ℝ) : ℂ))‖ ≤ 5 / |ω| := by
  set A : ℝ → ℂ := fun v => ((v ^ (-p) : ℝ) : ℂ) with hA
  set φ : ℝ → ℝ := fun v => ω * v - t * Real.log v with hφ
  have hp0 : 0 < p := lt_trans one_pos hp
  have hω0 : 0 < |ω| := abs_pos.mpr hω
  have hpos : ∀ v ∈ Ici (1 : ℝ), 0 < v := fun v hv => lt_of_lt_of_le one_pos hv
  have hAc : ContinuousOn A (Ici 1) := Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_id.rpow_const fun v hv => Or.inl (hpos v hv).ne')
  have hφc : ContinuousOn φ (Ici 1) := (continuousOn_const.mul continuousOn_id).sub
    (continuousOn_const.mul (Real.continuousOn_log.mono fun v hv => (hpos v hv).ne'))
  have hFc : ContinuousOn (fun v => A v * Complex.exp (Complex.I * (φ v : ℂ))) (Ici 1) :=
    hAc.mul (Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφc)))
  have hwp : IntegrableOn (fun v : ℝ => v ^ (-p)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hFi : IntegrableOn (fun v => A v * Complex.exp (Complex.I * (φ v : ℂ))) (Ioi 1) := by
    refine hwp.mono' ((hFc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, hA, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)]
  refine ⟨hFi, ?_⟩
  have hi1 : IntegrableOn (fun v : ℝ => v ^ (-p - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hi2 : IntegrableOn (fun v : ℝ => v ^ (-p - 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  set m : ℝ → ℝ := fun v => 2 / |ω| * (p * v ^ (-p - 1)) + 4 * |t| / |ω| ^ 2 * v ^ (-p - 2) with hm
  have hmi : IntegrableOn m (Ioi 1) := ((hi1.const_mul p).const_mul _).add (hi2.const_mul _)
  have hm0 : ∀ v ∈ Ioi (1 : ℝ), 0 ≤ m v := fun v hv => by
    have hv0 : 0 < v := lt_trans one_pos hv
    have := Real.rpow_nonneg hv0.le (-p - 1)
    have := Real.rpow_nonneg hv0.le (-p - 2)
    simp only [hm]
    positivity
  set Im : ℝ := ∫ v in Ioi (1 : ℝ), m v with hIm
  have hIm_eq : Im = 2 / |ω| + 4 * |t| / |ω| ^ 2 * (1 / (p + 1)) := by
    rw [hIm, hm, integral_add ((hi1.const_mul p).const_mul _) (hi2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
      integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp only [Real.one_rpow]
    have e1 : -(1 : ℝ) / (-p - 1 + 1) = 1 / p := by
      rw [show -p - 1 + 1 = -p by ring, div_neg, neg_div, neg_neg]
    have e2 : -(1 : ℝ) / (-p - 2 + 1) = 1 / (p + 1) := by
      rw [show -p - 2 + 1 = -(p + 1) by ring, div_neg, neg_div, neg_neg]
    rw [e1, e2]
    field_simp
  have hfin : ∀ X : ℝ, 1 ≤ X →
      ‖∫ v in (1 : ℝ)..X, A v * Complex.exp (Complex.I * (φ v : ℂ))‖ ≤
        2 / |ω| * X ^ (-p) + 2 / |ω| + Im := by
    intro X hX
    have hsub : uIcc (1 : ℝ) X ⊆ Ici 1 := by
      rw [uIcc_of_le hX]
      exact Icc_subset_Ici_self
    set B : ℝ → ℂ := fun v => ((rpowPhaseAmplitude p ω t v : ℝ) : ℂ) / Complex.I with hB
    set B' : ℝ → ℂ := fun v => ((rpowPhaseAmplitudeDeriv p ω t v : ℝ) : ℂ) / Complex.I
      with hB'
    have hne : ∀ v ∈ Ici (1 : ℝ), ω - t / v ≠ 0 := fun v hv => by
      have hd := half_abs_le_abs_phase_deriv (mem_Ici.mp hv) ht
      exact abs_pos.mp (lt_of_lt_of_le (by positivity) hd)
    have hφd : ∀ x ∈ uIcc (1 : ℝ) X, HasDerivAt φ (ω - t / x) x := fun x hx => by
      have hx0 := hpos x (hsub hx)
      have h := ((hasDerivAt_id x).const_mul ω).sub ((Real.hasDerivAt_log hx0.ne').const_mul t)
      refine h.congr_deriv ?_
      simp [div_eq_mul_inv]
    have hBd : ∀ x ∈ uIcc (1 : ℝ) X, HasDerivAt B (B' x) x := fun x hx =>
      ((hasDerivAt_rpowPhaseAmplitude p (hpos x (hsub hx)) (hne x (hsub hx))).ofReal_comp
        ).div_const Complex.I
    have hB'c : ContinuousOn B' (uIcc (1 : ℝ) X) :=
      ((Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_rpowPhaseAmplitudeDeriv p hω ht)).div_const Complex.I).mono hsub
    have hrel : ∀ x ∈ uIcc (1 : ℝ) X, B x * (Complex.I * ((ω - t / x : ℝ) : ℂ)) = A x := by
      intro x hx
      have hx' := hne x (hsub hx)
      simp only [hB, hA, rpowPhaseAmplitude]
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have hc : (ω : ℂ) - t / x ≠ 0 := by exact_mod_cast hx'
      push_cast
      field_simp
    have hmain := RHTower.norm_integral_cexp_le_of_antiderivative hX hφd hBd hB'c
      (hAc.mono hsub) hrel
    have hBn (v : ℝ) (hv : 1 ≤ v) : ‖B v‖ ≤ 2 / |ω| * v ^ (-p) := by
      simp only [hB, norm_div, Complex.norm_I, div_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_rpowPhaseAmplitude_le hω hv ht
    have hB'n : ∀ v ∈ Icc (1 : ℝ) X, ‖B' v‖ ≤ m v := fun v hv => by
      simp only [hB', norm_div, Complex.norm_I, div_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_rpowPhaseAmplitudeDeriv_le hp0.le hω hv.1 ht
    have hint1 : (∫ v in (1 : ℝ)..X, ‖B' v‖) ≤ Im := by
      have hmon : (∫ v in (1 : ℝ)..X, ‖B' v‖) ≤ ∫ v in (1 : ℝ)..X, m v :=
        intervalIntegral.integral_mono_on hX (hB'c.norm.intervalIntegrable)
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr
            (hmi.mono_set Ioc_subset_Ioi_self)) hB'n
      refine hmon.trans ?_
      rw [intervalIntegral.integral_of_le hX]
      exact setIntegral_mono_set hmi (ae_restrict_of_forall_mem measurableSet_Ioi hm0)
        (Eventually.of_forall fun v hv => hv.1)
    have hB1 := hBn 1 le_rfl
    rw [Real.one_rpow, mul_one] at hB1
    linarith [hBn X hX]
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) (1 : ℝ) hFi tendsto_id
  have hrhs : Tendsto (fun X : ℝ => 2 / |ω| * X ^ (-p) + 2 / |ω| + Im) atTop
      (𝓝 (2 / |ω| * 0 + 2 / |ω| + Im)) :=
    (((tendsto_rpow_neg_atTop hp0).const_mul _).add_const _).add_const _
  have hle := le_of_tendsto_of_tendsto (hlim.norm) hrhs
    (Filter.eventually_atTop.mpr ⟨1, fun X hX => hfin X hX⟩)
  rw [mul_zero, zero_add, hIm_eq] at hle
  refine le_trans hle ?_
  have hq : 4 * |t| / |ω| ^ 2 * (1 / (p + 1)) ≤ 1 / |ω| := by
    have h1 : 1 / (p + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have h2 : 4 * |t| / |ω| ^ 2 ≤ 2 / |ω| := by
      rw [div_le_div_iff₀ (by positivity) hω0]; nlinarith
    calc 4 * |t| / |ω| ^ 2 * (1 / (p + 1)) ≤ 2 / |ω| * (1 / 2) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = 1 / |ω| := by ring
  have : 2 / |ω| + 2 / |ω| + 1 / |ω| = 5 / |ω| := by ring
  linarith

/-- Cosine form: `|∫_1^∞ v^{-p} cos(θ v) e^{-it log v} dv| ≤ 5/|θ|` for `p > 1`, `|t| ≤ |θ|/2`. -/
theorem norm_integral_Ioi_one_rpow_mul_cos_mul_cexp_le_of_one_lt {p θ t : ℝ} (hp : 1 < p)
    (hθ : θ ≠ 0) (ht : |t| ≤ |θ| / 2) :
    IntegrableOn (fun v : ℝ => ((v ^ (-p) * Real.cos (θ * v) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))) (Ioi 1) ∧
    ‖∫ v in Ioi (1 : ℝ), ((v ^ (-p) * Real.cos (θ * v) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))‖ ≤ 5 / |θ| := by
  have hθ' : -θ ≠ 0 := neg_ne_zero.mpr hθ
  have ht' : |t| ≤ |-θ| / 2 := by rwa [abs_neg]
  obtain ⟨hi1, hb1⟩ := norm_integral_Ioi_one_rpow_mul_cexp_phase_le_of_one_lt hp hθ ht
  obtain ⟨hi2, hb2⟩ := norm_integral_Ioi_one_rpow_mul_cexp_phase_le_of_one_lt hp hθ' ht'
  have hpt : ∀ v : ℝ, ((v ^ (-p) * Real.cos (θ * v) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))) =
      (1 / 2 : ℂ) * (((v ^ (-p) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((θ * v - t * Real.log v : ℝ) : ℂ))) +
      (1 / 2 : ℂ) * (((v ^ (-p) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-θ * v - t * Real.log v : ℝ) : ℂ))) := by
    intro v
    rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
    push_cast
    rw [show Complex.I * (↑θ * ↑v - ↑t * ↑(Real.log v)) =
        ↑θ * ↑v * Complex.I + -(Complex.I * (↑t * ↑(Real.log v))) by ring,
      show Complex.I * (-↑θ * ↑v - ↑t * ↑(Real.log v)) =
        -(↑θ * ↑v) * Complex.I + -(Complex.I * (↑t * ↑(Real.log v))) by ring,
      Complex.exp_add, Complex.exp_add]
    ring
  have hfun : (fun v : ℝ => ((v ^ (-p) * Real.cos (θ * v) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))) = fun v =>
      (1 / 2 : ℂ) * (((v ^ (-p) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((θ * v - t * Real.log v : ℝ) : ℂ))) +
      (1 / 2 : ℂ) * (((v ^ (-p) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-θ * v - t * Real.log v : ℝ) : ℂ))) := funext hpt
  rw [hfun]
  refine ⟨(hi1.const_mul _).add (hi2.const_mul _), ?_⟩
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  rw [abs_neg] at hb2
  linarith

/-- A real phase combination is real: its complex form is the cast of its real part. -/
theorem factorialPhaseCombination_ofReal_re (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    (((factorialPhaseCombination S (fun n => (b n : ℂ)) v).re : ℝ) : ℂ) =
      factorialPhaseCombination S (fun n => (b n : ℂ)) v := by
  unfold factorialPhaseCombination
  rw [Complex.re_sum]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  simp

/-- **Mellin readout of a critical source.** For real `t`,
`ĝ(t) = ∫_ℝ g(x) e^{itx} dx = ∫_1^∞ v^{-3/2} B_b(v) e^{-it log v} dv`. -/
theorem paperFT_criticalFactorialSource (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    paperFT (fun x => (criticalFactorialSource S b x : ℂ)) t =
      ∫ v in Ioi (1 : ℝ), ((v ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
        factorialPhaseCombination S (fun n => (b n : ℂ)) v *
          Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))) := by
  set B := factorialPhaseCombination S (fun n => (b n : ℂ)) with hB
  have h1 : paperFT (fun x => (criticalFactorialSource S b x : ℂ)) t = ∫ y in Iic (0 : ℝ),
      (Real.exp (y / 2) : ℂ) * B (Real.exp (-y)) *
        Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
    unfold paperFT
    rw [← integral_indicator measurableSet_Iic]
    congr 1
    funext y
    by_cases hy : y ≤ 0
    · simp only [criticalFactorialSource, indicator_of_mem (show y ∈ Iic 0 from hy)]
      rw [Complex.ofReal_mul, factorialPhaseCombination_ofReal_re]
    · simp only [criticalFactorialSource, indicator_of_notMem (show y ∉ Iic 0 from hy),
        Complex.ofReal_zero, zero_mul]
  have h2 : (∫ y in Iic (0 : ℝ), (Real.exp (y / 2) : ℂ) * B (Real.exp (-y)) *
      Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) =
      ∫ y in Ioi (0 : ℝ), (Real.exp (-y / 2) : ℂ) * B (Real.exp y) *
        Complex.exp (-(Complex.I * ((t * y : ℝ) : ℂ))) := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ => (Real.exp (-y / 2) : ℂ) *
      B (Real.exp y) * Complex.exp (-(Complex.I * ((t * y : ℝ) : ℂ))))
    simp only [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
    rw [show -(-y) / 2 = y / 2 by ring,
      show (-(Complex.I * ((t * -y : ℝ) : ℂ))) = Complex.I * (t : ℂ) * (y : ℂ) by push_cast; ring]
  have h3 := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (fun v => ((v ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * B v *
      Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))))
  rw [Real.image_exp_Ioi, Real.exp_zero] at h3
  rw [h1, h2, h3]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [abs_of_pos (Real.exp_pos y), Complex.real_smul, Real.log_exp, ← Real.exp_mul]
  have he : Real.exp y * Real.exp (y * (-3 / 2)) = Real.exp (-y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, he]

/-- The critical Mellin kernel `v^{-3/2} e^{-it log v}`. -/
def criticalMellinKernel (t v : ℝ) : ℂ :=
  ((v ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))

/-- The critical Mellin kernel has modulus `v^{-3/2}`. -/
theorem norm_criticalMellinKernel {t v : ℝ} (hv : 0 < v) :
    ‖criticalMellinKernel t v‖ = v ^ (-3 / 2 : ℝ) := by
  unfold criticalMellinKernel
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hv.le _)]
  have h : -(Complex.I * ((t * Real.log v : ℝ) : ℂ)) =
      Complex.I * ((-(t * Real.log v) : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal, mul_one]

/-- **Critical Mellin bound for one harmonic layer.** For `k ≥ 1` and `|t| ≤ π (n+1)` on the
support, `‖∫_1^∞ H_k(v) v^{-3/2} e^{-it log v} dv‖ ≤ ∑_n ‖b_n‖ · 5/(π k (n+1))`. -/
theorem norm_integral_factorialHarmonicLayer_criticalMellinKernel_le (S : Finset ℕ) (b : ℕ → ℂ)
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ)) :
    IntegrableOn (fun v => factorialHarmonicLayer S b k v * criticalMellinKernel t v) (Ioi 1) ∧
    ‖∫ v in Ioi (1 : ℝ), factorialHarmonicLayer S b k v * criticalMellinKernel t v‖ ≤
      ∑ n ∈ S, ‖b n‖ * (5 / (Real.pi * k * ((n + 1 : ℕ) : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set G : ℝ → ℝ → ℂ := fun θ v => ((v ^ (-(3 / 2 : ℝ)) * Real.cos (θ * v) : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))) with hG
  have hθ (n : ℕ) (hn : n ∈ S) {θ : ℝ} (hθ : 2 * Real.pi * k * ((n + 1 : ℕ) : ℝ) ≤ θ) :
      IntegrableOn (G θ) (Ioi 1) ∧ ‖∫ v in Ioi (1 : ℝ), G θ v‖ ≤
        5 / (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) := by
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
    have htθ : |t| ≤ |θ| / 2 := by
      rw [abs_of_pos hθ0]
      have := ht n hn
      nlinarith [Real.pi_pos]
    obtain ⟨hi, hb⟩ := norm_integral_Ioi_one_rpow_mul_cos_mul_cexp_le_of_one_lt
      (p := 3 / 2) (by norm_num) hθ0.ne' htθ
    refine ⟨hi, hb.trans ?_⟩
    rw [abs_of_pos hθ0]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hθ
  have hlam (n : ℕ) : ((n + 1 : ℕ) : ℝ) ≤ factorialShiftedFreq (n + 1) := by
    have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
    linarith
  have hpt : ∀ v, factorialHarmonicLayer S b k v * criticalMellinKernel t v =
      ∑ n ∈ S, b n * (G (2 * Real.pi * k * factorialShiftedFreq (n + 1)) v -
        G (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) v) := by
    intro v
    unfold factorialHarmonicLayer criticalMellinKernel
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hG]
    rw [show 2 * Real.pi * k * factorialShiftedFreq (n + 1) * v =
        2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v) by ring,
      show 2 * Real.pi * k * ((n + 1 : ℕ) : ℝ) * v =
        2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v) by ring,
      show (-(3 / 2 : ℝ)) = -3 / 2 by norm_num]
    push_cast
    ring
  have hint (n : ℕ) (hn : n ∈ S) : IntegrableOn (fun v => b n *
      (G (2 * Real.pi * k * factorialShiftedFreq (n + 1)) v -
        G (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) v)) (Ioi 1) :=
    (((hθ n hn (mul_le_mul_of_nonneg_left (hlam n) (by positivity))).1).sub
      (hθ n hn le_rfl).1).const_mul _
  have hfun : (fun v => factorialHarmonicLayer S b k v * criticalMellinKernel t v) = fun v =>
      ∑ n ∈ S, b n * (G (2 * Real.pi * k * factorialShiftedFreq (n + 1)) v -
        G (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) v) := funext hpt
  rw [hfun]
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  obtain ⟨hiL, hbL⟩ := hθ n hn (mul_le_mul_of_nonneg_left (hlam n) (by positivity))
  obtain ⟨hiN, hbN⟩ := hθ n hn le_rfl
  rw [integral_const_mul, norm_mul, integral_sub hiL hiN]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
  have he : 5 / (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) + 5 / (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) =
      5 / (Real.pi * k * ((n + 1 : ℕ) : ℝ)) := by
    field_simp
    ring
  linarith

/-- **Low-frequency Mellin bound of a critical source.** If `|t| ≤ π (n+1)` for every `n ∈ S`,
then `‖ĝ(t)‖ ≤ D ∑_{n ∈ S} |b_n|/(n+1)` with `D = 15/π³`. -/
theorem norm_paperFT_criticalFactorialSource_le (S : Finset ℕ) (b : ℕ → ℝ) {t : ℝ}
    (ht : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ)) :
    ‖paperFT (fun x => (criticalFactorialSource S b x : ℂ)) t‖ ≤
      factorialLowFreqConstant * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := by
  set bc : ℕ → ℂ := fun n => (b n : ℂ) with hbc
  set T := ∑ n ∈ S, ‖bc n‖ / ((n + 1 : ℕ) : ℝ) with hT
  have hTeq : T = ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := by
    simp only [hT, hbc, Complex.norm_real, Real.norm_eq_abs]
  rw [← hTeq]
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  set Cb := 2 * ∑ n ∈ S, ‖bc n‖ with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set c : ℂ := -((2 / Real.pi ^ 2 : ℝ) : ℂ) with hc
  set F : ℕ → ℝ → ℂ := fun k v => c * (dyadicHarmonicWeight k : ℂ) *
    (factorialHarmonicLayer S bc k v * criticalMellinKernel t v) with hF
  have hreadout : paperFT (fun x => (criticalFactorialSource S b x : ℂ)) t =
      ∫ v in Ioi (1 : ℝ), ∑' k, F k v := by
    rw [paperFT_criticalFactorialSource]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [factorialPhaseCombination_eq_tsum, ← hc]
    simp only [hF]
    rw [show ((v ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (c * ∑' k, (dyadicHarmonicWeight k : ℂ) *
        factorialHarmonicLayer S bc k v) * Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))
        = (∑' k, (dyadicHarmonicWeight k : ℂ) * factorialHarmonicLayer S bc k v) *
          (c * criticalMellinKernel t v) by unfold criticalMellinKernel; ring, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    ring
  have hFk (k : ℕ) : IntegrableOn (F k) (Ioi 1) ∧ ‖∫ v in Ioi (1 : ℝ), F k v‖ ≤
      10 / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF, dyadicHarmonicWeight_zero]
    obtain ⟨hi, hb⟩ := norm_integral_factorialHarmonicLayer_criticalMellinKernel_le S bc hk ht
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    refine ⟨hi.const_mul _, ?_⟩
    simp only [hF]
    rw [integral_const_mul, norm_mul, norm_mul, hc, norm_neg, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
    have hw := abs_dyadicHarmonicWeight_le k
    have hsum : (∑ n ∈ S, ‖bc n‖ * (5 / (Real.pi * k * ((n + 1 : ℕ) : ℝ)))) =
        5 / (Real.pi * k) * T := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      field_simp
    rw [hsum] at hb
    calc 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| *
          ‖∫ v in Ioi (1 : ℝ), factorialHarmonicLayer S bc k v * criticalMellinKernel t v‖ ≤
          2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) * (5 / (Real.pi * k) * T) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hw (by positivity)) hb (norm_nonneg _)
            (by positivity)
      _ = 10 / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T := by
          field_simp
          ring
  have hmeas (k : ℕ) := (hFk k).1
  have hw32 : IntegrableOn (fun v : ℝ => v ^ (-3 / 2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hnormint (k : ℕ) : (∫ v in Ioi (1 : ℝ), ‖F k v‖) ≤
      2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * Cb * 2 := by
    calc (∫ v in Ioi (1 : ℝ), ‖F k v‖) ≤
          ∫ v in Ioi (1 : ℝ),
            2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * Cb * v ^ (-3 / 2 : ℝ) := by
          refine setIntegral_mono_on (hmeas k).norm (hw32.const_mul _)
            measurableSet_Ioi fun v hv => ?_
          have hv0 : 0 < v := lt_trans one_pos hv
          simp only [hF]
          rw [norm_mul, norm_mul, norm_mul, hc, norm_neg, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, norm_criticalMellinKernel hv0]
          have h1 := norm_factorialHarmonicLayer_le S bc k v
          have h2 := Real.rpow_nonneg hv0.le (-3 / 2 : ℝ)
          calc 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| *
                (‖factorialHarmonicLayer S bc k v‖ * v ^ (-3 / 2 : ℝ)) ≤
                2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * (Cb * v ^ (-3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) (by positivity)
            _ = _ := by ring
      _ = 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * Cb * 2 := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
          norm_num
  have hsumm : Summable fun k => ∫ v in Ioi (1 : ℝ), ‖F k v‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) hnormint
      ((summable_abs_dyadicHarmonicWeight.mul_left (2 / Real.pi ^ 2)).mul_right Cb
        |>.mul_right 2)
  rw [hreadout, ← integral_tsum_of_summable_integral_norm hmeas hsumm]
  have hb3 : Summable fun k : ℕ => 10 / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T :=
    ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)).mul_left _).mul_right _
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => (hFk k).2) hb3
  calc (∑' k, ‖∫ v in Ioi (1 : ℝ), F k v‖) ≤ ∑' k : ℕ, 10 / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T :=
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => (hFk k).2) hb3).tsum_le_tsum
          (fun k => (hFk k).2) hb3
    _ = 10 / Real.pi ^ 3 * (∑' k : ℕ, 1 / (k : ℝ) ^ 3) * T := by
        rw [tsum_mul_right, tsum_mul_left]
    _ ≤ 10 / Real.pi ^ 3 * (3 / 2) * T := by
        gcongr
        exact tsum_one_div_nat_cube_le_three_halves
    _ = factorialLowFreqConstant * T := by
        unfold factorialLowFreqConstant
        ring

/-- **Critical low-frequency exclusion (squared form).** For a family supported on
`n + 1 ≥ M ≥ 2` and `|t| ≤ π M`, `‖ĝ(t)‖² ≤ (2 D² / M) ∑ b_n²`. -/
theorem norm_sq_paperFT_criticalFactorialSource_le (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1) {t : ℝ} (ht : |t| ≤ Real.pi * M) :
    ‖paperFT (fun x => (criticalFactorialSource S b x : ℂ)) t‖ ^ 2 ≤
      2 * factorialLowFreqConstant ^ 2 / M * ∑ n ∈ S, b n ^ 2 := by
  have ht' : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ) := fun n hn => ht.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hS n hn) Real.pi_pos.le)
  have h1 := norm_paperFT_criticalFactorialSource_le S b ht'
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  have hcs : T ^ 2 ≤ (∑ n ∈ S, b n ^ 2) * ∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => |b n|) (fun n => 1 / ((n + 1 : ℕ) : ℝ))
    simpa only [hT, mul_one_div, sq_abs] using h
  have hinv : (∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2) ≤ 2 / (M : ℝ) := by
    have h := sum_low_freq_sq_le_two_mul_sq_div (S.map ⟨fun n => n + 1, add_left_injective 1⟩)
      hM (fun N hN => by
        obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hN
        exact hS n hn) 1
    rw [Finset.sum_map] at h
    simpa using h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hS0 : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc _ ≤ (factorialLowFreqConstant * T) ^ 2 := hsq
    _ = factorialLowFreqConstant ^ 2 * T ^ 2 := by ring
    _ ≤ factorialLowFreqConstant ^ 2 * ((∑ n ∈ S, b n ^ 2) * (2 / (M : ℝ))) :=
        mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_left hinv hS0))
          (sq_nonneg _)
    _ = 2 * factorialLowFreqConstant ^ 2 / M * ∑ n ∈ S, b n ^ 2 := by ring

end

end GaloisForLFunctions.ArithmeticPositivityTheory
