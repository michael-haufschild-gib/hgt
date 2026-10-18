import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialPhaseWindowAndPhysicalRieszBounds
import GaloisForLFunctions.«arithmetic-positivity-theory».NonstationaryMellinLowFrequencyExclusion
import GaloisForLFunctions.RHTower.VanDerCorputIBP

/-! Nonstationary bounds for the Mellin phase integrals `∫_1^∞ v^{-5/2} e^{i(ωv - t log v)} dv`.

For `ω ≠ 0` and `|t| ≤ |ω|/2`, the phase derivative `ω - t/v` stays at least `|ω|/2` on
`[1, ∞)`. Integrating by parts against `h(v) = v^{-5/2}/(ω - t/v)` on `[1, X]` bounds the
integral by `|h(1)| + |h(X)| + ∫_1^X |h'|`, with
`|h| ≤ (2/|ω|) v^{-5/2}` and `|h'| ≤ (2/|ω|)(5/2) v^{-7/2} + (4|t|/|ω|²) v^{-9/2}`.
Letting `X → ∞` gives `‖∫_1^∞ v^{-5/2} e^{i(ωv - t log v)}‖ ≤ 5/|ω|`, and averaging the two
exponentials of a cosine gives the same bound for `v^{-5/2} cos(θ v) e^{-it log v}`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The amplitude divided by the phase derivative, `h(v) = v^{-5/2} / (ω - t/v)`. -/
def mellinPhaseAmplitude (ω t v : ℝ) : ℝ :=
  v ^ (-5 / 2 : ℝ) / (ω - t / v)

/-- The derivative of `mellinPhaseAmplitude` in `v`. -/
def mellinPhaseAmplitudeDeriv (ω t v : ℝ) : ℝ :=
  (-5 / 2) * v ^ (-7 / 2 : ℝ) / (ω - t / v) - v ^ (-5 / 2 : ℝ) * (t / v ^ 2) / (ω - t / v) ^ 2

theorem hasDerivAt_mellinPhaseAmplitude {ω t v : ℝ} (hv : 0 < v) (hne : ω - t / v ≠ 0) :
    HasDerivAt (mellinPhaseAmplitude ω t) (mellinPhaseAmplitudeDeriv ω t v) v := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-5 / 2 : ℝ)) ((-5 / 2) * v ^ (-7 / 2 : ℝ)) v := by
    have h := Real.hasDerivAt_rpow_const (p := (-5 / 2 : ℝ)) (x := v) (Or.inl hv.ne')
    rwa [show (-5 / 2 : ℝ) - 1 = -7 / 2 by norm_num] at h
  have h2 : HasDerivAt (fun x : ℝ => ω - t / x) (t / v ^ 2) v := by
    have h := ((hasDerivAt_inv hv.ne').const_mul t).const_sub ω
    simp only [div_eq_mul_inv]
    exact h.congr_deriv (by ring)
  have h := h1.div h2 hne
  unfold mellinPhaseAmplitude mellinPhaseAmplitudeDeriv
  refine h.congr_deriv ?_
  field_simp

/-- On `v ≥ 1` with `|t| ≤ |ω|/2`, the phase derivative `ω - t/v` has modulus at least `|ω|/2`. -/
theorem half_abs_le_abs_phase_deriv {ω t v : ℝ} (hv : 1 ≤ v) (ht : |t| ≤ |ω| / 2) :
    |ω| / 2 ≤ |ω - t / v| := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have htv : |t / v| ≤ |t| := by
    rw [abs_div, abs_of_pos hv0]
    exact div_le_self (abs_nonneg t) hv
  have := abs_sub_abs_le_abs_sub ω (t / v)
  linarith

theorem abs_mellinPhaseAmplitude_le {ω t v : ℝ} (hω : ω ≠ 0) (hv : 1 ≤ v)
    (ht : |t| ≤ |ω| / 2) :
    |mellinPhaseAmplitude ω t v| ≤ 2 / |ω| * v ^ (-5 / 2 : ℝ) := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hω0 : 0 < |ω| := abs_pos.mpr hω
  have hd := half_abs_le_abs_phase_deriv hv ht
  have hd0 : 0 < |ω - t / v| := lt_of_lt_of_le (by positivity) hd
  unfold mellinPhaseAmplitude
  rw [abs_div, abs_of_nonneg (Real.rpow_nonneg hv0.le _), div_le_iff₀ hd0]
  have hp : 0 ≤ v ^ (-5 / 2 : ℝ) := Real.rpow_nonneg hv0.le _
  calc v ^ (-5 / 2 : ℝ) = 2 / |ω| * v ^ (-5 / 2 : ℝ) * (|ω| / 2) := by field_simp
    _ ≤ 2 / |ω| * v ^ (-5 / 2 : ℝ) * |ω - t / v| :=
        mul_le_mul_of_nonneg_left hd (by positivity)

theorem abs_mellinPhaseAmplitudeDeriv_le {ω t v : ℝ} (hω : ω ≠ 0) (hv : 1 ≤ v)
    (ht : |t| ≤ |ω| / 2) :
    |mellinPhaseAmplitudeDeriv ω t v| ≤
      2 / |ω| * ((5 / 2 : ℝ) * v ^ (-7 / 2 : ℝ)) + 4 * |t| / |ω| ^ 2 * v ^ (-9 / 2 : ℝ) := by
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
  have hω0 : 0 < |ω| := abs_pos.mpr hω
  have hd := half_abs_le_abs_phase_deriv hv ht
  have hd0 : 0 < |ω - t / v| := lt_of_lt_of_le (by positivity) hd
  have hp7 : 0 ≤ v ^ (-7 / 2 : ℝ) := Real.rpow_nonneg hv0.le _
  have hp5 : 0 ≤ v ^ (-5 / 2 : ℝ) := Real.rpow_nonneg hv0.le _
  have h9 : v ^ (-5 / 2 : ℝ) / v ^ 2 = v ^ (-9 / 2 : ℝ) := by
    rw [show (-9 / 2 : ℝ) = (-5 / 2) - (2 : ℕ) by norm_num, Real.rpow_sub_natCast hv0.ne']
  have hinv : 1 / |ω - t / v| ≤ 2 / |ω| := by
    rw [div_le_div_iff₀ hd0 hω0]
    linarith
  have hinv2 : 1 / |ω - t / v| ^ 2 ≤ 4 / |ω| ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hinv 2
    rw [div_pow, div_pow, one_pow] at h
    calc 1 / |ω - t / v| ^ 2 ≤ 2 ^ 2 / |ω| ^ 2 := h
      _ = 4 / |ω| ^ 2 := by norm_num
  unfold mellinPhaseAmplitudeDeriv
  refine (abs_sub _ _).trans ?_
  have hA : |(-5 / 2) * v ^ (-7 / 2 : ℝ) / (ω - t / v)| ≤
      2 / |ω| * ((5 / 2 : ℝ) * v ^ (-7 / 2 : ℝ)) := by
    rw [abs_div, abs_mul, abs_of_nonneg hp7, show |(-5 / 2 : ℝ)| = 5 / 2 by norm_num]
    calc 5 / 2 * v ^ (-7 / 2 : ℝ) / |ω - t / v| =
          (5 / 2 * v ^ (-7 / 2 : ℝ)) * (1 / |ω - t / v|) := by ring
      _ ≤ (5 / 2 * v ^ (-7 / 2 : ℝ)) * (2 / |ω|) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hB : |v ^ (-5 / 2 : ℝ) * (t / v ^ 2) / (ω - t / v) ^ 2| ≤
      4 * |t| / |ω| ^ 2 * v ^ (-9 / 2 : ℝ) := by
    rw [abs_div, abs_mul, abs_of_nonneg hp5, abs_div, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2),
      abs_pow]
    calc v ^ (-5 / 2 : ℝ) * (|t| / v ^ 2) / |ω - t / v| ^ 2 =
          (|t| * (v ^ (-5 / 2 : ℝ) / v ^ 2)) * (1 / |ω - t / v| ^ 2) := by ring
      _ ≤ (|t| * (v ^ (-5 / 2 : ℝ) / v ^ 2)) * (4 / |ω| ^ 2) :=
          mul_le_mul_of_nonneg_left hinv2 (by positivity)
      _ = 4 * |t| / |ω| ^ 2 * v ^ (-9 / 2 : ℝ) := by rw [h9]; ring
  linarith

theorem continuousOn_mellinPhaseAmplitudeDeriv {ω t : ℝ} (hω : ω ≠ 0) (ht : |t| ≤ |ω| / 2) :
    ContinuousOn (mellinPhaseAmplitudeDeriv ω t) (Ici 1) := by
  have hne : ∀ v ∈ Ici (1 : ℝ), ω - t / v ≠ 0 := fun v hv => by
    have hd := half_abs_le_abs_phase_deriv (mem_Ici.mp hv) ht
    have hω0 : 0 < |ω| := abs_pos.mpr hω
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hd)
  have hpos : ∀ v ∈ Ici (1 : ℝ), v ≠ 0 := fun v hv => (lt_of_lt_of_le one_pos hv).ne'
  have hrp (p : ℝ) : ContinuousOn (fun v : ℝ => v ^ p) (Ici 1) :=
    continuousOn_id.rpow_const fun v hv => Or.inl (hpos v hv)
  have hden : ContinuousOn (fun v : ℝ => ω - t / v) (Ici 1) :=
    continuousOn_const.sub (continuousOn_const.div continuousOn_id hpos)
  unfold mellinPhaseAmplitudeDeriv
  refine ContinuousOn.sub ((continuousOn_const.mul (hrp _)).div hden hne) ?_
  refine ((hrp _).mul (continuousOn_const.div (continuousOn_id.pow 2)
    fun v hv => pow_ne_zero 2 (hpos v hv))).div (hden.pow 2) fun v hv => pow_ne_zero 2 (hne v hv)

/-- **Nonstationary Mellin bound.** For `ω ≠ 0` and `|t| ≤ |ω|/2`,
`‖∫_1^∞ v^{-5/2} e^{i(ωv - t log v)} dv‖ ≤ 5/|ω|`. Integration by parts on `[1, X]` against
`v^{-5/2}/(i(ω - t/v))` and `X → ∞`. -/
theorem norm_integral_Ioi_one_rpow_mul_cexp_phase_le {ω t : ℝ} (hω : ω ≠ 0)
    (ht : |t| ≤ |ω| / 2) :
    IntegrableOn (fun v : ℝ => ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((ω * v - t * Real.log v : ℝ) : ℂ))) (Ioi 1) ∧
    ‖∫ v in Ioi (1 : ℝ), ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((ω * v - t * Real.log v : ℝ) : ℂ))‖ ≤ 5 / |ω| := by
  set A : ℝ → ℂ := fun v => ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) with hA
  set φ : ℝ → ℝ := fun v => ω * v - t * Real.log v with hφ
  have hω0 : 0 < |ω| := abs_pos.mpr hω
  have hpos : ∀ v ∈ Ici (1 : ℝ), 0 < v := fun v hv => lt_of_lt_of_le one_pos hv
  have hAc : ContinuousOn A (Ici 1) := Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_id.rpow_const fun v hv => Or.inl (hpos v hv).ne')
  have hφc : ContinuousOn φ (Ici 1) := (continuousOn_const.mul continuousOn_id).sub
    (continuousOn_const.mul (Real.continuousOn_log.mono fun v hv => (hpos v hv).ne'))
  have hFc : ContinuousOn (fun v => A v * Complex.exp (Complex.I * (φ v : ℂ))) (Ici 1) :=
    hAc.mul (Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφc)))
  have hw5 : IntegrableOn (fun v : ℝ => v ^ (-5 / 2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hFi : IntegrableOn (fun v => A v * Complex.exp (Complex.I * (φ v : ℂ))) (Ioi 1) := by
    refine hw5.mono' ((hFc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, hA, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)]
  refine ⟨hFi, ?_⟩
  -- the majorant of the derivative term
  set m : ℝ → ℝ := fun v => 2 / |ω| * ((5 / 2 : ℝ) * v ^ (-7 / 2 : ℝ)) +
    4 * |t| / |ω| ^ 2 * v ^ (-9 / 2 : ℝ) with hm
  have hmi : IntegrableOn m (Ioi 1) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul (5 / 2 : ℝ)
      |>.const_mul _).add
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _)
  have hm0 : ∀ v ∈ Ioi (1 : ℝ), 0 ≤ m v := fun v hv => by
    have hv0 : 0 < v := lt_trans one_pos hv
    have := Real.rpow_nonneg hv0.le (-7 / 2 : ℝ)
    have := Real.rpow_nonneg hv0.le (-9 / 2 : ℝ)
    simp only [hm]
    positivity
  set Im : ℝ := ∫ v in Ioi (1 : ℝ), m v with hIm
  have hIm_eq : Im = (2 / |ω|) * (∫ v in Ioi (1 : ℝ), (5 / 2 : ℝ) * v ^ (-7 / 2 : ℝ)) +
      (4 * |t| / |ω| ^ 2) * (∫ v in Ioi (1 : ℝ), v ^ (-9 / 2 : ℝ)) := by
    rw [hIm, hm, integral_add
      (((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul (5 / 2 : ℝ)).const_mul _)
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _)]
    congr 1 <;> exact integral_const_mul _ _
  have hfin : ∀ X : ℝ, 1 ≤ X →
      ‖∫ v in (1 : ℝ)..X, A v * Complex.exp (Complex.I * (φ v : ℂ))‖ ≤
        2 / |ω| * X ^ (-5 / 2 : ℝ) + 2 / |ω| + Im := by
    intro X hX
    have hsub : uIcc (1 : ℝ) X ⊆ Ici 1 := by
      rw [uIcc_of_le hX]
      exact Icc_subset_Ici_self
    set B : ℝ → ℂ := fun v => ((mellinPhaseAmplitude ω t v : ℝ) : ℂ) / Complex.I with hB
    set B' : ℝ → ℂ := fun v => ((mellinPhaseAmplitudeDeriv ω t v : ℝ) : ℂ) / Complex.I
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
      ((hasDerivAt_mellinPhaseAmplitude (hpos x (hsub hx)) (hne x (hsub hx))).ofReal_comp
        ).div_const Complex.I
    have hB'c : ContinuousOn B' (uIcc (1 : ℝ) X) :=
      ((Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_mellinPhaseAmplitudeDeriv hω ht)).div_const Complex.I).mono hsub
    have hrel : ∀ x ∈ uIcc (1 : ℝ) X, B x * (Complex.I * ((ω - t / x : ℝ) : ℂ)) = A x := by
      intro x hx
      have hx' := hne x (hsub hx)
      simp only [hB, hA, mellinPhaseAmplitude]
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have hc : (ω : ℂ) - t / x ≠ 0 := by exact_mod_cast hx'
      push_cast
      field_simp
    have hmain := RHTower.norm_integral_cexp_le_of_antiderivative hX hφd hBd hB'c
      (hAc.mono hsub) hrel
    have hBn (v : ℝ) (hv : 1 ≤ v) : ‖B v‖ ≤ 2 / |ω| * v ^ (-5 / 2 : ℝ) := by
      simp only [hB, norm_div, Complex.norm_I, div_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_mellinPhaseAmplitude_le hω hv ht
    have hB'n : ∀ v ∈ Icc (1 : ℝ) X, ‖B' v‖ ≤ m v := fun v hv => by
      simp only [hB', norm_div, Complex.norm_I, div_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_mellinPhaseAmplitudeDeriv_le hω hv.1 ht
    have hint1 : (∫ v in (1 : ℝ)..X, ‖B' v‖) ≤ Im := by
      have hmon : (∫ v in (1 : ℝ)..X, ‖B' v‖) ≤ ∫ v in (1 : ℝ)..X, m v :=
        intervalIntegral.integral_mono_on hX (hB'c.norm.intervalIntegrable)
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr
            (hmi.mono_set Ioc_subset_Ioi_self)) hB'n
      refine hmon.trans ?_
      rw [intervalIntegral.integral_of_le hX]
      exact setIntegral_mono_set hmi (ae_restrict_of_forall_mem measurableSet_Ioi hm0)
        (Eventually.of_forall fun v hv => hv.1)
    have h1 : (1 : ℝ) ^ (-5 / 2 : ℝ) = 1 := Real.one_rpow _
    have hB1 := hBn 1 le_rfl
    rw [h1, mul_one] at hB1
    linarith [hBn X hX]
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) (1 : ℝ) hFi tendsto_id
  have hrhs : Tendsto (fun X : ℝ => 2 / |ω| * X ^ (-5 / 2 : ℝ) + 2 / |ω| + Im) atTop
      (𝓝 (2 / |ω| * 0 + 2 / |ω| + Im)) := by
    have h := tendsto_rpow_neg_atTop (y := (5 / 2 : ℝ)) (by norm_num)
    rw [show (-(5 / 2 : ℝ)) = -5 / 2 by norm_num] at h
    exact ((h.const_mul _).add_const _).add_const _
  have hle := le_of_tendsto_of_tendsto (hlim.norm) hrhs
    (Filter.eventually_atTop.mpr ⟨1, fun X hX => hfin X hX⟩)
  have h5 := nonstationary_mellin_majorant_le_five_div_abs hω ht
  rw [mul_zero, zero_add, hIm_eq] at hle
  refine le_trans hle ?_
  linarith

/-- Cosine form: `|∫_1^∞ v^{-5/2} cos(θ v) e^{-it log v} dv| ≤ 5/|θ|` for `|t| ≤ |θ|/2`. -/
theorem norm_integral_Ioi_one_rpow_mul_cos_mul_cexp_le {θ t : ℝ} (hθ : θ ≠ 0)
    (ht : |t| ≤ |θ| / 2) :
    IntegrableOn (fun v : ℝ => ((v ^ (-5 / 2 : ℝ) * Real.cos (θ * v) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))) (Ioi 1) ∧
    ‖∫ v in Ioi (1 : ℝ), ((v ^ (-5 / 2 : ℝ) * Real.cos (θ * v) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))‖ ≤ 5 / |θ| := by
  have hθ' : -θ ≠ 0 := neg_ne_zero.mpr hθ
  have ht' : |t| ≤ |-θ| / 2 := by rwa [abs_neg]
  obtain ⟨hi1, hb1⟩ := norm_integral_Ioi_one_rpow_mul_cexp_phase_le hθ ht
  obtain ⟨hi2, hb2⟩ := norm_integral_Ioi_one_rpow_mul_cexp_phase_le hθ' ht'
  have hpt : ∀ v : ℝ, ((v ^ (-5 / 2 : ℝ) * Real.cos (θ * v) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))) =
      (1 / 2 : ℂ) * (((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((θ * v - t * Real.log v : ℝ) : ℂ))) +
      (1 / 2 : ℂ) * (((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) *
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
  have hfun : (fun v : ℝ => ((v ^ (-5 / 2 : ℝ) * Real.cos (θ * v) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))) = fun v =>
      (1 / 2 : ℂ) * (((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((θ * v - t * Real.log v : ℝ) : ℂ))) +
      (1 / 2 : ℂ) * (((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-θ * v - t * Real.log v : ℝ) : ℂ))) := funext hpt
  rw [hfun]
  refine ⟨(hi1.const_mul _).add (hi2.const_mul _), ?_⟩
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  rw [abs_neg] at hb2
  linarith

end

end GaloisForLFunctions.ArithmeticPositivityTheory
