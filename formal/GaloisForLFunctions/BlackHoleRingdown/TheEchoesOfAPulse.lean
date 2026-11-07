import GaloisForLFunctions.BlackHoleRingdown.TheRingdownOfAPulse

/-!
# The echoes of a pulse

For a compact pulse `h` the reflected signal is the pulse convolved with the echo train minus its mean growth:

`𝒮_h(T) = ∫ h(T - τ) (K(τ) - (3/π) e^{τ/2}) dτ`.

Since `K` vanishes on `τ ≤ 0`, the response `h ∗ K` vanishes before the pulse can have reached the first echo:
the wavefront is exact. The horocycle mean of the image field is simply

`∫₀¹ Π_h dx = √Y (h(τ + log Y) + (h ∗ K)(τ - log Y))`,

the incoming pulse and its echoes, with no mean term at all: the mean growth of `𝓕_h` and the constant
`6a(-i/2) e^{τ/2}` cancel.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-- The reflected signal of a pulse. -/
def pulseReflected (h : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∫ ξ : ℝ, pulseAmplitude h (ξ : ℂ) * scatteringPhase ((ξ : ℂ) * I) * Complex.exp (I * (ξ : ℂ) * (T : ℂ))

/-- The response of the echo train to a pulse. -/
def pulseEcho (h : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∫ τ : ℝ, h (T - τ) * ((echoKernel τ : ℝ) : ℂ)

namespace CompactPulse

variable (h : CompactPulse)

/-- The amplitude on the real line against a bounded symbol is integrable. -/
theorem integrable_amplitude_mul {J : ℝ → ℂ} (hJ : Measurable J) (hb : ∀ ξ, ‖J ξ‖ ≤ 1) (T : ℝ) :
    Integrable fun ξ : ℝ => pulseAmplitude h (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ)) := by
  have hint := (h.integrable_amplitude_line 0).norm
  have harg : ∀ y : ℝ, ((y : ℂ) - ((0 : ℝ) : ℂ) * I) = (y : ℂ) := fun y => by simp
  simp only [harg] at hint
  have hcont : Continuous fun ξ : ℝ => pulseAmplitude h (ξ : ℂ) :=
    h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal
  have hexp : Continuous fun ξ : ℝ => Complex.exp (I * (ξ : ℂ) * (T : ℂ)) := by fun_prop
  refine hint.mono' ((hcont.measurable.mul hJ).mul hexp.measurable).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, norm_mul, norm_exp_I_mul, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (hb ξ)

theorem eq_integral_amplitude (S : ℝ) :
    h S = ∫ ξ : ℝ, pulseAmplitude h (ξ : ℂ) * 1 * Complex.exp (I * (ξ : ℂ) * (S : ℂ)) := by
  rw [h.eq_integral_amplitude_line 0 S]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Complex.ofReal_zero, zero_add, mul_one]
  have harg : -I * ((y : ℂ) * I) = y := by linear_combination (-(y : ℂ)) * I_sq
  have he : Complex.exp ((y : ℂ) * I * (S : ℂ)) = Complex.exp (I * (y : ℂ) * (S : ℂ)) := by
    congr 1
    ring
  rw [harg, he]

/-- **The horocycle mean of the packet.** -/
theorem setIntegral_pulsePacket (τ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun x => pulsePacket h τ x Y) (Ioc (0 : ℝ) 1) ∧
      ∫ x in Ioc (0 : ℝ) 1, pulsePacket h τ x Y =
        ((Real.sqrt Y : ℝ) : ℂ) * (h (τ + Real.log Y) + pulseReflected h (τ - Real.log Y)) := by
  obtain ⟨C, M, hC, hE⟩ := exists_eisenstein_jets_line_le_poly hY
  obtain ⟨Ca, hCa, ha⟩ := h.rapidAmplitude.exists_mul_poly_le 0 M
  have hYm := mem_window_self hY
  set F : ℝ → ℝ → ℂ := fun x ξ => pulseAmplitude h (ξ : ℂ) *
    normalizedEisenstein ((ξ : ℂ) * I) x Y * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) with hF
  have hmeasF : Measurable (Function.uncurry F) := by
    have hg : Continuous fun p : ℝ × ℝ => pulseAmplitude h ((p.2 : ℝ) : ℂ) :=
      h.differentiable_amplitude.continuous.comp (Complex.continuous_ofReal.comp continuous_snd)
    have he : Continuous fun p : ℝ × ℝ => Complex.exp (I * ((p.2 : ℝ) : ℂ) * (τ : ℂ)) := by
      fun_prop
    have hE' := (measurable_normalizedEisenstein_pair hY).comp (measurable_swap (α := ℝ) (β := ℝ))
    exact (hg.measurable.mul hE').mul he.measurable
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  have hbound : ∀ x ξ : ℝ, ‖F x ξ‖ ≤ C * Ca * ((1 + |ξ|) ^ 2)⁻¹ := by
    intro x ξ
    simp only [hF]
    rw [norm_mul, norm_mul, norm_exp_I_mul, mul_one]
    have h1 := ha (ξ : ℂ) (by simp)
    simp only [Complex.ofReal_re] at h1
    calc ‖pulseAmplitude h (ξ : ℂ)‖ * ‖normalizedEisenstein ((ξ : ℂ) * I) x Y‖
        ≤ ‖pulseAmplitude h (ξ : ℂ)‖ * (C * (1 + |ξ|) ^ M) :=
          mul_le_mul_of_nonneg_left (hE ξ x Y hYm).1 (norm_nonneg _)
      _ = C * (‖pulseAmplitude h (ξ : ℂ)‖ * (1 + |ξ|) ^ M) := by ring
      _ ≤ C * (Ca * ((1 + |ξ|) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 hC
      _ = _ := by ring
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    have hG : Integrable (fun p : ℝ × ℝ => C * Ca * ((1 + |p.2|) ^ 2)⁻¹)
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) :=
      (integrable_inv_one_add_abs_sq.const_mul (C * Ca)).comp_snd _
    exact hG.mono' hmeasF.aestronglyMeasurable (Eventually.of_forall fun p => hbound p.1 p.2)
  refine ⟨hint.integral_prod_left, ?_⟩
  have hswap := integral_integral_swap (f := F) hint
  simp only [pulsePacket]
  rw [hswap]
  have hinner : ∀ ξ : ℝ, (∫ x in Ioc (0 : ℝ) 1, F x ξ) =
      pulseAmplitude h (ξ : ℂ) * ((Y : ℂ) ^ (1 / 2 + (ξ : ℂ) * I) +
        scatteringPhase ((ξ : ℂ) * I) * (Y : ℂ) ^ (1 / 2 - (ξ : ℂ) * I)) *
          Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by
    intro ξ
    simp only [hF]
    rw [integral_mul_const, integral_const_mul, setIntegral_normalizedEisenstein _ hY]
  simp_rw [hinner]
  have h1 := h.integrable_amplitude_mul (J := fun _ => 1) measurable_const (by simp) (τ + Real.log Y)
  have h2 := h.integrable_amplitude_mul (J := fun ξ => scatteringPhase ((ξ : ℂ) * I))
    continuous_scatteringPhase_line.measurable (fun ξ => (norm_scatteringPhase_line ξ).le)
    (τ - Real.log Y)
  rw [h.eq_integral_amplitude, pulseReflected, ← integral_add h1 h2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [cpow_half_add_eq hY, show (1 / 2 - (ξ : ℂ) * I) = 1 / 2 + (-((ξ : ℂ) * I)) by ring,
    cpow_half_add_eq hY]
  have hexp1 : Complex.exp (I * (ξ : ℂ) * ((τ + Real.log Y : ℝ) : ℂ)) =
      Complex.exp ((ξ : ℂ) * I * (Real.log Y : ℂ)) * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexp2 : Complex.exp (I * (ξ : ℂ) * ((τ - Real.log Y : ℝ) : ℂ)) =
      Complex.exp (-((ξ : ℂ) * I) * (Real.log Y : ℂ)) * Complex.exp (I * (ξ : ℂ) * (τ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp1, hexp2]
  ring

/-! ### The convolution -/

/-- The integrand of the double integral. -/
def echoDouble (T τ y : ℝ) : ℂ :=
  pulseAmplitude h (-I * linePoint 1 y) * Complex.exp (linePoint 1 y * ((T - τ : ℝ) : ℂ)) *
    ((echoKernel τ : ℝ) : ℂ)

theorem integrable_echoDouble (T : ℝ) :
    Integrable (Function.uncurry (h.echoDouble T)) (volume.prod volume) := by
  have hw : 1 / 2 < ((1 : ℝ) : ℂ).re := by norm_num
  have h1 := (integrable_cexp_mul_echoKernel hw).norm
  have hA : Integrable fun y : ℝ => pulseAmplitude h (-I * linePoint 1 y) := by
    have hint := h.integrable_amplitude_line 1
    refine hint.congr (Eventually.of_forall fun y => ?_)
    simp only [linePoint]
    congr 1
    linear_combination (y : ℂ) * I_sq
  have h2 := hA.norm.const_mul (Real.exp (1 * T))
  have hG := h1.mul_prod h2
  have hcA : Continuous fun p : ℝ × ℝ => pulseAmplitude h (-I * linePoint 1 p.2) :=
    h.differentiable_amplitude.continuous.comp (by unfold linePoint; fun_prop)
  have hcE : Continuous fun p : ℝ × ℝ =>
      Complex.exp (linePoint 1 p.2 * ((T - p.1 : ℝ) : ℂ)) := by
    unfold linePoint
    fun_prop
  have hK : Measurable fun p : ℝ × ℝ => ((echoKernel p.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_echoKernel.comp measurable_fst)
  have hmeas : Measurable (Function.uncurry (h.echoDouble T)) :=
    (hcA.measurable.mul hcE.measurable).mul hK
  refine hG.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p => le_of_eq ?_)
  have hE1 : ‖Complex.exp (linePoint 1 p.2 * ((T - p.1 : ℝ) : ℂ))‖ =
      Real.exp (1 * T) * Real.exp (-1 * p.1) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    have : (linePoint 1 p.2 * ((T - p.1 : ℝ) : ℂ)).re = 1 * (T - p.1) := by simp [linePoint]
    rw [this]
    ring
  have hE2 : ‖Complex.exp (-((1 : ℝ) : ℂ) * (p.1 : ℂ))‖ = Real.exp (-1 * p.1) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  show ‖h.echoDouble T p.1 p.2‖ = _
  rw [echoDouble]
  simp only [norm_mul]
  rw [hE1, hE2]
  ring

theorem integral_echoDouble_y (T τ : ℝ) :
    ∫ y : ℝ, h.echoDouble T τ y = h (T - τ) * ((echoKernel τ : ℝ) : ℂ) := by
  simp only [echoDouble]
  rw [integral_mul_const]
  congr 1
  exact (h.eq_integral_amplitude_line 1 (T - τ)).symm

theorem integral_echoDouble_τ (T y : ℝ) :
    ∫ τ : ℝ, h.echoDouble T τ y = pulseAmplitude h (-I * linePoint 1 y) *
      Complex.exp (linePoint 1 y * (T : ℂ)) * scatteringPhase (linePoint 1 y) := by
  have hre : 1 / 2 < (linePoint 1 y).re := by
    rw [linePoint_re]
    norm_num
  have hpoint : ∀ τ : ℝ, h.echoDouble T τ y = pulseAmplitude h (-I * linePoint 1 y) *
      Complex.exp (linePoint 1 y * (T : ℂ)) *
        (Complex.exp (-linePoint 1 y * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ)) := by
    intro τ
    have he : Complex.exp (linePoint 1 y * ((T - τ : ℝ) : ℂ)) =
        Complex.exp (linePoint 1 y * (T : ℂ)) * Complex.exp (-linePoint 1 y * (τ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [echoDouble, he]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_cexp_mul_echoKernel_eq_completed hre,
    completed_div_eq_scatteringPhase hre]

theorem integrable_pulse_mul_echoKernel (T : ℝ) :
    Integrable fun τ : ℝ => h (T - τ) * ((echoKernel τ : ℝ) : ℂ) := by
  have hi := (h.integrable_echoDouble T).integral_prod_left
  refine hi.congr (Eventually.of_forall fun τ => ?_)
  exact h.integral_echoDouble_y T τ

/-- The response on the line `Re w = 1`. -/
theorem pulseEcho_eq_line (T : ℝ) :
    pulseEcho h T = ∫ y : ℝ, pulseAmplitude h (-I * linePoint 1 y) *
      Complex.exp (linePoint 1 y * (T : ℂ)) * scatteringPhase (linePoint 1 y) := by
  have hswap := integral_integral_swap (f := h.echoDouble T) (h.integrable_echoDouble T)
  simp_rw [h.integral_echoDouble_y, h.integral_echoDouble_τ] at hswap
  exact hswap

/-! ### The shift -/

/-- The integrand `a(-iw) e^{wT} φ(½+w)` in regular form. -/
def echoIntegrand (T : ℝ) (w : ℂ) : ℂ :=
  pulseAmplitude h (-I * w) * Complex.exp (w * (T : ℂ)) * ((1 + 2 * w) * (xi (2 * w) / xi (1 + 2 * w))) /
    (2 * w - 1)

theorem echoIntegrand_eq (T : ℝ) (w : ℂ) :
    h.echoIntegrand T w =
      pulseAmplitude h (-I * w) * Complex.exp (w * (T : ℂ)) * scatteringPhase w := by
  rw [echoIntegrand, scatteringPhase]
  field_simp

theorem analyticAt_echoRegular (T : ℝ) {w : ℂ} (hw : 0 ≤ w.re) :
    AnalyticAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v) * Complex.exp (v * (T : ℂ)) *
      ((1 + 2 * v) * (xi (2 * v) / xi (1 + 2 * v)))) w := by
  have h1 : AnalyticAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) w :=
    (h.differentiable_amplitude.comp (by fun_prop : Differentiable ℂ fun v : ℂ => -I * v)).analyticAt w
  have h2 : AnalyticAt ℂ (fun v : ℂ => Complex.exp (v * (T : ℂ))) w := by fun_prop
  have hx1 : AnalyticAt ℂ (fun v : ℂ => xi (1 + 2 * v)) w := differentiable_xi_shift.analyticAt w
  have hx2 : AnalyticAt ℂ (fun v : ℂ => xi (2 * v)) w :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)).analyticAt w
  exact (h1.mul h2).mul ((by fun_prop : AnalyticAt ℂ (fun v : ℂ => 1 + 2 * v) w).mul
    (hx2.div hx1 (xi_shift_ne_zero hw)))

/-- The bound for the integrand on the strip, away from the real axis. -/
theorem exists_norm_echoIntegrand_le (T : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ c → 1 / 2 ≤ |w.im| →
      ‖h.echoIntegrand T w‖ ≤ K * ((1 + |w.im|) ^ 2)⁻¹ := by
  obtain ⟨Ca, hCa, ha⟩ := h.rapidAmplitude.exists_rotated_le c 1
  refine ⟨Real.exp (c * |T|) * (2 + 2 * c) * Ca, by positivity, fun w h0 h1 him => ?_⟩
  have hyn := abs_nonneg w.im
  have hden : 1 ≤ ‖2 * w - 1‖ := by
    have hh := Complex.abs_im_le_norm (2 * w - 1)
    have him2 : (2 * w - 1).im = 2 * w.im := by simp
    rw [him2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    linarith
  have hd : 2 * w - 1 ≠ 0 := by
    intro h0'
    rw [h0', norm_zero] at hden
    linarith
  have hnum : ‖1 + 2 * w‖ ≤ (2 + 2 * c) * (1 + |w.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h3 : (1 + 2 * w).re = 1 + 2 * w.re := by simp
    have h4 : (1 + 2 * w).im = 2 * w.im := by simp
    rw [h3, h4, abs_of_nonneg (by linarith), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_nonneg hc hyn]
  have hphase : ‖scatteringPhase w‖ ≤ (2 + 2 * c) * (1 + |w.im|) :=
    (norm_scatteringPhase_le h0).trans (div_le_of_le_mul₀ (norm_nonneg _) (by positivity)
      (hnum.trans (le_mul_of_one_le_right (by positivity) hden)))
  have hexp : ‖Complex.exp (w * (T : ℂ))‖ ≤ Real.exp (c * |T|) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hr : (w * (T : ℂ)).re = w.re * T := by simp
    rw [hr]
    calc w.re * T ≤ |w.re * T| := le_abs_self _
      _ = w.re * |T| := by rw [abs_mul, abs_of_nonneg h0]
      _ ≤ c * |T| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hA := ha w (abs_le.mpr ⟨by linarith, h1⟩)
  rw [pow_one] at hA
  rw [h.echoIntegrand_eq T, norm_mul, norm_mul]
  calc ‖pulseAmplitude h (-I * w)‖ * ‖Complex.exp (w * (T : ℂ))‖ * ‖scatteringPhase w‖
      ≤ ‖pulseAmplitude h (-I * w)‖ * Real.exp (c * |T|) * ((2 + 2 * c) * (1 + |w.im|)) := by
        gcongr
    _ = Real.exp (c * |T|) * (2 + 2 * c) * (‖pulseAmplitude h (-I * w)‖ * (1 + |w.im|)) := by ring
    _ ≤ Real.exp (c * |T|) * (2 + 2 * c) * (Ca * ((1 + |w.im|) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = _ := by ring

theorem integrable_echoIntegrand_line (T : ℝ) {c : ℝ} (hc : 0 ≤ c) (hc' : c ≠ 1 / 2) :
    Integrable fun y : ℝ => h.echoIntegrand T ((c : ℂ) + (y : ℂ) * I) := by
  obtain ⟨K, -, hK⟩ := h.exists_norm_echoIntegrand_le T hc
  have hre : ∀ y : ℝ, ((c : ℂ) + (y : ℂ) * I).re = c := fun y => by simp
  have him : ∀ y : ℝ, ((c : ℂ) + (y : ℂ) * I).im = y := fun y => by simp
  have hcont : Continuous fun y : ℝ => h.echoIntegrand T ((c : ℂ) + (y : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hd : 2 * ((c : ℂ) + (y : ℂ) * I) - 1 ≠ 0 := fun h0 => hc' (by
      have := congrArg Complex.re h0
      simp at this
      linarith)
    have han : AnalyticAt ℂ (h.echoIntegrand T) ((c : ℂ) + (y : ℂ) * I) :=
      (h.analyticAt_echoRegular T (w := (c : ℂ) + (y : ℂ) * I) (by rw [hre]; exact hc)).div
        (by fun_prop) hd
    exact ContinuousAt.comp (f := fun y : ℝ => (c : ℂ) + (y : ℂ) * I) han.continuousAt (by fun_prop)
  refine integrable_of_continuous_of_inv_sq_tail hcont (R := 1 / 2) (C := K) fun y hy => ?_
  have hb := hK ((c : ℂ) + (y : ℂ) * I) (by rw [hre]; exact hc) (by rw [hre]) (by rw [him]; exact hy)
  rwa [him] at hb

/-- The residue at `w = ½`. -/
theorem laurentCoeff_echoIntegrand (T : ℝ) :
    laurentCoeff (h.echoIntegrand T) (1 / 2) (-1) =
      pulseAmplitude h (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2) * (3 / (Real.pi : ℂ)) := by
  have hre : (0 : ℝ) ≤ ((1 / 2 : ℂ)).re := by norm_num
  have hD : Differentiable ℂ fun w : ℂ => 2 * w - 1 := by fun_prop
  have hder : deriv (fun w : ℂ => 2 * w - 1) (1 / 2) = 2 := by
    have hd : HasDerivAt (fun w : ℂ => 2 * w - 1) 2 (1 / 2) := by
      simpa using ((hasDerivAt_id (1 / 2 : ℂ)).const_mul 2).sub_const 1
    exact hd.deriv
  have heq : laurentCoeff (h.echoIntegrand T) (1 / 2) (-1) =
      laurentCoeff (fun u => (fun v : ℂ => pulseAmplitude h (-I * v) * Complex.exp (v * (T : ℂ)) *
        ((1 + 2 * v) * (xi (2 * v) / xi (1 + 2 * v)))) u / (2 * u - 1)) (1 / 2) (-1) := rfl
  rw [heq, laurentCoeff_div_of_simple_zero (h.analyticAt_echoRegular T hre) hD (by norm_num)
    (by rw [hder]; norm_num), hder]
  have e1 : (2 : ℂ) * (1 / 2) = 1 := by norm_num
  have e2 : (1 : ℂ) + 1 = 2 := by norm_num
  rw [e1, e2, xi_one_div_xi_two, show (1 / 2 : ℂ) * (T : ℂ) = (T : ℂ) / 2 by ring]
  ring

/-- **The shift of the response.** -/
theorem pulseEcho_eq (T : ℝ) :
    pulseEcho h T = pulseReflected h T + meanCoefficient h * Complex.exp ((T : ℂ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := h.exists_norm_echoIntegrand_le T (c := 1) (by norm_num)
  have hLat : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun k : ℕ => K * ((1 + ((k : ℝ) + 1)) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 + ((k : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ hLat
    have h2 : Tendsto (fun k : ℕ => (1 + ((k : ℝ) + 1)) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h1
    simpa using (tendsto_inv_atTop_zero.comp h2).const_mul K
  have hshift := integral_line_shift (f := h.echoIntegrand T) (c := 1) (by norm_num)
    (fun s hs _ hne => (h.analyticAt_echoRegular T hs).div (by fun_prop) (fun h0 =>
      hne (by linear_combination h0 / 2)))
    ((h.analyticAt_echoRegular T (by norm_num : (0 : ℝ) ≤ ((1 / 2 : ℂ)).re)).meromorphicAt.div
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 2 * w - 1) (1 / 2)).meromorphicAt)
    (h.integrable_echoIntegrand_line T (by norm_num) (by norm_num))
    (h.integrable_echoIntegrand_line T le_rfl (by norm_num)) hLat hB
    (Eventually.of_forall fun k q hq s hs => by
      have hre : ((q : ℂ) + (s : ℂ) * I).re = q := by simp
      have him : ((q : ℂ) + (s : ℂ) * I).im = s := by simp
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hb := hK ((q : ℂ) + (s : ℂ) * I) (by rw [hre]; exact hq.1) (by rw [hre]; exact hq.2)
        (by rw [him, hs]; linarith)
      rwa [him, hs] at hb)
  rw [h.laurentCoeff_echoIntegrand] at hshift
  have hright : ∫ y : ℝ, h.echoIntegrand T (((1 : ℝ) : ℂ) + (y : ℂ) * I) = pulseEcho h T := by
    rw [h.pulseEcho_eq_line]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    exact h.echoIntegrand_eq T _
  have hleft : ∫ y : ℝ, h.echoIntegrand T (((0 : ℝ) : ℂ) + (y : ℂ) * I) = pulseReflected h T := by
    rw [pulseReflected]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [h.echoIntegrand_eq T]
    have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
    have harg : -I * ((t : ℂ) * I) = t := by linear_combination (-(t : ℂ)) * I_sq
    have he : Complex.exp ((t : ℂ) * I * (T : ℂ)) = Complex.exp (I * (t : ℂ) * (T : ℂ)) := by
      congr 1
      ring
    rw [e, harg, he]
    ring
  rw [hright, hleft] at hshift
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [sub_eq_iff_eq_add] at hshift
  rw [hshift, meanCoefficient]
  field_simp
  ring

/-! ### The mean growth and the identity -/

theorem integrable_pulse_mul_exp (T : ℝ) :
    Integrable fun τ : ℝ => h (T - τ) * Complex.exp ((τ : ℂ) / 2) := by
  have hint : Integrable fun S : ℝ => h S * Complex.exp (((T - S : ℝ) : ℂ) / 2) := by
    refine Continuous.integrable_of_hasCompactSupport (h.continuous_toFun.mul (by fun_prop)) ?_
    exact h.compact.mul_right
  refine (hint.comp_sub_left T).congr (Eventually.of_forall fun τ => ?_)
  simp only
  rw [sub_sub_cancel]

theorem integral_pulse_mul_exp (T : ℝ) :
    ∫ τ : ℝ, h (T - τ) * Complex.exp ((τ : ℂ) / 2) =
      2 * Real.pi * pulseAmplitude h (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2) := by
  have hsub : ∫ τ : ℝ, h (T - τ) * Complex.exp ((τ : ℂ) / 2) =
      ∫ S : ℝ, h S * Complex.exp (((T - S : ℝ) : ℂ) / 2) := by
    rw [← integral_sub_left_eq_self
      (fun S : ℝ => h S * Complex.exp (((T - S : ℝ) : ℂ) / 2)) volume T]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    rw [sub_sub_cancel]
  have hpoint : ∀ S : ℝ, h S * Complex.exp (((T - S : ℝ) : ℂ) / 2) =
      Complex.exp ((T : ℂ) / 2) * (h S * Complex.exp (-(1 / 2 : ℂ) * (S : ℂ))) := by
    intro S
    have he : Complex.exp (((T - S : ℝ) : ℂ) / 2) =
        Complex.exp ((T : ℂ) / 2) * Complex.exp (-(1 / 2 : ℂ) * (S : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  rw [hsub]
  simp_rw [hpoint]
  rw [integral_const_mul, h.integral_mul_cexp_eq]
  ring

/-- **The echo identity for a compact pulse.** -/
theorem pulseReflected_eq (T : ℝ) :
    pulseReflected h T = ∫ τ : ℝ, h (T - τ) *
      (((echoKernel τ : ℝ) : ℂ) - 3 / (Real.pi : ℂ) * Complex.exp ((τ : ℂ) / 2)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsplit : ∫ τ : ℝ, h (T - τ) *
      (((echoKernel τ : ℝ) : ℂ) - 3 / (Real.pi : ℂ) * Complex.exp ((τ : ℂ) / 2)) =
      (∫ τ : ℝ, h (T - τ) * ((echoKernel τ : ℝ) : ℂ)) -
        3 / (Real.pi : ℂ) * ∫ τ : ℝ, h (T - τ) * Complex.exp ((τ : ℂ) / 2) := by
    rw [← integral_const_mul, ← integral_sub (h.integrable_pulse_mul_echoKernel T)
      ((h.integrable_pulse_mul_exp T).const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    ring
  have he := h.pulseEcho_eq T
  rw [pulseEcho] at he
  rw [hsplit, he, h.integral_pulse_mul_exp, meanCoefficient]
  field_simp
  ring

/-- **The wavefront is exact.**  The response vanishes before the pulse can reach the first echo. -/
theorem pulseEcho_eq_zero {S₀ : ℝ} (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) {T : ℝ} (hT : T < -S₀) :
    pulseEcho h T = 0 := by
  rw [pulseEcho]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun τ => ?_)
  rcases le_or_gt τ 0 with hτ | hτ
  · simp [echoKernel_eq_zero_of_nonpos hτ]
  · have hs : S₀ < |T - τ| := by
      have h1 := neg_abs_le (T - τ)
      linarith
    simp [hS₀ _ hs]

/-- Before the first echo the reflected signal is exactly minus the mean. -/
theorem pulseReflected_before_wavefront {S₀ : ℝ} (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) {T : ℝ}
    (hT : T < -S₀) :
    pulseReflected h T = -(meanCoefficient h * Complex.exp ((T : ℂ) / 2)) := by
  have he := h.pulseEcho_eq T
  rw [h.pulseEcho_eq_zero hS₀ hT] at he
  linear_combination -he

/-- **The horocycle mean of the image field** is the pulse and its echoes, with no mean term. -/
theorem setIntegral_imageField (τ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∫ x in Ioc (0 : ℝ) 1, imageField h τ x Y =
      ((Real.sqrt Y : ℝ) : ℂ) * (h (τ + Real.log Y) + pulseEcho h (τ - Real.log Y)) := by
  obtain ⟨hint, hval⟩ := h.setIntegral_pulsePacket τ hY
  have hfin : volume (Ioc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hconst : IntegrableOn (fun _ : ℝ => meanCoefficient h * Complex.exp ((τ : ℂ) / 2))
      (Ioc 0 1) := integrableOn_const hfin
  have hsplit : ∫ x in Ioc (0 : ℝ) 1, imageField h τ x Y =
      (∫ x in Ioc (0 : ℝ) 1, pulsePacket h τ x Y) +
        ∫ _x in Ioc (0 : ℝ) 1, meanCoefficient h * Complex.exp ((τ : ℂ) / 2) := by
    rw [← integral_add hint hconst]
    exact setIntegral_congr_fun measurableSet_Ioc fun x _ => imageField_eq_packet h τ x hY
  have hone : ∫ _x in Ioc (0 : ℝ) 1, meanCoefficient h * Complex.exp ((τ : ℂ) / 2) =
      meanCoefficient h * Complex.exp ((τ : ℂ) / 2) := by
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioc]
  have hkey : ((Real.sqrt Y : ℝ) : ℂ) * Complex.exp (((τ - Real.log Y : ℝ) : ℂ) / 2) =
      Complex.exp ((τ : ℂ) / 2) := by
    have hs : ((Real.sqrt Y : ℝ) : ℂ) = Complex.exp ((Real.log Y : ℂ) / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hY, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hs, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit, hval, hone, h.pulseEcho_eq]
  linear_combination (-(meanCoefficient h)) * hkey

end CompactPulse

end GaloisForLFunctions.BlackHoleRingdown

end
