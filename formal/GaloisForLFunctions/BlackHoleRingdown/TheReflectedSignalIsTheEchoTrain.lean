import GaloisForLFunctions.BlackHoleRingdown.TheConvolutionOfThePulseWithTheEchoes
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLagariasMeromorphicInner

/-!
# The reflected signal is the echo train

The reflected signal of the Eisenstein wave packet is the incoming pulse convolved with the echo train
minus its mean growth:

`𝒮(T) = ∫ g(T - τ) (K(τ) - (3/π) e^{τ/2}) dτ`.

The convolution with `K` is an integral of `a(-iw) e^{wT} φ(½+w)` on a line `Re w = c > ½`. Moving it to
`Re w = 0` crosses the single pole `w = ½`, of residue `3/π`. The horizontal edges vanish because
`‖ξ(2w)‖ ≤ ‖ξ(1+2w)‖` on `Re w ≥ 0`, so `φ(½+w)` is bounded by a rational factor against the Gaussian
amplitude. This inner bound holds unconditionally, as all zeros lie in `Re s < 1`.

The term `(3/π) e^{τ/2}` is the mode of the constant function on the horizon, and after the lift of decay
`½` it is the zero mode.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### The inner bound -/

theorem xiZeroHalfPlaneBound_half : XiZeroHalfPlaneBound (1 / 2) := fun _ h => by
  have := re_lt_one_of_xi_eq_zero h
  linarith

/-- **The inner bound.**  On `Re w ≥ 0`, one has `‖ξ(2w)‖ ≤ ‖ξ(1+2w)‖`. -/
theorem norm_xi_two_mul_le {w : ℂ} (hw : 0 ≤ w.re) : ‖xi (2 * w)‖ ≤ ‖xi (1 + 2 * w)‖ := by
  rcases hw.eq_or_lt with h | h
  · set s : ℂ := 1 + 2 * w with hs
    have hconj : 2 * w = 1 - (starRingEnd ℂ) s := by
      apply Complex.ext
      · simp [hs, ← h]
      · simp [hs]
    rw [hconj, xi_one_sub, xi_conj, RCLike.norm_conj]
  · have hstrict : ∀ c : ℝ, 1 / 2 < c →
        ‖xi (1 / 2 + 2 * w - (c : ℂ))‖ ≤ ‖xi (1 / 2 + 2 * w + (c : ℂ))‖ := by
      intro c hc
      have hneg : (2 * w * (-I)).im < 0 := by
        simp
        linarith
      have hmain := norm_XiC_vertical_shift_lt_of_halfPlaneBound hc xiZeroHalfPlaneBound_half
        (2 * w * (-I)) hneg
      have e1 : (1 / 2 : ℂ) + (2 * w * (-I) + (c : ℂ) * I) * I = 1 / 2 + 2 * w - (c : ℂ) := by
        linear_combination (-(2 * w) + (c : ℂ)) * I_sq
      have e2 : (1 / 2 : ℂ) + (2 * w * (-I) - (c : ℂ) * I) * I = 1 / 2 + 2 * w + (c : ℂ) := by
        linear_combination (-(2 * w) - (c : ℂ)) * I_sq
      simp only [XiC, e1, e2] at hmain
      exact hmain.le
    have hc1 : Continuous fun c : ℝ => ‖xi (1 / 2 + 2 * w - (c : ℂ))‖ :=
      (xi_differentiable.continuous.comp (by fun_prop)).norm
    have hc2 : Continuous fun c : ℝ => ‖xi (1 / 2 + 2 * w + (c : ℂ))‖ :=
      (xi_differentiable.continuous.comp (by fun_prop)).norm
    have e1 : (1 / 2 : ℂ) + 2 * w - ((1 / 2 : ℝ) : ℂ) = 2 * w := by
      push_cast
      ring
    have e2 : (1 / 2 : ℂ) + 2 * w + ((1 / 2 : ℝ) : ℂ) = 1 + 2 * w := by
      push_cast
      ring
    have hT1 := (hc1.tendsto (1 / 2)).mono_left (nhdsWithin_le_nhds (s := Ioi (1 / 2)))
    have hT2 := (hc2.tendsto (1 / 2)).mono_left (nhdsWithin_le_nhds (s := Ioi (1 / 2)))
    simp only [e1, e2] at hT1 hT2
    refine le_of_tendsto_of_tendsto hT1 hT2 ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact hstrict c hc

/-- On `Re w ≥ 0` the scattering coefficient is dominated by its rational factor. -/
theorem norm_scatteringPhase_le {w : ℂ} (hw : 0 ≤ w.re) :
    ‖scatteringPhase w‖ ≤ ‖1 + 2 * w‖ / ‖2 * w - 1‖ := by
  rw [scatteringPhase, norm_mul, norm_div, norm_div]
  have hne : xi (1 + 2 * w) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
  have hq : ‖xi (2 * w)‖ / ‖xi (1 + 2 * w)‖ ≤ 1 :=
    div_le_one_of_le₀ (norm_xi_two_mul_le hw) (norm_nonneg _)
  exact mul_le_of_le_one_right (by positivity) hq

/-! ### The integrand -/

/-- The integrand `a(-iw) e^{wT} φ(½+w)` of the contour shift. -/
def echoIntegrand (ε ξ₀ T : ℝ) (w : ℂ) : ℂ :=
  gaussianAmplitude ε ξ₀ (-I * w) * Complex.exp (w * (T : ℂ)) * scatteringPhase w

theorem xi_shift_ne_zero {w : ℂ} (hw : 0 ≤ w.re) : xi (1 + 2 * w) ≠ 0 :=
  xi_ne_zero_of_one_le_re (by simp; linarith)

/-- The part of the integrand that is regular at `w = ½`. -/
def echoRegular (ε ξ₀ T : ℝ) (w : ℂ) : ℂ :=
  gaussianAmplitude ε ξ₀ (-I * w) * Complex.exp (w * (T : ℂ)) * (1 + 2 * w) *
    (xi (2 * w) / xi (1 + 2 * w))

theorem echoIntegrand_eq (ε ξ₀ T : ℝ) :
    echoIntegrand ε ξ₀ T = fun w => echoRegular ε ξ₀ T w / (2 * w - 1) := by
  funext w
  simp only [echoIntegrand, echoRegular, scatteringPhase]
  ring

theorem analyticAt_echoRegular (ε ξ₀ T : ℝ) {w : ℂ} (hw : 0 ≤ w.re) :
    AnalyticAt ℂ (echoRegular ε ξ₀ T) w := by
  have h1 : AnalyticAt ℂ (fun v : ℂ => Complex.exp (v * (T : ℂ))) w := by fun_prop
  have h2 : AnalyticAt ℂ (fun v : ℂ => 1 + 2 * v) w := by fun_prop
  have h3 : AnalyticAt ℂ (fun v : ℂ => xi (2 * v)) w :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)).analyticAt w
  have h4 : AnalyticAt ℂ (fun v : ℂ => xi (1 + 2 * v)) w := differentiable_xi_shift.analyticAt w
  exact (((analyticAt_gaussianAmplitude_rotated ε ξ₀ w).mul h1).mul h2).mul
    (h3.div h4 (xi_shift_ne_zero hw))

theorem analyticAt_echoIntegrand (ε ξ₀ T : ℝ) {w : ℂ} (hw : 0 ≤ w.re) (hne : w ≠ 1 / 2) :
    AnalyticAt ℂ (echoIntegrand ε ξ₀ T) w := by
  rw [echoIntegrand_eq]
  have hd : (2 : ℂ) * w - 1 ≠ 0 := fun h => hne (by linear_combination h / 2)
  exact (analyticAt_echoRegular ε ξ₀ T hw).div (by fun_prop) hd

theorem meromorphicAt_echoIntegrand (ε ξ₀ T : ℝ) :
    MeromorphicAt (echoIntegrand ε ξ₀ T) (1 / 2) := by
  rw [echoIntegrand_eq]
  have hre : (0 : ℝ) ≤ ((1 / 2 : ℂ)).re := by norm_num
  exact (analyticAt_echoRegular ε ξ₀ T hre).meromorphicAt.div
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 2 * w - 1) (1 / 2)).meromorphicAt

/-! ### The residue -/

/-- `ξ(1)/ξ(2) = 3/π`, since `ξ(1) = ½` and `ξ(2) = Λ(2) = π/6`. -/
theorem xi_one_div_xi_two : xi 1 / xi 2 = 3 / (Real.pi : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    rw [Complex.Gammaℝ_def]
    have h1 : (-(2 : ℂ) / 2) = -1 := by norm_num
    have h2 : ((2 : ℂ) / 2) = 1 := by norm_num
    rw [h1, h2, Complex.Gamma_one, Complex.cpow_neg_one, mul_one]
  have hz := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
  rw [riemannZeta_two, hG, div_inv_eq_mul] at hz
  have hΛ : completedRiemannZeta 2 = (Real.pi : ℂ) / 6 := by
    field_simp at hz
    field_simp
    linear_combination -hz
  rw [xi_one, xi_two, hΛ]
  field_simp
  norm_num

/-- **The residue at `w = ½`.** -/
theorem laurentCoeff_echoIntegrand (ε ξ₀ T : ℝ) :
    laurentCoeff (echoIntegrand ε ξ₀ T) (1 / 2) (-1) =
      gaussianAmplitude ε ξ₀ (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2) * (3 / (Real.pi : ℂ)) := by
  have hre : (0 : ℝ) ≤ ((1 / 2 : ℂ)).re := by norm_num
  have hD : Differentiable ℂ fun w : ℂ => 2 * w - 1 := by fun_prop
  have hder : deriv (fun w : ℂ => 2 * w - 1) (1 / 2) = 2 := by
    have h : HasDerivAt (fun w : ℂ => 2 * w - 1) 2 (1 / 2) := by
      simpa using ((hasDerivAt_id (1 / 2 : ℂ)).const_mul 2).sub_const 1
    exact h.deriv
  rw [echoIntegrand_eq, laurentCoeff_div_of_simple_zero (analyticAt_echoRegular ε ξ₀ T hre) hD
    (by norm_num) (by rw [hder]; norm_num), hder, echoRegular]
  have e1 : (2 : ℂ) * (1 / 2) = 1 := by norm_num
  have e2 : (1 : ℂ) + 1 = 2 := by norm_num
  rw [e1, e2, xi_one_div_xi_two, show (1 / 2 : ℂ) * (T : ℂ) = (T : ℂ) / 2 by ring]
  ring

/-! ### Bounds -/

/-- The integrand is Gaussian on the strip `0 ≤ Re w ≤ c`, away from the real axis. -/
theorem exists_norm_echoIntegrand_le {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ c → 1 / 2 ≤ |w.im| →
      ‖echoIntegrand ε ξ₀ T w‖ ≤ K * Real.exp (-(ε / 4) * w.im ^ 2) := by
  obtain ⟨C₁, hC₁, hcmp⟩ := exists_one_add_pow_mul_exp_le_gaussian 1 (b := 0) (c := ε / 4)
    (by positivity)
  refine ⟨Real.exp (ε * c ^ 2 + ε * ξ₀ ^ 2) * Real.exp (c * |T|) * ((2 + 2 * c) * C₁),
    by positivity, fun w h0 h1 him => ?_⟩
  have hyn := abs_nonneg w.im
  have hre2 : w.re ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ h0 h1 2
  have hamp : ‖gaussianAmplitude ε ξ₀ (-I * w)‖ ≤
      Real.exp (ε * c ^ 2 + ε * ξ₀ ^ 2) * Real.exp (-(ε / 2) * w.im ^ 2) := by
    rw [norm_gaussianAmplitude_rotated, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hε.le (sq_nonneg (w.im - 2 * ξ₀)), mul_le_mul_of_nonneg_left hre2 hε.le]
  have hexp : ‖Complex.exp (w * (T : ℂ))‖ ≤ Real.exp (c * |T|) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hr : (w * (T : ℂ)).re = w.re * T := by simp
    rw [hr]
    calc w.re * T ≤ |w.re * T| := le_abs_self _
      _ = w.re * |T| := by rw [abs_mul, abs_of_nonneg h0]
      _ ≤ c * |T| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hden : 1 ≤ ‖2 * w - 1‖ := by
    have h := Complex.abs_im_le_norm (2 * w - 1)
    have him2 : (2 * w - 1).im = 2 * w.im := by simp
    rw [him2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  have hnum : ‖1 + 2 * w‖ ≤ (2 + 2 * c) * (1 + |w.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h3 : (1 + 2 * w).re = 1 + 2 * w.re := by simp
    have h4 : (1 + 2 * w).im = 2 * w.im := by simp
    rw [h3, h4, abs_of_nonneg (by linarith), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_nonneg hc hyn]
  have hphase : ‖scatteringPhase w‖ ≤ (2 + 2 * c) * (1 + |w.im|) :=
    (norm_scatteringPhase_le h0).trans ((div_le_of_le_mul₀ (norm_nonneg _) (by positivity)
      (hnum.trans (le_mul_of_one_le_left (by positivity) hden))))
  have hpoly := hcmp |w.im| hyn
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one, sq_abs] at hpoly
  have hgauss : Real.exp (-(ε / 2) * w.im ^ 2) * Real.exp (ε / 4 * w.im ^ 2) =
      Real.exp (-(ε / 4) * w.im ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [echoIntegrand, norm_mul, norm_mul]
  calc ‖gaussianAmplitude ε ξ₀ (-I * w)‖ * ‖Complex.exp (w * (T : ℂ))‖ * ‖scatteringPhase w‖
      ≤ (Real.exp (ε * c ^ 2 + ε * ξ₀ ^ 2) * Real.exp (-(ε / 2) * w.im ^ 2)) * Real.exp (c * |T|) *
          ((2 + 2 * c) * (C₁ * Real.exp (ε / 4 * w.im ^ 2))) :=
        mul_le_mul (mul_le_mul hamp hexp (norm_nonneg _) (by positivity))
          (hphase.trans (mul_le_mul_of_nonneg_left hpoly (by positivity))) (norm_nonneg _)
          (by positivity)
    _ = Real.exp (ε * c ^ 2 + ε * ξ₀ ^ 2) * Real.exp (c * |T|) * ((2 + 2 * c) * C₁) *
          (Real.exp (-(ε / 2) * w.im ^ 2) * Real.exp (ε / 4 * w.im ^ 2)) := by ring
    _ = _ := by rw [hgauss]

/-- The integrand is integrable on every line `Re w = c`, `c ≥ 0`, that misses the pole. -/
theorem integrable_echoIntegrand_line {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hc' : c ≠ 1 / 2) : Integrable fun y : ℝ => echoIntegrand ε ξ₀ T ((c : ℂ) + (y : ℂ) * I) := by
  obtain ⟨K, -, hK⟩ := exists_norm_echoIntegrand_le hε ξ₀ T hc
  have hre : ∀ y : ℝ, ((c : ℂ) + (y : ℂ) * I).re = c := fun y => by simp
  have him : ∀ y : ℝ, ((c : ℂ) + (y : ℂ) * I).im = y := fun y => by simp
  have hcont : Continuous fun y : ℝ => echoIntegrand ε ξ₀ T ((c : ℂ) + (y : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hne : ((c : ℂ) + (y : ℂ) * I) ≠ 1 / 2 := fun h => hc' (by
      have := congrArg Complex.re h
      rw [hre] at this
      simpa using this)
    have han := analyticAt_echoIntegrand ε ξ₀ T (w := (c : ℂ) + (y : ℂ) * I) (by rw [hre]; exact hc) hne
    exact ContinuousAt.comp (f := fun y : ℝ => (c : ℂ) + (y : ℂ) * I) han.continuousAt
      (by fun_prop)
  refine integrable_of_continuous_of_gaussian_tail hcont (R := 1 / 2) (C := K) (c := ε / 4)
    (by positivity) fun y hy => ?_
  have h := hK _ (by rw [hre]; exact hc) (by rw [hre]) (by rw [him]; exact hy)
  rwa [him] at h

/-! ### The contour shift -/

/-- The residue theorem on the rectangle `[0, c] × [-L, L]`. -/
theorem rectangleIntegral'_echoIntegrand (ε ξ₀ T : ℝ) {c L : ℝ} (hc : 1 / 2 < c) (hL : 0 < L) :
    RectangleIntegral' (echoIntegrand ε ξ₀ T) ⟨0, -L⟩ ⟨c, L⟩ =
      laurentCoeff (echoIntegrand ε ξ₀ T) (1 / 2) (-1) := by
  have hre1 : (0 : ℝ) ≤ c := by linarith
  have him1 : -L ≤ L := by linarith
  have h := rectangleIntegral'_eq_sum_laurentCoeff (f := echoIntegrand ε ξ₀ T)
    (z := ⟨0, -L⟩) (w := ⟨c, L⟩) (P := {1 / 2}) hre1 him1 ?_ ?_ ?_
  · simpa using h
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm]
    simp only
    rw [uIoo_of_le hre1, uIoo_of_le him1]
    constructor
    · constructor
      · norm_num
      · simpa using hc
    · constructor
      · simpa using hL
      · simpa using hL
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact meromorphicAt_echoIntegrand ε ξ₀ T
  · intro s hs hsP
    rw [Rectangle, Complex.mem_reProdIm] at hs
    simp only at hs
    rw [uIcc_of_le hre1] at hs
    refine analyticAt_echoIntegrand ε ξ₀ T hs.1.1 fun he => hsP ?_
    rw [Finset.mem_singleton]
    exact he

/-- **The contour shift.**  Moving the line `Re w = c > ½` to `Re w = 0` picks up the pole at `w = ½`. -/
theorem integral_echoIntegrand_shift {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    (∫ y : ℝ, echoIntegrand ε ξ₀ T ((c : ℂ) + (y : ℂ) * I)) -
        ∫ y : ℝ, echoIntegrand ε ξ₀ T (((0 : ℝ) : ℂ) + (y : ℂ) * I) =
      2 * Real.pi * laurentCoeff (echoIntegrand ε ξ₀ T) (1 / 2) (-1) := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  obtain ⟨K, hK0, hK⟩ := exists_norm_echoIntegrand_le hε ξ₀ T hc0
  have hbound : Tendsto (fun L : ℝ => K * Real.exp (-(ε / 4) * L ^ 2) * c) atTop (𝓝 0) := by
    have hsq : Tendsto (fun L : ℝ => ε / 4 * L ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop (by positivity)
    have hexp : Tendsto (fun L : ℝ => Real.exp (-(ε / 4) * L ^ 2)) atTop (𝓝 0) := by
      refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsq)).congr fun L => ?_
      simp only [Function.comp_def]
      congr 1
      ring
    simpa using (hexp.const_mul K).mul_const c
  have hEdge : ∀ s : ℝ, s = 1 ∨ s = -1 → Tendsto
      (fun L : ℝ => HIntegral (echoIntegrand ε ξ₀ T) 0 c (s * L)) atTop (𝓝 0) := by
    intro s hs
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    rw [HIntegral]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := c)
      (f := fun x : ℝ => echoIntegrand ε ξ₀ T ((x : ℂ) + ((s * L : ℝ) : ℂ) * I))
      (C := K * Real.exp (-(ε / 4) * L ^ 2)) (fun x hx => by
        rw [uIoc_of_le hc0] at hx
        have hre : ((x : ℂ) + ((s * L : ℝ) : ℂ) * I).re = x := by simp
        have him : ((x : ℂ) + ((s * L : ℝ) : ℂ) * I).im = s * L := by simp
        have habs : |s * L| = L := by
          rcases hs with rfl | rfl
          · rw [one_mul, abs_of_nonneg (by linarith)]
          · rw [neg_one_mul, abs_neg, abs_of_nonneg (by linarith)]
        have h := hK _ (by rw [hre]; exact hx.1.le) (by rw [hre]; exact hx.2)
          (by rw [him, habs]; linarith)
        rw [him, ← sq_abs (s * L), habs] at h
        exact h)
    refine hb.trans (le_of_eq ?_)
    rw [sub_zero, abs_of_nonneg hc0]
  have hBot := hEdge (-1) (Or.inr rfl)
  have hTop := hEdge 1 (Or.inl rfl)
  simp only [neg_one_mul, one_mul] at hBot hTop
  have hlow : Tendsto (fun L : ℝ => -L) atTop atBot := tendsto_neg_atTop_atBot
  have hR := intervalIntegral_tendsto_integral
    (integrable_echoIntegrand_line hε ξ₀ T hc0 hc.ne') hlow tendsto_id
  have hL := intervalIntegral_tendsto_integral
    (integrable_echoIntegrand_line hε ξ₀ T (c := 0) le_rfl (by norm_num)) hlow tendsto_id
  have hmain := ((hBot.sub hTop).add (hR.const_smul I)).sub (hL.const_smul I)
  have hscaled := hmain.const_smul ((1 : ℂ) / (2 * Real.pi * I))
  have hlimit : ((1 : ℂ) / (2 * Real.pi * I)) •
      ((0 - 0 + I • ∫ y : ℝ, echoIntegrand ε ξ₀ T ((c : ℂ) + (y : ℂ) * I)) -
        I • ∫ y : ℝ, echoIntegrand ε ξ₀ T (((0 : ℝ) : ℂ) + (y : ℂ) * I)) =
      (2 * Real.pi : ℂ)⁻¹ * ((∫ y : ℝ, echoIntegrand ε ξ₀ T ((c : ℂ) + (y : ℂ) * I)) -
        ∫ y : ℝ, echoIntegrand ε ξ₀ T (((0 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hlimit] at hscaled
  have hconst : Tendsto (fun L : ℝ => RectangleIntegral' (echoIntegrand ε ξ₀ T) ⟨0, -L⟩ ⟨c, L⟩)
      atTop (𝓝 (laurentCoeff (echoIntegrand ε ξ₀ T) (1 / 2) (-1))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL0
    exact (rectangleIntegral'_echoIntegrand ε ξ₀ T hc hL0).symm
  have huniq := tendsto_nhds_unique (hscaled.congr fun L => ?_) hconst
  · have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    rw [← huniq, mul_inv_cancel_left₀ hpi]
  · simp only [RectangleIntegral', RectangleIntegral, VIntegral]
    simp

/-! ### The echo identity -/

/-- On the line `Re w = 0` the integrand is the integrand of the reflected signal. -/
theorem integral_echoIntegrand_zero (ε ξ₀ T : ℝ) :
    ∫ y : ℝ, echoIntegrand ε ξ₀ T (((0 : ℝ) : ℂ) + (y : ℂ) * I) = reflectedSignal ε ξ₀ T := by
  rw [reflectedSignal, packet]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Complex.ofReal_zero, zero_add, echoIntegrand]
  have h : -I * ((y : ℂ) * I) = y := by linear_combination (-(y : ℂ)) * I_sq
  have he : Complex.exp ((y : ℂ) * I * (T : ℂ)) = Complex.exp (I * (y : ℂ) * (T : ℂ)) := by
    congr 1
    ring
  rw [h, he]
  ring

/-- The convolution of the pulse with the echo train. -/
theorem integral_pulse_mul_echoKernel {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) :
    ∫ τ : ℝ, incomingPulse ε ξ₀ (T - τ) * ((echoKernel τ : ℝ) : ℂ) =
      reflectedSignal ε ξ₀ T +
        6 * gaussianAmplitude ε ξ₀ (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2) := by
  have hc : (1 / 2 : ℝ) < 1 := by norm_num
  have hline := integral_pulse_mul_echoKernel_eq_line hε ξ₀ T hc
  have hshift := integral_echoIntegrand_shift hε ξ₀ T hc
  rw [integral_echoIntegrand_zero, laurentCoeff_echoIntegrand] at hshift
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hval : (∫ y : ℝ, echoIntegrand ε ξ₀ T (((1 : ℝ) : ℂ) + (y : ℂ) * I)) =
      reflectedSignal ε ξ₀ T +
        6 * gaussianAmplitude ε ξ₀ (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2) := by
    rw [sub_eq_iff_eq_add] at hshift
    rw [hshift]
    field_simp
    ring
  rw [hline, ← hval]
  rfl

/-- **The echo identity.**  The reflected signal is the pulse convolved with the echo train minus its
mean growth. -/
theorem reflectedSignal_eq_echoConvolution {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) :
    reflectedSignal ε ξ₀ T = ∫ τ : ℝ, incomingPulse ε ξ₀ (T - τ) *
      (((echoKernel τ : ℝ) : ℂ) - 3 / (Real.pi : ℂ) * Complex.exp ((τ : ℂ) / 2)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsplit : ∫ τ : ℝ, incomingPulse ε ξ₀ (T - τ) *
      (((echoKernel τ : ℝ) : ℂ) - 3 / (Real.pi : ℂ) * Complex.exp ((τ : ℂ) / 2)) =
      (∫ τ : ℝ, incomingPulse ε ξ₀ (T - τ) * ((echoKernel τ : ℝ) : ℂ)) -
        3 / (Real.pi : ℂ) * ∫ τ : ℝ, incomingPulse ε ξ₀ (T - τ) * Complex.exp ((τ : ℂ) / 2) := by
    rw [← integral_const_mul, ← integral_sub (integrable_pulse_mul_echoKernel hε ξ₀ T)
      ((integrable_pulse_mul_exp hε ξ₀ T).const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    ring
  rw [hsplit, integral_pulse_mul_echoKernel hε, integral_pulse_mul_exp hε]
  field_simp
  ring

/-- **The horocycle mean in terms of the echoes.**  The constant term of the wave packet is the incoming
pulse together with its echoes, minus their mean growth. -/
theorem setIntegral_wavePacket_echo {ε : ℝ} (hε : 0 < ε) (ξ₀ τ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∫ x in Ioc (0 : ℝ) 1, wavePacket ε ξ₀ τ x Y =
      ((Real.sqrt Y : ℝ) : ℂ) * (incomingPulse ε ξ₀ (τ + Real.log Y) +
        ∫ σ : ℝ, incomingPulse ε ξ₀ (τ - Real.log Y - σ) *
          (((echoKernel σ : ℝ) : ℂ) - 3 / (Real.pi : ℂ) * Complex.exp ((σ : ℂ) / 2))) := by
  rw [setIntegral_wavePacket hε, reflectedSignal_eq_echoConvolution hε]

end GaloisForLFunctions.BlackHoleRingdown

end
