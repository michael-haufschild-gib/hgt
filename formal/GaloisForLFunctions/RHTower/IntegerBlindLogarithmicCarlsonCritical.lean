import GaloisForLFunctions.RHTower.IntegerBlindLogarithmicCarlsonSharpness

/-!
# The critical constant `K = π/2` of the logarithmic Carlson threshold

With room `e^{(π/2)|t| − K|t|/log(|t|+3)}`, integer blindness of `w ∈ L¹` forces `ŵ ≡ 0` for
`K < π/2` (`fourier_eq_zero_of_integerMoment_eq_zero_logRoom`), and fails for `K > π/2`
(`exists_integerBlind_logRoom`).  This file settles the boundary.

**Theorem** (`fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom_critical`,
`logRoom_integerBlind_iff`).  Blindness at a node set `N ⊆ [2,∞)` with `Σ_{n∈N} 1/(n log n) = ∞`
forces `ŵ ≡ 0` also at `K = π/2`.  Hence, for every real `K`, integer blindness with room `K`
forces vanishing **iff `K ≤ π/2`**.

**Proof.**  The sharp supremum
`sup_{s ≥ 0} (K s/log(s+3) − δ s) ≤ K e^{K/(2δ)} + (2δ²/K) e^{K/δ}` replaces `K e^{K/δ}` in the
growth bound of `G(ζ) = ∫ w(t) ζ^{-it} dt`.  After the narrowing `u ↦ u/log u` the angle is
`δ ≥ (π/2)/(log|u| + 2)`, so at `K = π/2` the dominant term becomes
`π e² · w(|u|)`, `w(x) = x/(log x + 2)²`, instead of `|u|`.  The function `x ↦ w(M/|1−z|)` has
uniformly bounded circle averages: the primitive `M/(log(M/(ε+θ)) + 2)` integrates it in closed
form.  Jensen's formula and the divergence of `Σ 1/(n log n)` conclude as in the subcritical case
(`eqOn_zero_of_logNarrow_circleAverage_le`).
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real

noncomputable section

namespace RHTower.PrimeBlindCarlson

/-- `K s/log(s+3) − δ s ≤ K e^{K/(2δ)} + (2δ²/K) e^{K/δ}` for `s ≥ 0`. -/
theorem mul_div_log_sub_le_sharp {K δ s : ℝ} (hK : 0 < K) (hδ : 0 < δ) (hs : 0 ≤ s) :
    K * s / Real.log (s + 3) - δ * s ≤
      K * Real.exp (K / (2 * δ)) + 2 * δ ^ 2 / K * Real.exp (K / δ) := by
  set L := Real.log (s + 3) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < L := by linarith
  have hR1 : 0 ≤ K * Real.exp (K / (2 * δ)) := by positivity
  have hR2 : 0 ≤ 2 * δ ^ 2 / K * Real.exp (K / δ) := by positivity
  rcases le_or_gt K (δ * L) with h | h
  · have : K * s / L ≤ δ * s := by
      rw [div_le_iff₀ hL0]; nlinarith
    linarith
  · set m := K / δ with hm
    have hKm : K = δ * m := by rw [hm, mul_div_cancel₀ _ hδ.ne']
    have hLm : L < m := by rw [hm, lt_div_iff₀ hδ]; linarith
    have hse : s ≤ Real.exp L := by
      rw [hLdef, Real.exp_log (by linarith)]; linarith
    have heq : K * s / L - δ * s = δ * s * (m - L) / L := by
      rw [hKm]; field_simp
    rw [heq]
    have hmL : 0 < m - L := by linarith
    rcases le_or_gt L (m / 2) with h2 | h2
    · -- `(m − L)/L ≤ m` and `s ≤ e^{m/2}`
      have h3 : (m - L) / L ≤ m := by
        rw [div_le_iff₀ hL0]; nlinarith
      have h4 : s ≤ Real.exp (m / 2) := hse.trans (Real.exp_le_exp.mpr h2)
      have h5 : δ * s * (m - L) / L ≤ δ * Real.exp (m / 2) * m := by
        have : δ * s * (m - L) / L = δ * s * ((m - L) / L) := by ring
        rw [this]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h4 hδ.le) h3
          (div_nonneg hmL.le hL0.le) (by positivity)
      have h6 : δ * Real.exp (m / 2) * m = K * Real.exp (K / (2 * δ)) := by
        rw [hKm, show δ * m / (2 * δ) = m / 2 by field_simp]; ring
      linarith
    · -- `(m − L) e^L ≤ e^{m−1}` and `1/L < 2/m`
      have hm0 : 0 < m := by linarith
      have h3 : (m - L) * Real.exp L ≤ Real.exp m := by
        have h := Real.add_one_le_exp (m - L - 1)
        have hE : Real.exp (m - L - 1) * Real.exp L ≤ Real.exp m := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
        nlinarith [Real.exp_pos L]
      have h4 : δ * s * (m - L) / L ≤ δ * Real.exp m * (2 / m) := by
        rw [div_le_iff₀ hL0]
        have h5 : δ * s * (m - L) ≤ δ * Real.exp m := by
          have : s * (m - L) ≤ Real.exp L * (m - L) := mul_le_mul_of_nonneg_right hse hmL.le
          nlinarith
        have h6 : δ * Real.exp m ≤ δ * Real.exp m * (2 / m) * L := by
          have : 1 ≤ 2 / m * L := by rw [div_mul_eq_mul_div, le_div_iff₀ hm0]; linarith
          have hp : 0 ≤ δ * Real.exp m := by positivity
          nlinarith
        linarith
      have h7 : δ * Real.exp m * (2 / m) = 2 * δ ^ 2 / K * Real.exp (K / δ) := by
        rw [hKm, show δ * m / δ = m by field_simp]; field_simp
      linarith

theorem exp_le_logRoomWeight_mul_sharp {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) (t : ℝ) :
    Real.exp ((π / 2 - δ) * |t|) ≤ logRoomWeight K t *
      Real.exp (K * Real.exp (K / (2 * δ)) + 2 * δ ^ 2 / K * Real.exp (K / δ)) := by
  unfold logRoomWeight
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have := mul_div_log_sub_le_sharp hK hδ (abs_nonneg t)
  linarith

variable {w : ℝ → ℂ}

/-- **Sharp growth with logarithmic room.**
`|G(ζ)| ≤ B exp(K e^{K/(2η)} + (2η²/K) e^{K/η})`, `η = π/2 − |arg ζ|`. -/
theorem norm_logFourier_le_logRoom_sharp {K : ℝ} (hK : 0 < K)
    (hroom : Integrable fun t => ‖w t‖ * logRoomWeight K t) {ζ : ℂ} (hζ : 0 < ζ.re) :
    ‖logFourier w ζ‖ ≤ (∫ t, ‖w t‖ * logRoomWeight K t) *
      Real.exp (K * Real.exp (K / (2 * (π / 2 - |ζ.arg|))) +
        2 * (π / 2 - |ζ.arg|) ^ 2 / K * Real.exp (K / (π / 2 - |ζ.arg|))) := by
  set η := π / 2 - |ζ.arg| with hη
  have hη0 : 0 < η := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ); linarith
  unfold logFourier
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hroom.mul_const _) ?_
  filter_upwards with t
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (norm_cexp_log_le_of_abs_arg_le (a := π / 2 - η) (by rw [hη]; ring_nf; rfl) t).trans
    (exp_le_logRoomWeight_mul_sharp hK hη0 t)

/-- `e^a/(a+2)² ≤ e^b/(b+2)²` for `0 ≤ a ≤ b`. -/
theorem exp_div_sq_add_two_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp a / (a + 2) ^ 2 ≤ Real.exp b / (b + 2) ^ 2 := by
  rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos (by linarith) 2)]
  set r := b - a with hr
  have hr0 : 0 ≤ r := by linarith
  have h1 : 1 + r / 2 ≤ Real.exp (r / 2) := by linarith [Real.add_one_le_exp (r / 2)]
  have h2 : (1 + r / 2) ^ 2 ≤ Real.exp r := by
    have : Real.exp (r / 2) ^ 2 = Real.exp r := by rw [← Real.exp_nat_mul]; ring_nf
    rw [← this]; exact pow_le_pow_left₀ (by linarith) h1 2
  have h3 : (b + 2) ^ 2 ≤ (a + 2) ^ 2 * (1 + r / 2) ^ 2 := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by linarith)
    rw [hr]; nlinarith
  have hb : Real.exp b = Real.exp a * Real.exp r := by rw [← Real.exp_add]; congr 1; ring
  rw [hb]
  have hea := Real.exp_pos a
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (a + 2) ^ 2),
    mul_le_mul_of_nonneg_left h3 hea.le]

/-- `x/(log x + 2)²`. -/
def logSqRoomWeight (x : ℝ) : ℝ := x / (Real.log x + 2) ^ 2

theorem logSqWeight_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : logSqRoomWeight x ≤ logSqRoomWeight y := by
  unfold logSqRoomWeight
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have h := exp_div_sq_add_two_mono (Real.log_nonneg hx) (Real.log_le_log hx0 hxy)
  rwa [Real.exp_log hx0, Real.exp_log hy0] at h

theorem logSqWeight_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ logSqRoomWeight x := by
  unfold logSqRoomWeight; positivity

theorem hasDerivAt_logSq_primitive {M ε θ : ℝ} (hM : 0 < M) (hθ : 0 < ε + θ)
    (hpos : 0 < Real.log (M / (ε + θ)) + 2) :
    HasDerivAt (fun x : ℝ => M * (Real.log M - Real.log (ε + x) + 2)⁻¹)
      (logSqRoomWeight (M / (ε + θ))) θ := by
  have hlog : Real.log (M / (ε + θ)) = Real.log M - Real.log (ε + θ) :=
    Real.log_div hM.ne' hθ.ne'
  have h1 : HasDerivAt (fun x : ℝ => Real.log (ε + x)) (1 / (ε + θ)) θ := by
    have := ((hasDerivAt_id θ).const_add ε).log (by simpa using hθ.ne')
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => Real.log M - Real.log (ε + x) + 2) (-(1 / (ε + θ))) θ := by
    simpa using (h1.const_sub (Real.log M)).add_const 2
  have hne : Real.log M - Real.log (ε + θ) + 2 ≠ 0 := by rw [← hlog]; exact hpos.ne'
  have h3 := (h2.inv hne).const_mul M
  refine h3.congr_deriv ?_
  unfold logSqRoomWeight
  rw [hlog]
  field_simp

theorem continuousOn_logSqWeight_shift {M ε : ℝ} (hM : 4 * π ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ContinuousOn (fun θ : ℝ => logSqRoomWeight (M / (ε + θ))) (uIcc 0 (2 * π)) := by
  have hπ := Real.pi_gt_three
  have hM0 : 0 < M := by linarith
  unfold logSqRoomWeight
  have hden : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), ε + θ ≠ 0 := by
    intro θ hθ; rw [uIcc_of_le (by positivity)] at hθ; linarith [hθ.1]
  have hq : ContinuousOn (fun θ : ℝ => M / (ε + θ)) (uIcc 0 (2 * π)) :=
    continuousOn_const.div (by fun_prop) hden
  refine hq.div ((hq.log fun θ hθ => ?_).add continuousOn_const |>.pow 2) fun θ hθ => ?_
  · rw [uIcc_of_le (by positivity)] at hθ
    exact (div_pos hM0 (by linarith [hθ.1])).ne'
  · rw [uIcc_of_le (by positivity)] at hθ
    have : 0 ≤ Real.log (M / (ε + θ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith [hθ.1])]; linarith [hθ.2]
    positivity

/-- `∫_0^{2π} w(M/(ε+θ)) dθ ≤ M/2` for `w(x) = x/(log x + 2)²`, `M ≥ 4π`, `0 < ε ≤ 1`. -/
theorem integral_logSqWeight_shift_le {M ε : ℝ} (hM : 4 * π ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ θ in (0 : ℝ)..2 * π, logSqRoomWeight (M / (ε + θ)) ≤ M / 2 := by
  have hπ := Real.pi_gt_three
  have hM0 : 0 < M := by linarith
  have hlogpos : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), 0 ≤ Real.log (M / (ε + θ)) := by
    intro θ hθ
    rw [uIcc_of_le (by positivity)] at hθ
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith [hθ.1])]; linarith [hθ.2]
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt
      (fun x : ℝ => M * (Real.log M - Real.log (ε + x) + 2)⁻¹)
      (logSqRoomWeight (M / (ε + θ))) θ := by
    intro θ hθ
    have hθ0 : 0 ≤ θ := by rw [uIcc_of_le (by positivity)] at hθ; exact hθ.1
    exact hasDerivAt_logSq_primitive hM0 (by linarith) (by linarith [hlogpos θ hθ])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_logSqWeight_shift hM hε hε1).intervalIntegrable]
  have hθ2 : (2 * π) ∈ uIcc (0 : ℝ) (2 * π) := by rw [uIcc_of_le (by positivity)]; simp; positivity
  have hθ0 : (0 : ℝ) ∈ uIcc (0 : ℝ) (2 * π) := by rw [uIcc_of_le (by positivity)]; simp; positivity
  have hl2 := hlogpos _ hθ2
  have hl0 := hlogpos _ hθ0
  have e2 : Real.log M - Real.log (ε + 2 * π) = Real.log (M / (ε + 2 * π)) :=
    (Real.log_div hM0.ne' (by linarith)).symm
  have e0 : Real.log M - Real.log (ε + 0) = Real.log (M / (ε + 0)) :=
    (Real.log_div hM0.ne' (by linarith)).symm
  rw [e2, e0]
  have hA : M * (Real.log (M / (ε + 2 * π)) + 2)⁻¹ ≤ M / 2 := by
    rw [← div_eq_mul_inv]; exact div_le_div_of_nonneg_left hM0.le (by norm_num) (by linarith)
  have hB : 0 ≤ M * (Real.log (M / (ε + 0)) + 2)⁻¹ := by
    have : 0 < Real.log (M / (ε + 0)) + 2 := by linarith
    positivity
  linarith

theorem integral_logSqWeight_shift_reflect_le {M ε : ℝ} (hM : 4 * π ≤ M) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∫ θ in (0 : ℝ)..2 * π, logSqRoomWeight (M / (ε + (2 * π - θ))) ≤ M / 2 := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => logSqRoomWeight (M / (ε + x))) (2 * π) (a := 0) (b := 2 * π)
  simp only [sub_zero, sub_self] at h
  rw [h]
  exact integral_logSqWeight_shift_le hM hε hε1

/-- **Bounded circle averages at the critical exponent.**  For `M ≥ 4` and `1/2 ≤ R < 1`,
`avg_{|z| = R} w(M/|1 − z|) ≤ M/2` with `w(x) = x/(log x + 2)²`. -/
theorem circleAverage_logSqWeight_le {M R : ℝ} (hM : 4 ≤ M) (hR : 1 / 2 ≤ R) (hR1 : R < 1) :
    Real.circleAverage (fun z => logSqRoomWeight (M / ‖1 - z‖)) 0 R ≤ M / 2 := by
  set ε := 2 * (1 - R) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  have hπ := Real.pi_gt_three
  have hM0 : 0 < M := by linarith
  have hne : ∀ θ : ℝ, 1 - circleMap 0 R θ ≠ 0 := by
    intro θ h
    have : circleMap 0 R θ = 1 := by linear_combination -h
    have hn := norm_circleMap_zero R θ
    rw [this, norm_one, abs_of_pos (by linarith)] at hn
    linarith
  have hle2 : ∀ θ : ℝ, ‖1 - circleMap 0 R θ‖ ≤ 2 := by
    intro θ
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_circleMap_zero, abs_of_pos (by linarith)]; linarith
  have hge1 : ∀ θ : ℝ, 1 ≤ M / ‖1 - circleMap 0 R θ‖ := by
    intro θ
    have hp : 0 < ‖1 - circleMap 0 R θ‖ := norm_pos_iff.mpr (hne θ)
    rw [le_div_iff₀ hp]; linarith [hle2 θ]
  have hpt : ∀ θ ∈ Icc (0 : ℝ) (2 * π), logSqRoomWeight (M / ‖1 - circleMap 0 R θ‖) ≤
      logSqRoomWeight (M * π / (ε + θ)) + logSqRoomWeight (M * π / (ε + (2 * π - θ))) := by
    intro θ hθ
    set u := min θ (2 * π - θ) with hu
    have hu0 : 0 ≤ u := le_min hθ.1 (by linarith [hθ.2])
    have hge : (ε + u) / π ≤ ‖1 - circleMap 0 R θ‖ := norm_one_sub_circleMap_ge hR hR1 hθ.1 hθ.2
    have hp : 0 < ‖1 - circleMap 0 R θ‖ := norm_pos_iff.mpr (hne θ)
    have hup : M / ‖1 - circleMap 0 R θ‖ ≤ M * π / (ε + u) := by
      rw [div_le_div_iff₀ hp (by linarith)]
      have h1 := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℝ) ≤ M * π)
      have h2 : M * π * ((ε + u) / π) = M * (ε + u) := by field_simp
      linarith
    have h1 := logSqWeight_mono (hge1 θ) hup
    have hA : 0 ≤ logSqRoomWeight (M * π / (ε + θ)) :=
      logSqWeight_nonneg (div_nonneg (by positivity) (by linarith [hθ.1]))
    have hB : 0 ≤ logSqRoomWeight (M * π / (ε + (2 * π - θ))) :=
      logSqWeight_nonneg (div_nonneg (by positivity) (by linarith [hθ.2]))
    rcases min_choice θ (2 * π - θ) with h | h <;> rw [hu, h] at h1 <;> linarith
  have hcz : Continuous fun θ : ℝ => M / ‖1 - circleMap 0 R θ‖ :=
    continuous_const.div (continuous_const.sub (continuous_circleMap 0 R)).norm
      fun θ => norm_ne_zero_iff.mpr (hne θ)
  have hi1 : IntervalIntegrable (fun θ => logSqRoomWeight (M / ‖1 - circleMap 0 R θ‖)) volume
      0 (2 * π) := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold logSqRoomWeight
    refine hcz.div ((hcz.log fun θ => ?_).add continuous_const |>.pow 2) fun θ => ?_
    · exact (lt_of_lt_of_le one_pos (hge1 θ)).ne'
    · have := Real.log_nonneg (hge1 θ); positivity
  have hMπ : 4 * π ≤ M * π := by nlinarith
  have hcA := (continuousOn_logSqWeight_shift hMπ hε0 hε1).intervalIntegrable (μ := volume)
  have hcB : IntervalIntegrable (fun θ : ℝ => logSqRoomWeight (M * π / (ε + (2 * π - θ)))) volume
      0 (2 * π) := by
    have h := hcA.comp_sub_left (2 * π)
    simp only [sub_zero, sub_self] at h
    exact h.symm
  have hi2 := hcA.add hcB
  have hmono := intervalIntegral.integral_mono_on Real.two_pi_pos.le hi1 hi2 fun θ hθ => hpt θ hθ
  rw [intervalIntegral.integral_add hcA hcB] at hmono
  have h1 := integral_logSqWeight_shift_le hMπ hε0 hε1
  have h2 := integral_logSqWeight_shift_reflect_le hMπ hε0 hε1
  rw [Real.circleAverage_def, smul_eq_mul]
  calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, logSqRoomWeight (M / ‖1 - circleMap 0 R θ‖)
      ≤ (2 * π)⁻¹ * (M * π / 2 + M * π / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = M / 2 := by field_simp; ring

/-- `e^m/m² ≤ e² + e^{m₀}/m₀²` for `1 ≤ m ≤ m₀`, `2 ≤ m₀`. -/
theorem exp_div_sq_le_of_le {m m₀ : ℝ} (hm : 1 ≤ m) (hmm : m ≤ m₀) (hm₀ : 2 ≤ m₀) :
    Real.exp m / m ^ 2 ≤ Real.exp 2 + Real.exp m₀ / m₀ ^ 2 := by
  have h0 : 0 ≤ Real.exp m₀ / m₀ ^ 2 := by positivity
  rcases le_or_gt m 2 with h | h
  · have h1 : Real.exp m / m ^ 2 ≤ Real.exp m := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ m ^ 2 := by nlinarith
      nlinarith [Real.exp_pos m]
    have h2 : Real.exp m ≤ Real.exp 2 := Real.exp_le_exp.mpr h
    linarith
  · have hmono := exp_div_sq_add_two_mono (a := m - 2) (b := m₀ - 2) (by linarith) (by linarith)
    rw [show m - 2 + 2 = m by ring, show m₀ - 2 + 2 = m₀ by ring] at hmono
    have e1 : Real.exp m / m ^ 2 = Real.exp 2 * (Real.exp (m - 2) / m ^ 2) := by
      rw [← mul_div_assoc, ← Real.exp_add]; ring_nf
    have e2 : Real.exp m₀ / m₀ ^ 2 = Real.exp 2 * (Real.exp (m₀ - 2) / m₀ ^ 2) := by
      rw [← mul_div_assoc, ← Real.exp_add]; ring_nf
    rw [e1]
    have := mul_le_mul_of_nonneg_left hmono (Real.exp_pos 2).le
    have h3 : Real.exp 2 * (Real.exp (m₀ - 2) / m₀ ^ 2) ≤ Real.exp m₀ / m₀ ^ 2 := le_of_eq e2.symm
    linarith [Real.exp_pos 2]


/-! ## The narrowing `z ↦ u/log u`, `u = e⁴ + (1+z)/(1−z)`, as a map -/

/-- `u(z) = e⁴ + (1+z)/(1−z)`. -/
def narrowBase (z : ℂ) : ℂ := (Real.exp 4 : ℂ) + cayley z

/-- `Ψ(z) = u(z)/log u(z)`. -/
def logNarrow (z : ℂ) : ℂ := narrowBase z / Complex.log (narrowBase z)

theorem re_narrowBase_gt {z : ℂ} (hz : ‖z‖ < 1) : Real.exp 4 < (narrowBase z).re := by
  simp only [narrowBase, Complex.add_re, Complex.ofReal_re]; linarith [re_cayley_pos hz]

theorem four_le_log_norm_narrowBase {z : ℂ} (hz : ‖z‖ < 1) : 4 ≤ Real.log ‖narrowBase z‖ := by
  have h1 : Real.exp 4 ≤ ‖narrowBase z‖ := (re_narrowBase_gt hz).le.trans (Complex.re_le_norm _)
  calc (4 : ℝ) = Real.log (Real.exp 4) := by rw [Real.log_exp]
    _ ≤ _ := Real.log_le_log (Real.exp_pos 4) h1

theorem logNarrow_mem {z : ℂ} (hz : ‖z‖ < 1) : 0 < (logNarrow z).re ∧
    π / 2 / (Real.log ‖narrowBase z‖ + 2) ≤ π / 2 - |(logNarrow z).arg| :=
  re_div_log_pos_and_le (by linarith [re_narrowBase_gt hz, Real.exp_pos 4])
    (four_le_log_norm_narrowBase hz)

theorem log_narrowBase_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : Complex.log (narrowBase z) ≠ 0 := by
  intro h
  have h4 := four_le_log_norm_narrowBase hz
  have h2 : (Complex.log (narrowBase z)).re = Real.log ‖narrowBase z‖ := Complex.log_re _
  rw [h, Complex.zero_re] at h2; linarith

theorem analyticAt_logNarrow {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ logNarrow z := by
  have hc : AnalyticAt ℂ narrowBase z :=
    analyticAt_const.add ((analyticAt_const.add analyticAt_id).div
      (analyticAt_const.sub analyticAt_id) (one_sub_ne_zero_of_norm_lt hz))
  have hslit : narrowBase z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [re_narrowBase_gt hz, Real.exp_pos 4]))
  exact hc.div (hc.clog hslit) (log_narrowBase_ne_zero hz)

theorem norm_narrowBase_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖narrowBase z‖ ≤ 2 * (Real.exp 4 + 1) * ‖1 - z‖⁻¹ := by
  have hn1 : 0 < ‖1 - z‖ := norm_pos_iff.mpr (one_sub_ne_zero_of_norm_lt hz)
  have hn12 : ‖1 - z‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hinv : 1 / 2 ≤ ‖1 - z‖⁻¹ := by rw [one_div]; exact inv_anti₀ hn1 hn12
  have hcay : ‖cayley z‖ ≤ 2 * ‖1 - z‖⁻¹ := by
    rw [cayley, norm_div, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have hW := Real.exp_pos 4
  have h1 : ‖narrowBase z‖ ≤ Real.exp 4 + 2 * ‖1 - z‖⁻¹ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hW]; linarith
  nlinarith

theorem norm_logNarrow_le {z : ℂ} (hz : ‖z‖ < 1) : ‖logNarrow z‖ ≤ ‖narrowBase z‖ := by
  have hlogu1 : 1 ≤ ‖Complex.log (narrowBase z)‖ := by
    have h2 : (Complex.log (narrowBase z)).re = Real.log ‖narrowBase z‖ := Complex.log_re _
    have := Complex.re_le_norm (Complex.log (narrowBase z))
    linarith [four_le_log_norm_narrowBase hz]
  unfold logNarrow; rw [norm_div]
  exact div_le_self (norm_nonneg _) hlogu1

/-- **Narrowed Jensen uniqueness.**  If `G` is analytic on `Re ζ > 0`, the circle averages of
`log |G ∘ Ψ|` are bounded on `1/2 ≤ R < 1`, and `G` vanishes on `N ⊆ [2, ∞)` with
`Σ_{n ∈ N} 1/(n log n) = ∞`, then `G ≡ 0`. -/
theorem eqOn_zero_of_logNarrow_circleAverage_le {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G rightHalf)
    {B : ℝ} (havg : ∀ R : ℝ, 1 / 2 ≤ R → R < 1 →
      Real.circleAverage (fun z => Real.log ‖G (logNarrow z)‖) 0 R ≤ B)
    {N : Set ℕ} (hN2 : ∀ n ∈ N, 2 ≤ n)
    (hdiv : ¬ Summable (N.indicator fun n : ℕ => 1 / ((n : ℝ) * Real.log n)))
    (hz : ∀ n ∈ N, G n = 0) : EqOn G 0 rightHalf := by
  classical
  set W : ℝ := Real.exp 4 with hW
  have hW1 : 1 ≤ W := Real.one_le_exp (by norm_num)
  have hπ := Real.pi_gt_three
  set u : ℂ → ℂ := narrowBase with hu
  set Ψ : ℂ → ℂ := logNarrow with hΨ
  set f : ℂ → ℂ := fun z => G (Ψ z) with hf
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := by
    intro z hz1
    have hz1' : ‖z‖ < 1 := by simpa using hz1
    exact AnalyticAt.comp (g := G) (f := Ψ) (hG _ (logNarrow_mem hz1').1)
      (analyticAt_logNarrow hz1')
  -- the narrowing on the real axis
  have hΨnode : ∀ y : ℝ, W + 2 ≤ y → Ψ (realNode (y - W)) = ((y / Real.log y : ℝ) : ℂ) := by
    intro y hy
    have hy0 : 0 < y - W := by linarith
    have hu' : u (realNode (y - W)) = (y : ℂ) := by
      show ((Real.exp 4 : ℝ) : ℂ) + cayley (realNode (y - W)) = (y : ℂ)
      rw [cayley_realNode hy0, ← Complex.ofReal_add]
      congr 1; rw [hW]; ring
    show u (realNode (y - W)) / Complex.log (u (realNode (y - W))) = _
    rw [hu', ← Complex.ofReal_log (by linarith), ← Complex.ofReal_div]
  -- the nodes `x_n / log x_n = n`
  have hex : ∀ n : ℕ, W + 2 ≤ (n : ℝ) →
      ∃ y, W + 2 ≤ y ∧ y ≤ (n : ℝ) ^ 2 ∧ y / Real.log y = n :=
    fun n hn => exists_div_log_eq hW1 hn
  set xs : ℕ → ℝ := fun n =>
    if h : W + 2 ≤ (n : ℝ) then Classical.choose (hex n h) else 0 with hxs
  have hxs_spec : ∀ n : ℕ, W + 2 ≤ (n : ℝ) →
      W + 2 ≤ xs n ∧ xs n ≤ (n : ℝ) ^ 2 ∧ xs n / Real.log (xs n) = n := by
    intro n hn
    simp only [hxs, dif_pos hn]
    exact Classical.choose_spec (hex n hn)
  set a : ℕ → ℂ := fun n => realNode (xs n - W) with ha
  set N' : Set ℕ := {n | n ∈ N ∧ W + 2 ≤ (n : ℝ)} with hN'
  have hnodes : ∀ n ∈ N', ‖a n‖ < 1 ∧ a n ≠ 0 ∧ f (a n) = 0 := by
    intro n hn
    obtain ⟨h1, -, h3⟩ := hxs_spec n hn.2
    refine ⟨norm_realNode_lt_one (by linarith), realNode_ne_zero (by linarith), ?_⟩
    show G (Ψ (realNode (xs n - W))) = 0
    rw [hΨnode _ h1, h3, Complex.ofReal_natCast]
    exact hz n hn.1
  have hinj : Set.InjOn a N' := by
    intro m hm n hn hmn
    have hm1 := (hxs_spec m hm.2).1
    have hn1 := (hxs_spec n hn.2).1
    have h := congrArg cayley hmn
    simp only [ha, cayley_realNode (by linarith : 0 < xs m - W),
      cayley_realNode (by linarith : 0 < xs n - W)] at h
    have hx : xs m = xs n := by have := Complex.ofReal_injective h; linarith
    have hm3 := (hxs_spec m hm.2).2.2
    have hn3 := (hxs_spec n hn.2).2.2
    rw [hx] at hm3
    exact_mod_cast hm3.symm.trans hn3
  -- `f ≡ 0`
  have hf0 : ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
    by_contra hcon
    push Not at hcon
    have hsum := summable_log_inv_of_circleAverage_le hfan havg hcon hinj hnodes
    apply hdiv
    set g : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log n) with hg
    have hgnn : ∀ n ∈ N, 0 ≤ g n := by
      intro n hn
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hN2 n hn
      have := Real.log_pos (by linarith : (1 : ℝ) < n)
      simp only [hg]; positivity
    have hle : ∀ n ∈ N', g n ≤ Real.log ‖a n‖⁻¹ := by
      intro n hn
      obtain ⟨h1, h2, h3⟩ := hxs_spec n hn.2
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hN2 n hn.1
      have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
      have hxpos : 0 < xs n := by linarith
      have hlogx : 0 < Real.log (xs n) := Real.log_pos (by linarith)
      have hxeq : xs n = n * Real.log (xs n) := by
        field_simp at h3; linarith
      have hlogle : Real.log (xs n) ≤ 2 * Real.log n := by
        calc Real.log (xs n) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hxpos h2
          _ = 2 * Real.log n := by rw [Real.log_pow]; push_cast; ring
      have hxle : xs n ≤ 2 * (n * Real.log n) := by
        rw [hxeq]; nlinarith
      have hnode := two_div_le_log_inv_realNode (by linarith : 1 < xs n - W)
      have hstep : g n ≤ 2 / (xs n - W + 1) := by
        simp only [hg]
        rw [div_le_div_iff₀ (by positivity) (by linarith)]
        nlinarith
      exact hstep.trans hnode
    have hfin : Summable ((N \ N').indicator g) := by
      refine summable_of_ne_finset_zero (s := Finset.range (⌈W + 2⌉₊)) fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      have hn' : W + 2 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      rw [Set.indicator_of_notMem]
      rintro ⟨hnN, hnN'⟩
      exact hnN' ⟨hnN, hn'⟩
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hsum.add hfin)
    · by_cases hn : n ∈ N
      · rw [Set.indicator_of_mem hn]; exact hgnn n hn
      · simp [hn]
    · by_cases hn : n ∈ N
      · rw [Set.indicator_of_mem hn]
        by_cases hn' : n ∈ N'
        · rw [Set.indicator_of_mem hn', Set.indicator_of_notMem (fun h => h.2 hn')]
          linarith [hle n hn']
        · rw [Set.indicator_of_notMem hn', Set.indicator_of_mem (show n ∈ N \ N' from ⟨hn, hn'⟩), zero_add]
      · rw [Set.indicator_of_notMem hn]
        have h1 : 0 ≤ N'.indicator (fun n => Real.log ‖a n‖⁻¹) n := by
          by_cases hn' : n ∈ N'
          · rw [Set.indicator_of_mem hn']
            exact Real.log_nonneg ((one_le_inv₀ (norm_pos_iff.mpr (hnodes n hn').2.1)).mpr
              (hnodes n hn').1.le)
          · simp [hn']
        have h2 : 0 ≤ (N \ N').indicator g n := by simp [Set.indicator_of_notMem, hn]
        linarith
  -- `G` vanishes on the real ray `[W + 2, ∞)`, hence everywhere
  have hGv : ∀ v : ℝ, W + 2 ≤ v → G (v : ℂ) = 0 := by
    intro v hv
    obtain ⟨y, hy1, -, hyv⟩ := exists_div_log_eq hW1 hv
    have hz : realNode (y - W) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]; exact norm_realNode_lt_one (by linarith)
    have h := hf0 _ hz
    simp only [hf] at h
    rwa [hΨnode y hy1, hyv] at h
  show EqOn G 0 rightHalf
  set z₀ : ℂ := ((W + 3 : ℝ) : ℂ) with hz₀def
  have hz₀ : z₀ ∈ rightHalf := by
    show 0 < z₀.re; rw [hz₀def, Complex.ofReal_re]; linarith
  refine hG.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_rightHalf hz₀ ?_
  have ht : Tendsto (fun k : ℕ => ((W + 3 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (W + 3)
      rw [add_zero] at h
      exact (Complex.continuous_ofReal.tendsto _).comp h
    · simp only [mem_compl_iff, mem_singleton_iff, hz₀def]
      intro h
      have h' := Complex.ofReal_injective h
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  exact ht.frequently (Frequently.of_forall fun k => hGv _ (by
    have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    linarith))

/-! ## Growth after the narrowing at the critical constant -/

/-- First critical term: `(π/2) e^{(π/2)/(2δ)} ≤ (π/2) e √x` when `δ ≥ (π/2)/(log x + 2)`. -/
theorem exp_half_le_critical {x δ : ℝ} (hx : 0 < x) (hδ : π / 2 / (Real.log x + 2) ≤ δ)
    (hL : 0 < Real.log x + 2) :
    π / 2 * Real.exp (π / 2 / (2 * δ)) ≤ π / 2 * Real.exp 1 * Real.sqrt x := by
  have hδ0 : 0 < π / 2 / (Real.log x + 2) := by positivity
  have hδpos : 0 < δ := lt_of_lt_of_le hδ0 hδ
  have hm : π / 2 / δ ≤ Real.log x + 2 := by
    calc π / 2 / δ ≤ π / 2 / (π / 2 / (Real.log x + 2)) :=
          div_le_div_of_nonneg_left (by positivity) hδ0 hδ
      _ = Real.log x + 2 := by field_simp
  have hsq : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]; ring_nf
  rw [hsq, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have : π / 2 / (2 * δ) = (π / 2 / δ) / 2 := by field_simp
  rw [this]; linarith

/-- Second critical term: `(2δ²/(π/2)) e^{(π/2)/δ} ≤ π e² (1 + w(x))` when
`(π/2)/(log x + 2) ≤ δ ≤ π/2` and `log x ≥ 0`. -/
theorem sq_mul_exp_le_critical {x δ : ℝ} (hx : 1 ≤ x) (hδ : π / 2 / (Real.log x + 2) ≤ δ)
    (hδ' : δ ≤ π / 2) :
    2 * δ ^ 2 / (π / 2) * Real.exp (π / 2 / δ) ≤
      π * Real.exp 2 + π * Real.exp 2 * logSqRoomWeight x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL : 0 < Real.log x + 2 := by linarith
  have hδ0 : 0 < π / 2 / (Real.log x + 2) := by positivity
  have hδpos : 0 < δ := lt_of_lt_of_le hδ0 hδ
  set m := π / 2 / δ with hmdef
  have hm1 : 1 ≤ m := by rw [hmdef, le_div_iff₀ hδpos]; linarith
  have hm_le : m ≤ Real.log x + 2 := by
    calc m ≤ π / 2 / (π / 2 / (Real.log x + 2)) :=
          div_le_div_of_nonneg_left (by positivity) hδ0 hδ
      _ = Real.log x + 2 := by field_simp
  have hkey := exp_div_sq_le_of_le hm1 hm_le (by linarith)
  have hw : Real.exp (Real.log x + 2) / (Real.log x + 2) ^ 2 = Real.exp 2 * logSqRoomWeight x := by
    unfold logSqRoomWeight; rw [Real.exp_add, Real.exp_log hx0]; ring
  rw [hw] at hkey
  have e1 : 2 * δ ^ 2 / (π / 2) * Real.exp m = π * (Real.exp m / m ^ 2) := by
    rw [hmdef]; field_simp
  rw [e1]
  have := mul_le_mul_of_nonneg_left hkey Real.pi_pos.le
  linarith

/-- **Pointwise bound after the narrowing at `K = π/2`.** -/
theorem log_norm_comp_logNarrow_le_critical {G : ℂ → ℂ} {A : ℝ} (c : ℕ)
    (hgrowth : ∀ ζ : ℂ, 0 < ζ.re →
      ‖G ζ‖ ≤ A * Real.exp (π / 2 * Real.exp (π / 2 / (2 * (π / 2 - |ζ.arg|))) +
        2 * (π / 2 - |ζ.arg|) ^ 2 / (π / 2) * Real.exp (π / 2 / (π / 2 - |ζ.arg|))) *
          (1 + ‖ζ‖) ^ c)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Real.log ‖G (logNarrow z)‖ ≤ Real.log (max A 1) + π * Real.exp 2 +
      π * Real.exp 2 * logSqRoomWeight (2 * (Real.exp 4 + 1) / ‖1 - z‖) +
      (π / 2 * Real.exp 1 * Real.sqrt (2 * (Real.exp 4 + 1)) +
        2 * c * Real.sqrt (2 * (Real.exp 4 + 1))) * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by
  set M : ℝ := 2 * (Real.exp 4 + 1) with hM
  have hpi := Real.pi_pos
  have hn1 : 0 < ‖1 - z‖ := norm_pos_iff.mpr (one_sub_ne_zero_of_norm_lt hz)
  have hn12 : ‖1 - z‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hM4 : 4 ≤ M := by rw [hM]; linarith [Real.add_one_le_exp (4 : ℝ)]
  have hMz : 1 ≤ M / ‖1 - z‖ := by rw [le_div_iff₀ hn1]; linarith
  have hw0 : 0 ≤ logSqRoomWeight (M / ‖1 - z‖) := logSqWeight_nonneg (by positivity)
  have hA1 : 1 ≤ max A 1 := le_max_right _ _
  have hlogA : 0 ≤ Real.log (max A 1) := Real.log_nonneg hA1
  have hrpow : 0 ≤ ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hn1.le _
  rcases eq_or_ne (G (logNarrow z)) 0 with h0 | h0
  · rw [h0, norm_zero, Real.log_zero]
    have : 0 ≤ (π / 2 * Real.exp 1 * Real.sqrt M + 2 * c * Real.sqrt M) *
      ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by positivity
    have : 0 ≤ π * Real.exp 2 * logSqRoomWeight (M / ‖1 - z‖) := by positivity
    have : 0 ≤ π * Real.exp 2 := by positivity
    linarith
  obtain ⟨hre, hδ⟩ := logNarrow_mem hz
  set x := ‖narrowBase z‖ with hx
  have hL4 := four_le_log_norm_narrowBase hz
  rw [← hx] at hL4
  have hx1 : 1 ≤ x := by
    have := Real.exp_le_exp.mpr hL4
    rw [Real.exp_log (by
      rw [hx]; exact lt_of_lt_of_le (by linarith [re_narrowBase_gt hz, Real.exp_pos 4])
        (Complex.re_le_norm _))] at this
    linarith [Real.add_one_le_exp (4 : ℝ)]
  have hx0 : 0 < x := by linarith
  have hδ' : π / 2 - |(logNarrow z).arg| ≤ π / 2 := by linarith [abs_nonneg (logNarrow z).arg]
  have hnorm : x ≤ M / ‖1 - z‖ := by rw [hx, hM, div_eq_mul_inv]; exact norm_narrowBase_le hz
  have hT1 := exp_half_le_critical hx0 hδ (by linarith)
  have hT2 := sq_mul_exp_le_critical hx1 hδ hδ'
  have hmono := logSqWeight_mono hx1 hnorm
  have hsqrt : Real.sqrt x ≤ Real.sqrt M * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by
    calc Real.sqrt x ≤ Real.sqrt (M * ‖1 - z‖⁻¹) := Real.sqrt_le_sqrt (by
          rw [← div_eq_mul_inv]; exact hnorm)
      _ = Real.sqrt M * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
            Real.inv_rpow hn1.le, Real.rpow_neg hn1.le]
  have hpoly : (c : ℝ) * Real.log (1 + ‖logNarrow z‖) ≤
      2 * c * Real.sqrt M * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by
    have h1 := log_one_add_le_two_mul_sqrt (norm_nonneg (logNarrow z))
    have h2 : Real.sqrt ‖logNarrow z‖ ≤ Real.sqrt x := Real.sqrt_le_sqrt (norm_logNarrow_le hz)
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    calc (c : ℝ) * Real.log (1 + ‖logNarrow z‖) ≤ c * (2 * Real.sqrt x) := by
          gcongr; linarith
      _ ≤ c * (2 * (Real.sqrt M * ‖1 - z‖ ^ (-(1 / 2 : ℝ)))) := by gcongr
      _ = 2 * c * Real.sqrt M * ‖1 - z‖ ^ (-(1 / 2 : ℝ)) := by ring
  have hbound := (hgrowth (logNarrow z) hre).trans (by gcongr; exact le_max_left _ _ :
    A * Real.exp (π / 2 * Real.exp (π / 2 / (2 * (π / 2 - |(logNarrow z).arg|))) +
        2 * (π / 2 - |(logNarrow z).arg|) ^ 2 / (π / 2) *
          Real.exp (π / 2 / (π / 2 - |(logNarrow z).arg|))) * (1 + ‖logNarrow z‖) ^ c ≤
    max A 1 * Real.exp (π / 2 * Real.exp (π / 2 / (2 * (π / 2 - |(logNarrow z).arg|))) +
        2 * (π / 2 - |(logNarrow z).arg|) ^ 2 / (π / 2) *
          Real.exp (π / 2 / (π / 2 - |(logNarrow z).arg|))) * (1 + ‖logNarrow z‖) ^ c)
  have hlog := Real.log_le_log (norm_pos_iff.mpr h0) hbound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at hlog
  have h3 : π / 2 * Real.exp 1 * Real.sqrt x ≤
      π / 2 * Real.exp 1 * (Real.sqrt M * ‖1 - z‖ ^ (-(1 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have h4 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ π * Real.exp 2)
  nlinarith

/-- **The logarithmic Carlson theorem at the critical constant `K = π/2`.**  Let `G` be analytic
on `Re ζ > 0` with `|G(ζ)| ≤ A exp((π/2) e^{π/(4η)} + (4η²/π) e^{π/(2η)}) (1+|ζ|)^c`,
`η = π/2 − |arg ζ|`, and let `G` vanish on `N ⊆ [2, ∞)` with `Σ_{n∈N} 1/(n log n) = ∞`.  Then
`G ≡ 0`.  After the narrowing the growth is `O(1 + w(M/|1−z|) + |1−z|^{-1/2})`,
`w(x) = x/(log x + 2)²`, and its circle averages are bounded. -/
theorem eqOn_zero_of_logRoom_growth_critical {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G rightHalf)
    {A : ℝ} (c : ℕ)
    (hgrowth : ∀ ζ : ℂ, 0 < ζ.re →
      ‖G ζ‖ ≤ A * Real.exp (π / 2 * Real.exp (π / 2 / (2 * (π / 2 - |ζ.arg|))) +
        2 * (π / 2 - |ζ.arg|) ^ 2 / (π / 2) * Real.exp (π / 2 / (π / 2 - |ζ.arg|))) *
          (1 + ‖ζ‖) ^ c)
    {N : Set ℕ} (hN2 : ∀ n ∈ N, 2 ≤ n)
    (hdiv : ¬ Summable (N.indicator fun n : ℕ => 1 / ((n : ℝ) * Real.log n)))
    (hz : ∀ n ∈ N, G n = 0) : EqOn G 0 rightHalf := by
  set M : ℝ := 2 * (Real.exp 4 + 1) with hM
  have hM4 : 4 ≤ M := by rw [hM]; linarith [Real.add_one_le_exp (4 : ℝ)]
  set C₀ : ℝ := Real.log (max A 1) + π * Real.exp 2 with hC₀
  set E : ℝ := π * Real.exp 2 with hE
  have hE0 : 0 ≤ E := by positivity
  set D : ℝ := π / 2 * Real.exp 1 * Real.sqrt M + 2 * c * Real.sqrt M with hD
  have hD0 : 0 ≤ D := by positivity
  refine eqOn_zero_of_logNarrow_circleAverage_le hG
    (B := C₀ + E * (M / 2) + D * ((1 + 2 * π) / (1 - 1 / 2))) ?_ hN2 hdiv hz
  intro R hR hR1
  have hR0 : 0 < R := by linarith
  have hRabs : |R| = R := abs_of_pos hR0
  have hsph : sphere (0 : ℂ) |R| ⊆ ball 0 1 := by rw [hRabs]; exact sphere_subset_ball hR1
  have hfan : AnalyticOnNhd ℂ (fun z => G (logNarrow z)) (ball 0 1) := by
    intro z hz1
    have hz1' : ‖z‖ < 1 := by simpa using hz1
    exact AnalyticAt.comp (g := G) (f := logNarrow) (hG _ (logNarrow_mem hz1').1)
      (analyticAt_logNarrow hz1')
  have hcf : CircleIntegrable (fun z => Real.log ‖G (logNarrow z)‖) 0 R :=
    (hfan.mono hsph).meromorphicOn.circleIntegrable_log_norm
  have hnz : ∀ z ∈ sphere (0 : ℂ) R, ‖1 - z‖ ≠ 0 := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    refine norm_ne_zero_iff.mpr fun h => ?_
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz; linarith
  have hcg : CircleIntegrable (fun z : ℂ => ‖1 - z‖ ^ (-(1 / 2 : ℝ))) 0 R := by
    refine ContinuousOn.circleIntegrable hR0.le ?_
    exact ContinuousOn.rpow_const (f := fun z : ℂ => ‖1 - z‖) (by fun_prop)
      fun z hz => Or.inl (hnz z hz)
  have hcw : CircleIntegrable (fun z : ℂ => logSqRoomWeight (M / ‖1 - z‖)) 0 R := by
    refine ContinuousOn.circleIntegrable hR0.le ?_
    have hq : ContinuousOn (fun z : ℂ => M / ‖1 - z‖) (sphere 0 R) :=
      continuousOn_const.div (by fun_prop) hnz
    have hq1 : ∀ z ∈ sphere (0 : ℂ) R, 1 ≤ M / ‖1 - z‖ := by
      intro z hz
      have hp : 0 < ‖1 - z‖ := (norm_nonneg _).lt_of_ne (hnz z hz).symm
      rw [mem_sphere_zero_iff_norm] at hz
      rw [le_div_iff₀ hp]
      have : ‖1 - z‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one, hz]; linarith)
      linarith
    unfold logSqRoomWeight
    refine hq.div ((hq.log fun z hz => ?_).add continuousOn_const |>.pow 2) fun z hz => ?_
    · exact (lt_of_lt_of_le one_pos (hq1 z hz)).ne'
    · have := Real.log_nonneg (hq1 z hz); positivity
  have hsum : (fun z : ℂ => C₀ + E * logSqRoomWeight (M / ‖1 - z‖) +
      D * ‖1 - z‖ ^ (-(1 / 2 : ℝ))) = ((fun _ => C₀) +
        E • (fun z : ℂ => logSqRoomWeight (M / ‖1 - z‖))) +
          D • (fun z : ℂ => ‖1 - z‖ ^ (-(1 / 2 : ℝ))) := by
    funext z; simp [smul_eq_mul]
  have hc1 : CircleIntegrable ((fun _ => C₀) +
      E • (fun z : ℂ => logSqRoomWeight (M / ‖1 - z‖))) 0 R :=
    (circleIntegrable_const _ 0 R).add hcw.const_smul
  have hcs : CircleIntegrable (fun z : ℂ => C₀ + E * logSqRoomWeight (M / ‖1 - z‖) +
      D * ‖1 - z‖ ^ (-(1 / 2 : ℝ))) 0 R := by
    rw [hsum]; exact hc1.add hcg.const_smul
  have hmono := Real.circleAverage_mono hcf hcs fun z hz => by
    rw [hRabs, mem_sphere_zero_iff_norm] at hz
    have h := log_norm_comp_logNarrow_le_critical (A := A) c hgrowth (z := z) (by rw [hz]; exact hR1)
    rw [← hM] at h
    show _ ≤ C₀ + E * logSqRoomWeight (M / ‖1 - z‖) + D * ‖1 - z‖ ^ (-(1 / 2 : ℝ))
    rw [hC₀, hE, hD]; linarith
  have havg' : Real.circleAverage (fun z : ℂ => C₀ + E * logSqRoomWeight (M / ‖1 - z‖) +
      D * ‖1 - z‖ ^ (-(1 / 2 : ℝ))) 0 R =
      C₀ + E * Real.circleAverage (fun z : ℂ => logSqRoomWeight (M / ‖1 - z‖)) 0 R +
        D * Real.circleAverage (fun z : ℂ => ‖1 - z‖ ^ (-(1 / 2 : ℝ))) 0 R := by
    rw [hsum, Real.circleAverage_add hc1 hcg.const_smul,
      Real.circleAverage_add (circleIntegrable_const _ 0 R) hcw.const_smul,
      Real.circleAverage_const, Real.circleAverage_smul, Real.circleAverage_smul,
      smul_eq_mul, smul_eq_mul]
  rw [havg'] at hmono
  have h1 := mul_le_mul_of_nonneg_left (circleAverage_logSqWeight_le hM4 hR hR1) hE0
  have h2 := mul_le_mul_of_nonneg_left
    (circleAverage_rpow_neg_norm_one_sub_le (γ := 1 / 2) (by norm_num) (by norm_num) hR hR1) hD0
  linarith

variable {w : ℝ → ℂ}

/-- **Integer blindness at the critical room `K = π/2`.**  If
`∫ |w(t)| e^{(π/2)|t| − (π/2)|t|/log(|t|+3)} dt < ∞` and `∫ w(t) n^{-it} dt = 0` for every `n` in a
set `N ⊆ [2, ∞)` with `Σ_{n∈N} 1/(n log n) = ∞`, the Fourier transform of `w` vanishes. -/
theorem fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom_critical {N : Set ℕ}
    (hN2 : ∀ n ∈ N, 2 ≤ n)
    (hdiv : ¬ Summable (N.indicator fun n : ℕ => 1 / ((n : ℝ) * Real.log n)))
    (hwm : AEStronglyMeasurable w volume)
    (hroom : Integrable fun t => ‖w t‖ * logRoomWeight (π / 2) t)
    (hmom : ∀ n ∈ N, ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 :=
  fourier_eq_zero_of_eqOn (eqOn_zero_of_logRoom_growth_critical
    (analyticOnNhd_logFourier (dominatesSubcritical_logRoomWeight (by positivity)) hwm hroom) 0
    (fun ζ hζ => by simpa using norm_logFourier_le_logRoom_sharp (by positivity) hroom hζ) hN2 hdiv
    (fun n hn => by rw [logFourier_natCast]; exact hmom n hn)) x

theorem logRoomWeight_antitone {K K' : ℝ} (hKK' : K ≤ K') (t : ℝ) :
    logRoomWeight K' t ≤ logRoomWeight K t := by
  unfold logRoomWeight
  apply Real.exp_le_exp.mpr
  have hL : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith [abs_nonneg t])
  have : K * |t| / Real.log (|t| + 3) ≤ K' * |t| / Real.log (|t| + 3) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKK' (abs_nonneg t)) hL.le
  linarith

/-- **The exact logarithmic Carlson threshold for `log ℕ`.**  For real `K`, every `w` with
`∫ |w| e^{(π/2)|t| − K|t|/log(|t|+3)} < ∞` whose Dirichlet moments `∫ w(t) n^{-it} dt` vanish at
all integers `n ≥ 2` has vanishing Fourier transform **if and only if `K ≤ π/2`**. -/
theorem logRoom_integerBlind_iff (K : ℝ) :
    (∀ w : ℝ → ℂ, AEStronglyMeasurable w volume →
      Integrable (fun t => ‖w t‖ * logRoomWeight K t) →
      (∀ n : ℕ, 2 ≤ n → ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) →
      ∀ x : ℝ, ∫ t, w t * cexp (-(I * t) * x) = 0) ↔ K ≤ π / 2 := by
  constructor
  · intro h
    by_contra hK
    push Not at hK
    obtain ⟨w, hwc, -, hroom, hmom, x, hx⟩ := exists_integerBlind_logRoom hK
    exact hx (h w hwc.aestronglyMeasurable hroom (fun n hn => hmom n (by omega)) x)
  · intro hK w hwm hroom hmom x
    have hroom' : Integrable fun t => ‖w t‖ * logRoomWeight (π / 2) t := by
      refine hroom.mono' (hwm.norm.mul (continuous_logRoomWeight _).aestronglyMeasurable)
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (logRoomWeight_nonneg _ _))]
      exact mul_le_mul_of_nonneg_left (logRoomWeight_antitone hK t) (norm_nonneg _)
    exact fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom_critical (N := {n | 2 ≤ n})
      (fun _ hn => hn) not_summable_one_div_mul_log hwm hroom' (fun n hn => hmom n hn) x

end RHTower.PrimeBlindCarlson
