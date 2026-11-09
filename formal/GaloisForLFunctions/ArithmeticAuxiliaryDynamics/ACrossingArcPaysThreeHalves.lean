import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheSlowReturnBoundLivesRightOfTheLine
import GaloisForLFunctions.HTGeometry.LogQuotientDerivativeCeiling
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import GaloisForLFunctions.HTGeometry.HyperbolicLevyKhintchine
import GaloisForLFunctions.Bottcher.ZeroSet

/-!
# A reflected boundary arc pays the three-halves crossing cost

A disc crossing the critical line by depth `δ` contains the reflections
of a right-hand boundary arc of angular length proportional to `√δ`.
Jensen's inequality combines this arc with the functional equation to
force logarithmic growth proportional to `δ√δ log T`.
-/

noncomputable section

open Complex Metric Set MeasureTheory

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The reflected arc stays inside the larger crossing disc. -/
private theorem crossingArc_reflection_mem {δ T r : ℝ} (hδ : 0 < δ)
    (hrlo : 5 / 2 - 3 * δ / 4 ≤ r) (hrhi : r ≤ 5 / 2 - δ / 2)
    {w : ℂ} (hw : ‖w‖ = r) (hwre : r - δ / 8 ≤ w.re) :
    (((1 - (3 - w.re) : ℝ) : ℂ) + ((T - w.im : ℝ) : ℂ) * I) ∈
      closedBall ((3 : ℂ) + (T : ℂ) * I) (5 / 2 + δ) := by
  have hR : 0 ≤ 5 / 2 + δ := by linarith
  have hw₂ : w.re ^ 2 + w.im ^ 2 = r ^ 2 := by
    rw [← hw, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hr₂ : (5 - r) ^ 2 ≤ (5 / 2 + 3 * δ / 4) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [mem_closedBall, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num
  nlinarith only [hw₂, hr₂, hwre, sq_nonneg δ]

private theorem crossingArc_re_lower {δ r θ : ℝ} (hδ : 0 < δ)
    (hr : 0 ≤ r) (hrhi : r ≤ 5 / 2) (hθ : θ ∈ Icc 0 (Real.sqrt δ / 4)) :
    r - δ / 8 ≤ (circleMap 0 r θ).re := by
  have hθ₂ : θ ^ 2 ≤ δ / 16 := by
    have hh := pow_le_pow_left₀ hθ.1 hθ.2 2
    rw [div_pow, Real.sq_sqrt hδ.le] at hh
    norm_num at hh
    exact hh
  have hcos := _root_.HTGeometry.one_sub_cos_le_sq_div_two θ
  have hh := mul_le_mul_of_nonneg_left hcos hr
  have hh' := mul_le_mul_of_nonneg_left hθ₂ hr
  have hh'' := mul_le_mul_of_nonneg_right hrhi hδ.le
  rw [circleMap_zero_re]
  nlinarith only [hh, hh', hh'']

/-- Jensen combines an arc bound with the bound on the rest of a zero-free circle. -/
private theorem log_center_le_arc_budget {f : ℂ → ℂ} {r η L B : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (hηπ : η ≤ 2 * Real.pi)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hf₀ : f 0 ≠ 0)
    (hne : ∀ w : ℂ, ‖w‖ = r → f w ≠ 0)
    (houter : ∀ θ : ℝ, Real.log ‖f (circleMap 0 r θ)‖ ≤ L)
    (hinner : ∀ θ ∈ Icc 0 η, Real.log ‖f (circleMap 0 r θ)‖ ≤ L - B) :
    Real.log ‖f 0‖ ≤ L - η / (2 * Real.pi) * B := by
  have hfc : Continuous (fun θ : ℝ => f (circleMap 0 r θ)) :=
    hf.continuousOn.comp_continuous (continuous_circleMap _ _)
      (fun θ => circleMap_mem_closedBall _ hr.le θ)
  have hF : Continuous (fun θ : ℝ => Real.log ‖f (circleMap 0 r θ)‖) :=
    hfc.norm.log (fun θ => norm_ne_zero_iff.mpr (hne _ (by simp [abs_of_pos hr])))
  have hi₁ := hF.intervalIntegrable (μ := volume) (a := 0) (b := η)
  have hi₂ := hF.intervalIntegrable (μ := volume) (a := η) (b := 2 * Real.pi)
  have hfirst : (∫ θ in (0 : ℝ)..η, Real.log ‖f (circleMap 0 r θ)‖) ≤ η * (L - B) := by
    have hh := intervalIntegral.integral_mono_on hη hi₁
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => L - B) volume 0 η) hinner
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using hh
  have hsecond : (∫ θ in η..2 * Real.pi, Real.log ‖f (circleMap 0 r θ)‖) ≤
      (2 * Real.pi - η) * L := by
    have hh := intervalIntegral.integral_mono_on hηπ hi₂
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => L) volume η (2 * Real.pi))
      (fun θ _ => houter θ)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
  have hwhole : (∫ θ in (0 : ℝ)..2 * Real.pi, Real.log ‖f (circleMap 0 r θ)‖) ≤
      2 * Real.pi * L - η * B := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
    nlinarith only [hfirst, hsecond]
  have hj := HTGeometry.log_norm_le_circleAverage_log_norm hr hf hf₀
  rw [Real.circleAverage_def, smul_eq_mul] at hj
  have hh := mul_le_mul_of_nonneg_left hwhole (inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.pi))
  have heq : (2 * Real.pi)⁻¹ * (2 * Real.pi * L - η * B) = L - η / (2 * Real.pi) * B := by
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp [hπ]
  exact hj.trans (hh.trans_eq heq)

private theorem crossingArc_source_ne_one {δ T : ℝ} (hδ₁ : δ ≤ 1 / 8) (hT : 4 ≤ T)
    {w : ℂ} (hw : w ∈ closedBall 0 (5 / 2 + δ)) :
    (3 : ℂ) + (T : ℂ) * I - w ≠ 1 := by
  rw [mem_closedBall, dist_zero_right] at hw
  have him := (Complex.abs_im_le_norm w).trans hw
  intro h
  have hh := congrArg Complex.im h
  norm_num at hh
  linarith [(abs_le.mp him).2]

/-- The whole reflected arc, rather than one small disc, pays a three-halves depth cost. -/
private theorem exists_crossing_arc_logarithmic_cost_above_eight :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ T : ℝ, 0 < δ → δ ≤ 1 / 8 → 8 ≤ T → ∀ M : ℝ,
      (∀ z ∈ closedBall ((3 : ℂ) + (T : ℂ) * I) (5 / 2 + δ), ‖riemannZeta z‖ ≤ M) →
      δ * Real.sqrt δ / (32 * Real.pi) * Real.log T ≤ Real.log M + K := by
  obtain ⟨C, hC, hreflect⟩ := exists_norm_zeta_le_reflect
  have hCpos : 0 < C := by linarith
  refine ⟨Real.log 2 + Real.log C, add_nonneg (Real.log_nonneg (by norm_num))
    (Real.log_nonneg hC), fun δ T hδ hδ₁ hT M hM => ?_⟩
  have hR : 0 < 5 / 2 + δ := by linarith
  have hTpos : 0 < T := by linarith
  have hXpos : 0 < T / 2 := by linarith
  let f : ℂ → ℂ := fun w => riemannZeta ((3 : ℂ) + (T : ℂ) * I - w)
  have hf : AnalyticOnNhd ℂ f (closedBall 0 (5 / 2 + δ)) := by
    intro w hw
    exact (HTGeometry.analyticAt_riemannZeta (crossingArc_source_ne_one hδ₁ (by linarith) hw)).comp
      (by fun_prop)
  have hanchor : (1 / 2 : ℝ) ≤ ‖f 0‖ := by
    simpa only [f, sub_zero] using half_le_norm_zeta
      (s := (3 : ℂ) + (T : ℂ) * I) (by norm_num)
  have hf₀ : f 0 ≠ 0 := by
    intro hh
    rw [hh, norm_zero] at hanchor
    norm_num at hanchor
  have hfM : ∀ w ∈ closedBall 0 (5 / 2 + δ), ‖f w‖ ≤ M := by
    intro w hw
    apply hM
    rw [mem_closedBall, dist_zero_right] at hw
    rw [mem_closedBall, dist_eq_norm]
    rw [show ((3 : ℂ) + (T : ℂ) * I - w) - ((3 : ℂ) + (T : ℂ) * I) = -w by ring, norm_neg]
    exact hw
  have hMpos : 0 < M := by
    have hh := hanchor.trans (hfM _ (mem_closedBall_self hR.le))
    linarith
  obtain ⟨r, hr, havoid⟩ := Bottcher.exists_radius_avoiding_zeros hf
    isPreconnected_closedBall
    (mem_closedBall_self hR.le) hf₀
    (show 5 / 2 - 3 * δ / 4 < 5 / 2 - δ / 2 by linarith)
  have hrpos : 0 < r := by linarith [hr.1]
  have hrR : r ≤ 5 / 2 + δ := by linarith [hr.2]
  have hfr : AnalyticOnNhd ℂ f (closedBall 0 r) := hf.mono (closedBall_subset_closedBall hrR)
  have hne : ∀ w : ℂ, ‖w‖ = r → f w ≠ 0 := by
    intro w hw
    exact havoid w (by rw [mem_closedBall, dist_zero_right, hw]; exact hrR) hw
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsqrt₁ : Real.sqrt δ ≤ 1 := by
    have hh := Real.sq_sqrt hδ.le
    nlinarith only [hh, hδ₁, hsqrt]
  have hη : 0 ≤ Real.sqrt δ / 4 := by positivity
  have hηπ : Real.sqrt δ / 4 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hsmall : ∀ θ ∈ Icc 0 (Real.sqrt δ / 4),
      ‖f (circleMap 0 r θ)‖ ≤ C * (T / 2) ^ (-(δ / 2)) * M := by
    intro θ hθ
    let w := circleMap 0 r θ
    have hw : ‖w‖ = r := by simp [w, abs_of_pos hrpos]
    have hwre := crossingArc_re_lower hδ hrpos.le (by linarith [hr.2]) hθ
    change r - δ / 8 ≤ w.re at hwre
    have hwupper := Complex.re_le_norm w
    rw [hw] at hwupper
    have hwi := (le_abs_self w.im).trans (Complex.abs_im_le_norm w)
    rw [hw] at hwi
    have hu₀ : 1 / 2 + δ / 2 ≤ 3 - w.re := by linarith [hr.2]
    have hu₁ : 3 - w.re < 1 := by linarith [hr.1]
    have ht : T / 2 ≤ T - w.im := by linarith [hr.2]
    have ht₁ : 1 ≤ T - w.im := by linarith
    have hrefl := hreflect (3 - w.re) (T - w.im) (by linarith) hu₁ ht₁
    have hmem := crossingArc_reflection_mem (T := T) hδ hr.1.le hr.2.le hw hwre
    have hpow : (T - w.im) ^ (1 / 2 - (3 - w.re)) ≤ (T / 2) ^ (-(δ / 2)) := by
      calc (T - w.im) ^ (1 / 2 - (3 - w.re)) ≤ (T - w.im) ^ (-(δ / 2)) :=
          Real.rpow_le_rpow_of_exponent_le ht₁ (by linarith)
        _ ≤ (T / 2) ^ (-(δ / 2)) := by
          rw [Real.rpow_neg (by linarith : 0 ≤ T - w.im), Real.rpow_neg hXpos.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos hXpos _)
            (Real.rpow_le_rpow hXpos.le ht (by positivity))
    have heq : (3 : ℂ) + (T : ℂ) * I - w =
        ((3 - w.re : ℝ) : ℂ) + ((T - w.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    change ‖riemannZeta ((3 : ℂ) + (T : ℂ) * I - w)‖ ≤ _
    rw [heq]
    exact hrefl.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow hCpos.le)
      (hM _ hmem) (norm_nonneg _) (by positivity))
  have hlogouter : ∀ θ : ℝ, Real.log ‖f (circleMap 0 r θ)‖ ≤ Real.log M := by
    intro θ
    apply Real.log_le_log (norm_pos_iff.mpr (hne _ (by simp [abs_of_pos hrpos])))
    exact hfM _ (closedBall_subset_closedBall hrR (circleMap_mem_closedBall _ hrpos.le θ))
  have hloginner : ∀ θ ∈ Icc 0 (Real.sqrt δ / 4), Real.log ‖f (circleMap 0 r θ)‖ ≤
      Real.log M - (δ / 2 * Real.log (T / 2) - Real.log C) := by
    intro θ hθ
    have hh := Real.log_le_log (norm_pos_iff.mpr (hne _ (by simp [abs_of_pos hrpos])))
      (hsmall θ hθ)
    rw [Real.log_mul (mul_pos hCpos (Real.rpow_pos_of_pos hXpos _)).ne' hMpos.ne',
      Real.log_mul hCpos.ne' (Real.rpow_pos_of_pos hXpos _).ne', Real.log_rpow hXpos] at hh
    linarith
  have hj := log_center_le_arc_budget hrpos hη hηπ hfr hf₀ hne hlogouter hloginner
  have hanchlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hanchor
  rw [one_div, Real.log_inv] at hanchlog
  have hω : Real.sqrt δ / 4 / (2 * Real.pi) ≤ 1 := (div_le_one (by positivity)).2 hηπ
  have hlogC := Real.log_nonneg hC
  have hpay : δ * Real.sqrt δ / (16 * Real.pi) * Real.log (T / 2) ≤
      Real.log M + (Real.log 2 + Real.log C) := by
    have heq : Real.sqrt δ / 4 / (2 * Real.pi) * (δ / 2 * Real.log (T / 2)) =
        δ * Real.sqrt δ / (16 * Real.pi) * Real.log (T / 2) := by ring
    nlinarith only [hj, hanchlog, heq, mul_le_mul_of_nonneg_right hω hlogC]
  have hlogX : Real.log T / 2 ≤ Real.log (T / 2) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : 4 ≤ T)
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hfour] at hh
    rw [Real.log_div hTpos.ne' (by norm_num)]
    linarith
  have hh := mul_le_mul_of_nonneg_left hlogX
    (show 0 ≤ δ * Real.sqrt δ / (16 * Real.pi) by positivity)
  have heq : δ * Real.sqrt δ / (16 * Real.pi) * (Real.log T / 2) =
      δ * Real.sqrt δ / (32 * Real.pi) * Real.log T := by ring
  rw [heq] at hh
  exact hh.trans hpay

/-- A universal three-halves logarithmic cost holds down to height four. -/
theorem exists_crossing_arc_logarithmic_cost :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ T : ℝ, 0 < δ → δ ≤ 1 / 8 → 4 ≤ T → ∀ M : ℝ,
      (∀ z ∈ closedBall ((3 : ℂ) + (T : ℂ) * I) (5 / 2 + δ), ‖riemannZeta z‖ ≤ M) →
      δ * Real.sqrt δ / (32 * Real.pi) * Real.log T ≤ Real.log M + K := by
  obtain ⟨K, hK, hcost⟩ := exists_crossing_arc_logarithmic_cost_above_eight
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  refine ⟨K + Real.log 2 + Real.log 8, by positivity, fun δ T hδ hδ₁ hT M hM => ?_⟩
  by_cases hT₈ : 8 ≤ T
  · have hh := hcost δ T hδ hδ₁ hT₈ M hM
    linarith
  have hTpos : 0 < T := by linarith
  have hanchor := (half_le_norm_zeta (s := (3 : ℂ) + (T : ℂ) * I) (by norm_num)).trans
    (hM _ (mem_closedBall_self (by linarith)))
  have hanchlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hanchor
  rw [one_div, Real.log_inv] at hanchlog
  have hsqrt : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hsqrt₁ : Real.sqrt δ ≤ 1 := by nlinarith [Real.sq_sqrt hδ.le]
  have hprod : δ * Real.sqrt δ ≤ 1 := by
    nlinarith only [mul_le_mul_of_nonneg_left hsqrt₁ hδ.le, hδ₁]
  have hcoeff : δ * Real.sqrt δ / (32 * Real.pi) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith [Real.pi_gt_three]
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hl := Real.log_le_log hTpos (show T ≤ 8 by linarith)
  have hh := mul_le_mul_of_nonneg_right hcoeff hlogT
  nlinarith only [hl, hh, hanchlog, hK]

/-- Crossing depth `δ` forces a positive multiple of `T^(δ√δ/(32π))`. -/
theorem exists_crossing_arc_rpow_cost :
    ∃ c : ℝ, 0 < c ∧ ∀ δ T : ℝ, 0 < δ → δ ≤ 1 / 8 → 4 ≤ T → ∀ M : ℝ,
      (∀ z ∈ closedBall ((3 : ℂ) + (T : ℂ) * I) (5 / 2 + δ), ‖riemannZeta z‖ ≤ M) →
      c * T ^ (δ * Real.sqrt δ / (32 * Real.pi)) ≤ M := by
  obtain ⟨K, _, hK⟩ := exists_crossing_arc_logarithmic_cost
  refine ⟨Real.exp (-K), Real.exp_pos _, fun δ T hδ hδ₁ hT M hM => ?_⟩
  have hTpos : 0 < T := by linarith
  have hMpos : 0 < M := by
    have hh := (half_le_norm_zeta (s := (3 : ℂ) + (T : ℂ) * I) (by norm_num)).trans
      (hM _ (mem_closedBall_self (by linarith)))
    linarith
  have hlog := hK δ T hδ hδ₁ hT M hM
  have hh := Real.exp_le_exp.mpr
    (show -K + Real.log T * (δ * Real.sqrt δ / (32 * Real.pi)) ≤ Real.log M by nlinarith only [hlog])
  rwa [Real.exp_add, Real.exp_log hMpos, ← Real.rpow_def_of_pos hTpos] at hh

/-- The three-halves crossing cost is realized by an actual value of `ζ`. -/
theorem exists_large_zeta_value_on_crossing_arc_disc :
    ∃ c : ℝ, 0 < c ∧ ∀ δ T : ℝ, 0 < δ → δ ≤ 1 / 8 → 4 ≤ T →
      ∃ z ∈ closedBall ((3 : ℂ) + (T : ℂ) * I) (5 / 2 + δ),
        c * T ^ (δ * Real.sqrt δ / (32 * Real.pi)) ≤ ‖riemannZeta z‖ := by
  obtain ⟨c, hc, hcost⟩ := exists_crossing_arc_rpow_cost
  refine ⟨c, hc, fun δ T hδ hδ₁ hT => ?_⟩
  have hnonempty : (closedBall ((3 : ℂ) + (T : ℂ) * I) (5 / 2 + δ)).Nonempty :=
    ⟨_, mem_closedBall_self (by linarith)⟩
  have hcont : ContinuousOn (fun z : ℂ => ‖riemannZeta z‖)
      (closedBall ((3 : ℂ) + (T : ℂ) * I) (5 / 2 + δ)) := by
    intro z hz
    have hw : (3 : ℂ) + (T : ℂ) * I - z ∈ closedBall 0 (5 / 2 + δ) := by
      simpa only [mem_closedBall, dist_eq_norm, sub_zero, norm_sub_rev] using hz
    have hne := crossingArc_source_ne_one hδ₁ hT hw
    rw [show (3 : ℂ) + (T : ℂ) * I - ((3 : ℂ) + (T : ℂ) * I - z) = z by ring] at hne
    exact (differentiableAt_riemannZeta hne).continuousAt.norm.continuousWithinAt
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall ((3 : ℂ) + (T : ℂ) * I)
    (5 / 2 + δ)).exists_isMaxOn hnonempty hcont
  exact ⟨z, hz, hcost δ T hδ hδ₁ hT _ (fun w hw => hmax hw)⟩

/-- An aligned return budgets penetration to the three-halves power. -/
theorem exists_aligned_crossing_threeHalves_budget :
    ∃ K H : ℝ, 0 ≤ K ∧ 4 ≤ H ∧ ∀ T : ℝ, H ≤ T → ∀ N : ℕ, 1 ≤ N →
      IsHeadReturn N T → ∀ A δ γ : ℝ, 0 ≤ A → 0 < δ → δ ≤ 1 / 8 → 0 ≤ γ →
      (∀ z ∈ closedBall ((3 : ℂ) + (γ : ℂ) * I) (5 / 2 + δ),
        ‖riemannZeta (z + (T : ℂ) * I)‖ ≤ (N : ℝ) ^ A) →
      δ * Real.sqrt δ * Real.log (γ + T) ≤
        32 * Real.pi * (A * (Real.log 1024 + 6 * Real.log (Real.log T)) + K) := by
  obtain ⟨K, hK, hcost⟩ := exists_crossing_arc_logarithmic_cost
  obtain ⟨H, _, hlength⟩ := length_le_pow_log_of_isHeadReturn
  refine ⟨K, max 4 H, hK, le_max_left _ _, fun T hT N hN hhead A δ γ hA hδ hδ₁ hγ hM => ?_⟩
  have hT₄ : 4 ≤ T := (le_max_left _ _).trans hT
  have hTH : H ≤ T := (le_max_right _ _).trans hT
  obtain ⟨hlog, hlen⟩ := hlength T hTH N hhead
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hlogpos : 0 < Real.log T := by linarith
  have hlogN := Real.log_le_log hNpos hlen
  rw [Real.log_mul (by norm_num) (pow_pos hlogpos _).ne', Real.log_pow] at hlogN
  have hMactual : ∀ z ∈ closedBall ((3 : ℂ) + ((γ + T : ℝ) : ℂ) * I) (5 / 2 + δ),
      ‖riemannZeta z‖ ≤ (N : ℝ) ^ A := by
    intro z hz
    have hmem : z - (T : ℂ) * I ∈ closedBall ((3 : ℂ) + (γ : ℂ) * I) (5 / 2 + δ) := by
      rw [mem_closedBall, dist_eq_norm] at hz ⊢
      have heq : z - (T : ℂ) * I - ((3 : ℂ) + (γ : ℂ) * I) =
          z - ((3 : ℂ) + ((γ + T : ℝ) : ℂ) * I) := by push_cast; ring
      rwa [heq]
    simpa only [sub_add_cancel] using hM _ hmem
  have hbound := hcost δ (γ + T) hδ hδ₁ (by linarith) _ hMactual
  rw [Real.log_rpow hNpos] at hbound
  have hh := mul_le_mul_of_nonneg_left hlogN hA
  norm_num at hh
  have hbudget : δ * Real.sqrt δ / (32 * Real.pi) * Real.log (γ + T) ≤
      A * (Real.log 1024 + 6 * Real.log (Real.log T)) + K := by linarith only [hbound, hh]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 32 * Real.pi)] at hbudget
  nlinarith only [hbudget]

#print axioms exists_crossing_arc_logarithmic_cost
#print axioms exists_large_zeta_value_on_crossing_arc_disc
#print axioms exists_aligned_crossing_threeHalves_budget

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
