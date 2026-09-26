import GaloisForLFunctions.RHTower.ThetaCuspChargeModularCriticality
import GaloisForLFunctions.RHTower.ThetaFiniteShellNonrealZeros
import GaloisForLFunctions.RHTower.PrimeScreenAlmostPeriodicNoGo

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ### Cubic envelope for the charge source -/

theorem nine_halves_sub_pi_exp_le {x : ℝ} (hx : 0 ≤ x) :
    9 * x / 2 - π * Real.exp (2 * x) ≤ -x ^ 3 - x := by
  have he := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 2 * x) 4
  norm_num [Finset.sum_range_succ] at he
  have hpi := Real.pi_gt_three
  have hexp0 := Real.exp_pos (2 * x)
  nlinarith [sq_nonneg x, pow_nonneg hx 3]

theorem linear_sub_cube_le_rpow {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    t * x - x ^ 3 ≤ (1 + t) ^ (3 / 2 : ℝ) := by
  have hs0 := Real.sqrt_nonneg (1 + t)
  have hs2 := Real.sq_sqrt (by linarith : 0 ≤ 1 + t)
  have hpow : (1 + t) ^ (3 / 2 : ℝ) = (1 + t) * Real.sqrt (1 + t) := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by linarith : 0 < 1 + t), Real.rpow_one]
  rw [hpow]
  by_cases hxs : x ≤ Real.sqrt (1 + t)
  · nlinarith [mul_nonneg ht (sub_nonneg.mpr hxs), pow_nonneg hx 3]
  · have hsq : 1 + t ≤ x ^ 2 := by nlinarith
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hsq)]

theorem exists_charge_source_cubic :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
      ‖modSource (thetaGroupBasis 1) x‖ ≤ K * Real.exp (-|x| ^ 3 - |x|) := by
  obtain ⟨M, hM⟩ := exists_thetaGroupBasis_one_cusp
  have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis 1 τ - 0‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; rw [sub_zero]; exact hM τ hτ
  have hM0 : 0 ≤ M := by
    have h := hM Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  have hF := differentiableOn_thetaGroupBasis 1
  set X₃ : ℝ := Real.log 3 / 2 with hX₃
  have hX₃0 : 0 < X₃ := by have := Real.log_pos (by norm_num : (1:ℝ) < 3); positivity
  obtain ⟨xM, hxM, hmax⟩ := (isCompact_Icc (a := 0) (b := X₃)).exists_isMaxOn
    (nonempty_Icc.mpr hX₃0.le) (continuous_modSource hF).norm.continuousOn
  set B : ℝ := ‖modSource (thetaGroupBasis 1) xM‖
  set K : ℝ := max (B * Real.exp (X₃ ^ 3 + X₃)) (20 * M * Real.exp π)
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨K, le_max_of_le_left (by positivity), ?_⟩
  have hpos : ∀ x : ℝ, 0 ≤ x →
      ‖modSource (thetaGroupBasis 1) x‖ ≤ K * Real.exp (-x ^ 3 - x) := by
    intro x hx
    rcases le_or_gt x X₃ with hxX | hxX
    · have h1 : ‖modSource (thetaGroupBasis 1) x‖ ≤ B := hmax ⟨hx, hxX⟩
      have h2 : 1 ≤ Real.exp (X₃ ^ 3 + X₃) * Real.exp (-x ^ 3 - x) := by
        rw [← Real.exp_add]; apply Real.one_le_exp
        have : x ^ 3 ≤ X₃ ^ 3 := pow_le_pow_left₀ hx hxX 3
        linarith
      calc ‖modSource (thetaGroupBasis 1) x‖ ≤ B * (Real.exp (X₃ ^ 3 + X₃) * Real.exp (-x ^ 3 - x)) :=
            le_trans h1 (le_mul_of_one_le_right hB h2)
        _ = B * Real.exp (X₃ ^ 3 + X₃) * Real.exp (-x ^ 3 - x) := by ring
        _ ≤ K * Real.exp (-x ^ 3 - x) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · have hy : 3 ≤ Real.exp (2 * x) := by
        have : Real.exp (2 * X₃) = 3 := by
          rw [hX₃, show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]
        rw [← this]; exact Real.exp_le_exp.mpr (by linarith)
      have hub := norm_modSource_le_of_cuspDecay hF hM' hy
      set y := Real.exp (2 * x) with hydef
      have hy1 : 1 ≤ y := by linarith
      have hq : 3 * y + 2 * y ^ 2 ≤ 5 * y ^ 2 := by nlinarith
      have hy2 : Real.exp (x / 2) * y ^ 2 = Real.exp (9 * x / 2) := by
        rw [hydef, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      have hcube := nine_halves_sub_pi_exp_le hx
      calc ‖modSource (thetaGroupBasis 1) x‖
          ≤ 4 * M * Real.exp π * Real.exp (x / 2) * (3 * y + 2 * y ^ 2) * Real.exp (-π * y) := hub
        _ ≤ 4 * M * Real.exp π * Real.exp (x / 2) * (5 * y ^ 2) * Real.exp (-π * y) := by gcongr
        _ = 20 * M * Real.exp π * Real.exp (9 * x / 2 - π * y) := by
            rw [Real.exp_sub, ← hy2, show -π * y = -(π * y) by ring, Real.exp_neg]; ring
        _ ≤ 20 * M * Real.exp π * Real.exp (-x ^ 3 - x) := by
            gcongr
        _ ≤ K * Real.exp (-x ^ 3 - x) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  intro x
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact hpos x hx
  · have h := hpos (-x) (by linarith)
    rw [modSource_neg hF (thetaGroupBasis_axis 1)] at h
    rw [abs_of_nonpos hx]; exact h

/-! ### Order-`3/2` growth -/

theorem norm_thetaGroupXi_one_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖thetaGroupXi 1 z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨K, hK, henv⟩ := exists_charge_source_cubic
  refine ⟨2 * K + 2, by positivity, fun z => ?_⟩
  set Y : ℝ := |z.im|
  have hY : 0 ≤ Y := abs_nonneg _
  set E : ℝ := Real.exp ((1 + Y) ^ (3 / 2 : ℝ)) with hE
  have hmaj : Integrable (fun x : ℝ => K * E * Real.exp (-(1 * |x|))) :=
    (integrable_exp_neg_mul_abs' one_pos).const_mul _
  have hpt : ∀ x : ℝ, ‖modXiIntegrand (thetaGroupBasis 1) z x‖ ≤ K * E * Real.exp (-(1 * |x|)) := by
    intro x
    rw [norm_modXiIntegrand]
    have h1 : Real.exp (z.im * x) ≤ Real.exp (Y * |x|) :=
      Real.exp_le_exp.mpr (by
        have := abs_mul z.im x; have := le_abs_self (z.im * x); nlinarith [abs_nonneg x])
    have h2 : Y * |x| - |x| ^ 3 ≤ (1 + Y) ^ (3 / 2 : ℝ) := linear_sub_cube_le_rpow hY (abs_nonneg x)
    calc Real.exp (z.im * x) * ‖modSource (thetaGroupBasis 1) x‖
        ≤ Real.exp (Y * |x|) * (K * Real.exp (-|x| ^ 3 - |x|)) :=
          mul_le_mul h1 (henv x) (norm_nonneg _) (Real.exp_pos _).le
      _ = K * Real.exp (Y * |x| - |x| ^ 3) * Real.exp (-(1 * |x|)) := by
          rw [mul_comm, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ K * E * Real.exp (-(1 * |x|)) := by
          gcongr
          rw [hE]; exact Real.exp_le_exp.mpr h2
  have hint : ‖thetaGroupXi 1 z‖ ≤ 2 * K * E := by
    unfold thetaGroupXi modXi
    calc ‖∫ x : ℝ, modXiIntegrand (thetaGroupBasis 1) z x‖
        ≤ ∫ x : ℝ, ‖modXiIntegrand (thetaGroupBasis 1) z x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ, K * E * Real.exp (-(1 * |x|)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hmaj
            (Eventually.of_forall hpt)
      _ = 2 * K * E := by rw [integral_const_mul, integral_exp_neg_mul_abs_eq one_pos]; ring
  have hYz : 1 + Y ≤ 1 + ‖z‖ := by linarith [Complex.abs_im_le_norm z]
  have hr : (1 + Y) ^ (3 / 2 : ℝ) ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hYz (by norm_num)
  have hr1 : 1 ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
  refine le_trans hint ?_
  have h2K : 2 * K ≤ Real.exp (2 * K) := by have := Real.add_one_le_exp (2 * K); linarith
  calc 2 * K * E ≤ Real.exp (2 * K) * Real.exp ((1 + ‖z‖) ^ (3 / 2 : ℝ)) :=
        mul_le_mul h2K (Real.exp_le_exp.mpr hr) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * K + (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by rw [Real.exp_add]
    _ ≤ Real.exp ((2 * K + 2) * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
        apply Real.exp_le_exp.mpr; nlinarith

theorem norm_XiC_growth_rpow :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖XiC z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := XiC_order
  refine ⟨C * (2 * 2), by positivity, fun z => le_trans (hb z) (Real.exp_le_exp.mpr ?_)⟩
  set r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg z
  have hlog : Real.log (2 + r) ≤ (2 + r) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have h2 : (2 + r) ^ (1 / 2 : ℝ) ≤ (2 * (1 + r)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3 : (2 * (1 + r)) ^ (1 / 2 : ℝ) ≤ 2 * (1 + r) ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hsplit : (1 + r) ^ (3 / 2 : ℝ) = (1 + r) * (1 + r) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
  rw [hsplit]
  have hlog' : Real.log (2 + r) ≤ 2 * (2 * (1 + r) ^ (1 / 2 : ℝ)) := by
    have e : (2 + r) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (2 + r) ^ (1 / 2 : ℝ) := by ring
    rw [e] at hlog
    linarith
  have hC0 := hC.le
  calc C * (1 + r) * Real.log (2 + r) ≤ C * (1 + r) * (2 * (2 * (1 + r) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = C * (2 * 2) * ((1 + r) * (1 + r) ^ (1 / 2 : ℝ)) := by ring

/-! ### Two-ray decay and the zero sets on the charge line -/

theorem tendsto_thetaGroupXi_one_atTop :
    Tendsto (fun r : ℝ => ‖thetaGroupXi 1 (r : ℂ)‖) atTop (𝓝 0) := by
  set k : ℝ → ℂ := modSource (thetaGroupBasis 1) with hk
  have hRL := Real.tendsto_integral_exp_smul_cocompact k
  have hlin : Tendsto (fun r : ℝ => r / (2 * π)) atTop (cocompact ℝ) :=
    (tendsto_id.atTop_div_const (by positivity)).mono_right atTop_le_cocompact
  have h := (hRL.comp hlin).norm
  rw [norm_zero] at h
  refine h.congr (fun r => ?_)
  simp only [Function.comp]
  congr 1
  unfold thetaGroupXi modXi modXiIntegrand
  congr 1; funext v
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 1; congr 1
  push_cast; field_simp

theorem tendsto_thetaGroupXi_one_atTop_neg :
    Tendsto (fun r : ℝ => ‖thetaGroupXi 1 ((-r : ℝ) : ℂ)‖) atTop (𝓝 0) := by
  refine tendsto_thetaGroupXi_one_atTop.congr (fun r => ?_)
  rw [Complex.ofReal_neg, thetaGroupXi_one_neg]

theorem tendsto_XiC_norm_atTop : Tendsto (fun r : ℝ => ‖XiC (r : ℂ)‖) atTop (𝓝 0) := by
  have h := tendsto_XiC_ofReal_atTop.norm
  rwa [norm_zero] at h

/-- The charge line `Ξ + sΞ₁`. -/
def chargeLineXi (s : ℝ) (z : ℂ) : ℂ := XiC z + (s : ℂ) * thetaGroupXi 1 z

theorem differentiable_chargeLineXi (s : ℝ) : Differentiable ℂ (chargeLineXi s) :=
  XiC_differentiable.add ((differentiable_thetaGroupXi 1).const_mul _)

theorem chargeLineXi_neg (s : ℝ) (z : ℂ) : chargeLineXi s (-z) = chargeLineXi s z := by
  unfold chargeLineXi; rw [XiC_neg, thetaGroupXi_one_neg]

theorem chargeLineXi_eq_modXi (s : ℝ) (z : ℂ) :
    chargeLineXi s z = modXi (thetaGroupDeformation s 0) z := by
  rw [modXi_thetaGroupDeformation]; unfold chargeLineXi; simp

/-- **Away from `ξ` the charge line has only finitely many real zeros.** -/
theorem chargeLineXi_real_zeroSet_finite {s : ℝ} (hs : s ≠ 0) :
    {z : ℂ | chargeLineXi s z = 0 ∧ z.im = 0}.Finite := by
  obtain ⟨U, hU, hdom⟩ := XiC_le_eps_thetaGroupXi_one (ε := |s| / 2) (by positivity)
  have hne (b : ℝ) (hb : U ≤ b) : chargeLineXi s (b : ℂ) ≠ 0 := by
    obtain ⟨hneg, hle⟩ := hdom b hb
    have hg : 0 < ‖thetaGroupXi 1 (b : ℂ)‖ := by
      have := Complex.abs_re_le_norm (thetaGroupXi 1 (b : ℂ))
      have := abs_pos.mpr hneg.ne
      linarith
    intro h
    unfold chargeLineXi at h
    have h1 : ‖(s : ℂ) * thetaGroupXi 1 (b : ℂ)‖ = ‖XiC (b : ℂ)‖ := by
      rw [eq_neg_of_add_eq_zero_right h, norm_neg]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
    have hsabs : 0 < |s| := abs_pos.mpr hs
    nlinarith
  have hf := differentiable_chargeLineXi s
  have han := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hiso : ∀ z ∈ (univ : Set ℂ), ¬ (∀ᶠ w in 𝓝 z, chargeLineXi s w = 0) := by
    intro z _ hz
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) hz
    exact hne U le_rfl (hzero (mem_univ (U : ℂ)))
  have hfinite := GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact
    isOpen_univ hf.differentiableOn hiso
    (isCompact_closedBall (0 : ℂ) (|U| + 1)) (subset_univ _)
  apply hfinite.subset
  intro z hz
  refine ⟨?_, hz.1⟩
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hz.2
  have habs : chargeLineXi s ((|z.re| : ℝ) : ℂ) = chargeLineXi s z := by
    conv_rhs => rw [hzreal]
    rcases le_total 0 z.re with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hn, Complex.ofReal_neg, chargeLineXi_neg]
  have hr : |z.re| < U := by
    by_contra hr
    exact hne |z.re| (le_of_not_gt hr) (habs.trans hz.1)
  rw [Metric.mem_closedBall, dist_zero_right, hzreal, Complex.norm_real, Real.norm_eq_abs]
  linarith [le_abs_self U]

theorem chargeLineXi_zeroSet_infinite (s : ℝ) : {z : ℂ | chargeLineXi s z = 0}.Infinite := by
  obtain ⟨C₀, hC₀, h₀⟩ := norm_XiC_growth_rpow
  obtain ⟨C₁, hC₁, h₁⟩ := norm_thetaGroupXi_one_growth
  set C : ℝ := C₀ + C₁ + |s| + 1 with hC
  have hCnn : 0 ≤ C := by positivity
  have hgrow : ∀ z : ℂ, ‖chargeLineXi s z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
    intro z
    have hr1 : 1 ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) :=
      Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
    set R := (1 + ‖z‖) ^ (3 / 2 : ℝ)
    unfold chargeLineXi
    calc ‖XiC z + (s : ℂ) * thetaGroupXi 1 z‖ ≤ ‖XiC z‖ + |s| * ‖thetaGroupXi 1 z‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ Real.exp (C₀ * R) + Real.exp (|s|) * Real.exp (C₁ * R) := by
          have h1 : |s| ≤ Real.exp |s| := by have := Real.add_one_le_exp |s|; linarith
          gcongr
          · exact h₀ z
          · exact h₁ z
      _ ≤ Real.exp (C * R) := by
          have e1 : Real.exp (C₀ * R) ≤ Real.exp ((C₀ + C₁ + |s|) * R) :=
            Real.exp_le_exp.mpr (by nlinarith [abs_nonneg s])
          have e2 : Real.exp (|s|) * Real.exp (C₁ * R) ≤ Real.exp ((C₀ + C₁ + |s|) * R) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg s]
          have e3 : 2 * Real.exp ((C₀ + C₁ + |s|) * R) ≤ Real.exp (C * R) := by
            rw [hC, show (C₀ + C₁ + |s| + 1) * R = (C₀ + C₁ + |s|) * R + R by ring, Real.exp_add]
            have : 2 ≤ Real.exp R := by
              have := Real.add_one_le_exp R; linarith
            nlinarith [Real.exp_pos ((C₀ + C₁ + |s|) * R)]
          linarith
  have hplus : Tendsto (fun r : ℝ => ‖chargeLineXi s (r : ℂ)‖) atTop (𝓝 0) := by
    have h := tendsto_XiC_norm_atTop.add (tendsto_thetaGroupXi_one_atTop.const_mul |s|)
    rw [mul_zero, add_zero] at h
    refine squeeze_zero (fun r => norm_nonneg _) (fun r => ?_) h
    unfold chargeLineXi
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hminus : Tendsto (fun r : ℝ => ‖chargeLineXi s ((-r : ℝ) : ℂ)‖) atTop (𝓝 0) := by
    refine hplus.congr (fun r => ?_)
    rw [Complex.ofReal_neg, chargeLineXi_neg]
  exact zeroSet_infinite_of_subquadratic_twoRayDecay (differentiable_chargeLineXi s)
    (by norm_num : (0:ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2) hCnn hgrow hplus hminus

/-- **Hardy rigidity on the charge line.**  For every real `s ≠ 0` the transform of
`θ₃(1 + s·h)` has only finitely many real zeros and infinitely many nonreal zeros, while at
`s = 0` (the function `ξ`) the real zeros are infinite (Hardy). -/
theorem chargeLine_hardy_rigidity {s : ℝ} (hs : s ≠ 0) :
    {z : ℂ | modXi (thetaGroupDeformation s 0) z = 0 ∧ z.im = 0}.Finite ∧
      {z : ℂ | modXi (thetaGroupDeformation s 0) z = 0 ∧ z.im ≠ 0}.Infinite := by
  have e : ∀ z, modXi (thetaGroupDeformation s 0) z = chargeLineXi s z :=
    fun z => (chargeLineXi_eq_modXi s z).symm
  simp only [e]
  refine ⟨chargeLineXi_real_zeroSet_finite hs, fun hfin => ?_⟩
  apply chargeLineXi_zeroSet_infinite s
  apply (hfin.union (chargeLineXi_real_zeroSet_finite hs)).subset
  intro z hz
  by_cases him : z.im = 0
  · exact Or.inr ⟨hz, him⟩
  · exact Or.inl ⟨hz, him⟩

theorem XiC_real_zeroSet_infinite : {z : ℂ | XiC z = 0 ∧ z.im = 0}.Infinite := by
  intro hfin
  obtain ⟨R, hR⟩ := (hfin.image (fun z : ℂ => ‖z‖)).bddAbove
  obtain ⟨t, ht, hXt⟩ := exists_Xi_zero_gt (max R 0)
  have hmem : ((t : ℝ) : ℂ) ∈ {z : ℂ | XiC z = 0 ∧ z.im = 0} :=
    ⟨by rw [XiC_ofReal, hXt]; simp, by simp⟩
  have hle := hR ⟨_, hmem, rfl⟩
  simp only [Complex.norm_real, Real.norm_eq_abs] at hle
  have : t ≤ |t| := le_abs_self t
  have := le_max_left R 0
  linarith

end RHTower
