import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.RHTower.GammaVerticalPhaseSecondOrder
import GaloisForLFunctions.RHTower.XiHorizontalBound
import GaloisForLFunctions.RHTower.XiVerticalPhaseTwo

/-!
# Explicit bounds for the ξ quarter contour

Jensen's real-trace disc gives a horizontal bound `100 log T`. A compact digamma
estimate and its vertical remainder give error `10T` from the vertical main term.
These numerical bounds make the symmetric zero-count threshold effective.
-/

open Complex Filter Topology intervalIntegral MeasureTheory Set Metric
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

private lemma abs_re_digamma_one_le_five {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |(Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re| ≤ 5 := by
  let w : ℂ := 1 + (t : ℂ) * I
  let z : ℂ := w + 1
  have hwre : w.re = 1 := by simp [w]
  have hzre : z.re = 2 := by norm_num [z, w]
  have hn2 : 2 ≤ ‖z‖ := by simpa only [hzre] using Complex.re_le_norm z
  have hnsq : ‖z‖ ^ 2 = 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z, w]
    ring
  have hn3 : ‖z‖ ≤ 3 := by nlinarith [norm_nonneg z]
  have hnpos : 0 < ‖z‖ := by linarith
  have hlog0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (by linarith)
  have hlog2 : Real.log ‖z‖ ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos hnpos
    linarith
  have hrem := norm_digamma_sub_log_le_of_re_pos (z := z) (by rw [hzre]; norm_num) hn2
  have hremRe := (Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)).trans hrem
  rw [Complex.sub_re, Complex.log_re] at hremRe
  have hfrac : 3 / ‖z‖ ≤ (3 / 2 : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn2
  have hpsi : |(Complex.digamma z).re| ≤ 7 / 2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hremRe.trans hfrac)
    rw [abs_le]
    constructor <;> linarith
  have hpole : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    simp only [hwre, Complex.neg_re, Complex.natCast_re] at hr
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hshift : (Complex.digamma z).re = (Complex.digamma w).re + (1 / w : ℂ).re := by
    simpa only [Complex.add_re, one_div] using congrArg Complex.re
      (Complex.digamma_apply_add_one w hpole)
  have hinv : (1 / w : ℂ).re = 1 / (1 + t ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp [w, pow_two]
  have hinv0 : 0 ≤ (1 / w : ℂ).re := by rw [hinv]; positivity
  have hinv1 : (1 / w : ℂ).re ≤ 1 := by
    rw [hinv, div_le_one (by positivity)]
    nlinarith [sq_nonneg t]
  obtain ⟨hl, hu⟩ := abs_le.mp hpsi
  change |(Complex.digamma w).re| ≤ 5
  rw [abs_le]
  constructor <;> linarith

private lemma abs_gammaVerticalPhase_one_two_le : |gammaVerticalPhase 1 2| ≤ 10 := by
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 2,
      ‖(Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re‖ ≤ 5 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    rw [Real.norm_eq_abs]
    exact abs_re_digamma_one_le_five ht.1.le ht.2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  norm_num [Real.norm_eq_abs] at h
  simpa only [gammaVerticalPhase, Complex.ofReal_one] using h

/-- A numerical Stirling-phase error on the vertical line through one. -/
theorem abs_gammaVerticalPhase_one_sub_main_le_six_mul {t : ℝ} (ht : 2 ≤ t) :
    |gammaVerticalPhase 1 t - (t * Real.log t - t)| ≤ 6 * t := by
  have ht0 : 0 < t := by linarith
  let e : ℝ → ℝ := fun u =>
    (Complex.digamma ((1 : ℂ) + (u : ℂ) * I)).re - Real.log u
  have hecont : ContinuousOn e (Set.uIcc 2 t) := by
    refine (continuous_digammaVerticalRe (by norm_num : (0 : ℝ) < 1)).continuousOn.sub ?_
    refine Real.continuousOn_log.mono fun u hu => ?_
    rw [Set.uIcc_of_le ht, Set.mem_Icc] at hu
    exact Set.mem_compl_singleton_iff.mpr (by linarith [hu.1])
  have hint : (∫ u in (2 : ℝ)..t, e u) =
      gammaVerticalPhaseRemainder 1 t - gammaVerticalPhaseRemainder 1 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [Set.uIcc_of_le ht, Set.mem_Icc] at hu
      simpa only [e, Complex.ofReal_one] using
        hasDerivAt_gammaVerticalPhaseRemainder (σ := 1) (by norm_num) (by linarith [hu.1])
    · exact hecont.intervalIntegrable
  have hb : ∀ u ∈ Set.uIoc (2 : ℝ) t, ‖e u‖ ≤ 2 := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    rw [Real.norm_eq_abs]
    have he : |e u| ≤ 8 / u ^ 2 := abs_re_digamma_one_sub_log_le hu.1.le
    refine he.trans ?_
    have hu0 : 0 < u := by linarith [hu.1]
    rw [div_le_iff₀ (sq_pos_of_pos hu0)]
    nlinarith [hu.1]
  have hdiff := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, hint, abs_of_nonneg (by linarith : 0 ≤ t - 2)] at hdiff
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hbase : |gammaVerticalPhaseRemainder 1 2| ≤ 12 := by
    rw [gammaVerticalPhaseRemainder]
    refine (abs_sub _ _).trans ?_
    have hmain : |(2 : ℝ) * Real.log 2 - 2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    linarith [abs_gammaVerticalPhase_one_two_le]
  have htri := abs_add_le (gammaVerticalPhaseRemainder 1 t - gammaVerticalPhaseRemainder 1 2)
    (gammaVerticalPhaseRemainder 1 2)
  rw [sub_add_cancel] at htri
  change |gammaVerticalPhaseRemainder 1 t| ≤ 6 * t
  linarith

/-- The vertical ξ argument differs from `T log T / 2` by at most `10T`. -/
theorem abs_vertical_xi_sub_half_mul_log_le {T : ℝ} (hT : 4 ≤ T) :
    |(∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re)
      - (1 / 2) * (T * Real.log T)| ≤ 10 * T := by
  have hT0 : 0 < T := by linarith
  have hγ := abs_gammaVerticalPhase_one_sub_main_le_six_mul (t := T / 2) (by linarith)
  have hrat := abs_integral_rational_head_le T
  have hζ := abs_integral_re_logDeriv_zeta_two_le T
  have hlog2 : 0 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
    constructor
    · exact Real.log_nonneg (by norm_num)
    · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
  have hlogπ : 0 ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ 3 := by
    constructor
    · exact Real.log_nonneg (by linarith [Real.pi_gt_three])
    · have h := Real.log_le_sub_one_of_pos Real.pi_pos
      linarith [Real.pi_lt_d2]
  have hsplit :
      (∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re)
          - (1 / 2) * (T * Real.log T)
        = (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)))
          + (gammaVerticalPhase 1 (T / 2) - (T / 2 * Real.log (T / 2) - T / 2))
          + (∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re)
          - T / 2 * (Real.log 2 + Real.log Real.pi + 1) := by
    rw [integral_re_logDeriv_xi_two, Real.log_div hT0.ne' (by norm_num)]
    ring
  have hlin : |T / 2 * (Real.log 2 + Real.log Real.pi + 1)| ≤ 5 * T / 2 := by
    rw [abs_of_nonneg (mul_nonneg (by positivity) (by linarith [hlog2.1, hlogπ.1]))]
    nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hlog2.2),
      mul_nonneg hT0.le (sub_nonneg.mpr hlogπ.2)]
  rw [hsplit]
  calc
    _ ≤ |(∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2)))
          + (gammaVerticalPhase 1 (T / 2) - (T / 2 * Real.log (T / 2) - T / 2))
          + (∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re)|
          + |T / 2 * (Real.log 2 + Real.log Real.pi + 1)| := abs_sub _ _
    _ ≤ (|∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2))|
          + |gammaVerticalPhase 1 (T / 2) - (T / 2 * Real.log (T / 2) - T / 2)|
          + |∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re|)
          + |T / 2 * (Real.log 2 + Real.log Real.pi + 1)| := by
      gcongr
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 10 * T := by linarith [Real.pi_lt_d2]

/-- Jensen's disc contains at most `28 log T` real-trace zeros, counted with multiplicity. -/
theorem zetaRealTrace_divisor_le_twentyEight_log {T : ℝ} (hT : 4 ≤ T) :
    ((∑ᶠ u, MeromorphicOn.divisor (zetaRealTrace T)
      (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) u : ℤ) : ℝ) ≤ 28 * Real.log T := by
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hn : (1 / 4 : ℝ) ≤ ‖zetaRealTrace T 2‖ := by
    have hp := Real.pi_lt_d2
    have hp0 := Real.pi_pos
    have hβ := norm_zetaRealTrace_two_ge T
    nlinarith
  have hn0 : 0 < ‖zetaRealTrace T 2‖ := by linarith
  let M : ℝ := 2 + 8 * (T + 7 / 4)
  have hM0 : 0 < M := by dsimp only [M]; linarith
  have hM : M ≤ 12 * T := by dsimp only [M]; linarith
  have hratio : M / ‖zetaRealTrace T 2‖ ≤ 48 * T := by
    have hstep : M / ‖zetaRealTrace T 2‖ ≤ 4 * M := by
      rw [div_le_iff₀ hn0]
      nlinarith [mul_le_mul_of_nonneg_left hn hM0.le]
    linarith
  have hcube : (64 : ℝ) ≤ T ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hT 3
    norm_num at h
    exact h
  have hpower : 48 * T ≤ T ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hcube hT0.le]
  have hlog : Real.log (M / ‖zetaRealTrace T 2‖) ≤ 4 * Real.log T := by
    have h := Real.log_le_log (div_pos hM0 hn0) (hratio.trans hpower)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hden : (1 / 7 : ℝ) ≤ Real.log (7 / 6) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (7 / 6 : ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hden0 : 0 < Real.log (7 / 6) := by linarith
  refine (zetaRealTrace_divisor_le hT).trans ?_
  rw [show (7 / 4 / (3 / 2) : ℝ) = 7 / 6 by norm_num, div_le_iff₀ hden0]
  change Real.log (M / ‖zetaRealTrace T 2‖) ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hden hlogT]

/-- The horizontal argument increment of ζ has the explicit Backlund bound. -/
theorem abs_horizontal_zeta_le {T : ℝ} (hT : 4 ≤ T)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    |∫ u in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((u : ℂ) + (T : ℂ) * I)).im|
      ≤ 29 * Real.pi * Real.log T := by
  classical
  have hT0 : (0 : ℝ) < T := by linarith
  have hT2 : (2 : ℝ) < T := by linarith
  have hTne : T ≠ 0 := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hζne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 :=
    zeta_horizontal_ne_zero hTne hne
  set Z : Finset ℝ := (zetaRealTrace_real_zeros_finite hT2).toFinset with hZdef
  have hZmem : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 2,
      (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0 → x ∈ Z := by
    intro x hx hzero
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), Complex.dist_eq]
      have hx1 : (1 : ℝ) / 2 < x := hx.1
      have hx2 : x < 2 := hx.2
      have hval : ‖((x : ℂ) - 2)‖ = |x - 2| := by
        rw [show ((x : ℂ) - 2) = ((x - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hval, abs_le]
      constructor <;> linarith
    · rw [zetaRealTrace_ofReal, hzero]
      norm_num
  have hbound := abs_integral_im_logDeriv_zeta_le hTne hζne hZmem
  have hcard : ((Z.filter (fun z => z ∈ Set.Ioo (1 / 2 : ℝ) 2)).card : ℝ) ≤ 28 * Real.log T := by
    have hsub : (Z.filter (fun z => z ∈ Set.Ioo (1 / 2 : ℝ) 2)).card ≤ Z.card :=
      Finset.card_filter_le _ _
    have himg : (Z.image (fun x : ℝ => (x : ℂ))).card = Z.card :=
      Finset.card_image_of_injective _ (fun a b h => Complex.ofReal_inj.mp h)
    have hKcompact : IsCompact (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) := isCompact_closedBall ..
    have hKana : AnalyticOnNhd ℂ (zetaRealTrace T) (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) :=
      (analyticOnNhd_zetaRealTrace hT2).mono (by
        intro w hw
        rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hw
        rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)]
        linarith)
    have hKord : ∀ z ∈ closedBall (2 : ℂ) |(3 / 2 : ℝ)|,
        analyticOrderAt (zetaRealTrace T) z ≠ ⊤ := by
      intro z hz
      refine zetaRealTrace_order_ne_top hT2 ?_
      rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hz
      rw [mem_ball]
      linarith
    have hS : ∀ z ∈ Z.image (fun x : ℝ => (x : ℂ)),
        z ∈ closedBall (2 : ℂ) |(3 / 2 : ℝ)| ∧ zetaRealTrace T z = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rw [hZdef, Set.Finite.mem_toFinset] at hx
      exact hx
    have hle := card_le_divisor_sum hKcompact hKana hKord _ hS
    rw [himg] at hle
    have hcnt := zetaRealTrace_divisor_le_twentyEight_log hT
    have hcast : ((Z.card : ℤ) : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor (zetaRealTrace T)
        (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) u : ℤ) : ℝ) := by exact_mod_cast hle
    have hsubcast : ((Z.filter (fun z => z ∈ Set.Ioo (1 / 2 : ℝ) 2)).card : ℝ) ≤ (Z.card : ℝ) := by
      exact_mod_cast hsub
    push_cast at hcast
    linarith
  refine le_trans hbound ?_
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hcard, hlog1, hπ]

/-- The horizontal ξ argument is bounded by `100 log T` above height four. -/
theorem abs_horizontal_xi_le_hundred_log {T : ℝ} (hT : 4 ≤ T)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    |∫ x in (1 / 2 : ℝ)..2, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im|
      ≤ 100 * Real.log T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hTne : T ≠ 0 := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hζne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 :=
    zeta_horizontal_ne_zero hTne hne
  have hcxi : Continuous fun x : ℝ => (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im :=
    Complex.continuous_im.comp (continuous_logDeriv_xi_horizontal hne)
  have hcζ : Continuous fun x : ℝ => (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im :=
    Complex.continuous_im.comp (continuous_logDeriv_zeta_horizontal hTne hζne)
  have hsplit : (∫ x in (1 / 2 : ℝ)..2, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im)
      = (∫ x in (1 / 2 : ℝ)..2, ((logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im
          - (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im))
        + ∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im := by
    rw [intervalIntegral.integral_sub (hcxi.intervalIntegrable _ _)
      (hcζ.intervalIntegrable _ _)]
    ring
  have hhead : |∫ x in (1 / 2 : ℝ)..2, ((logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im
      - (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im)| ≤ 3 * (1 + Real.pi / 2) := by
    have hbnd : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) 2,
        ‖(logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im
          - (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im‖ ≤ 1 + Real.pi / 2 := by
      intro x hx
      rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
      rw [Real.norm_eq_abs]
      exact abs_im_logDeriv_xi_horizontal_le hT ⟨hx.1.le, hx.2⟩ (hζne x)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rw [Real.norm_eq_abs] at h
    have harith : (1 + Real.pi / 2) * |2 - 1 / 2| ≤ 3 * (1 + Real.pi / 2) := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 - 1 / 2)]
      nlinarith [Real.pi_pos]
    linarith [h, harith]
  have htail := abs_horizontal_zeta_le hT hne
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hC : 29 * Real.pi + 3 * (1 + Real.pi / 2) ≤ 100 := by
    linarith [Real.pi_lt_d2]
  have hhead' : 3 * (1 + Real.pi / 2) ≤ 3 * (1 + Real.pi / 2) * Real.log T := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ 3 * (1 + Real.pi / 2)) (sub_nonneg.mpr hlog1)]
  nlinarith [mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ Real.log T)]

#print axioms abs_vertical_xi_sub_half_mul_log_le
#print axioms abs_horizontal_xi_le_hundred_log

end RHTower
