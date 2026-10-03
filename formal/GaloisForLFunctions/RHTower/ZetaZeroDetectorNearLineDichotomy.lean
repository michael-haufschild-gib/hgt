import GaloisForLFunctions.RHTower.ZetaZeroDetectorParametricDichotomy

/-!
# The detector dichotomy for zeros near the critical line

The line-integral bound and the Type I / Type II dichotomy of
`ZetaZeroExponentialDetectorBounds` and `ZetaZeroDetectorParametricDichotomy` require
`β ≥ 7/12`, so that the detector line `Re w = 1/2 - β` stays at distance `≥ 1/12` from the pole
of `Γ` at `0`.  For `β ≥ 1/2 + η` the same proofs run with `|Γ(w)| ≤ (1/η) C e^{-|Im w|}` on
`Re w ≤ -η` (`norm_Gamma_neg_line_le_of_gap`), giving the dichotomy for every `σ₁ > 1/2`
(`exists_pDetector_dichotomy_of_gap`), with constants depending on `σ₁`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

theorem norm_Gamma_neg_line_le_of_gap {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x t : ℝ, 1 / 2 ≤ x → x ≤ 1 →
      ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.exp (-|t|))
    {η : ℝ} (hη : 0 < η) {c : ℝ} (hc1 : -1 / 2 ≤ c) (hc2 : c ≤ -η) (y : ℝ) :
    ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ ≤ 1 / η * C * Real.exp (-|y|) := by
  set w : ℂ := (c : ℂ) + (y : ℂ) * I with hw
  have hwre : w.re = c := by simp [hw]
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hwre] at this
    simp at this
    linarith
  have hnorm : η ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    rw [hwre, abs_of_neg (by linarith)] at h
    linarith
  have hrel : Complex.Gamma w = Complex.Gamma (w + 1) / w := by
    rw [Complex.Gamma_add_one w hw0]
    field_simp
  have hw1 : w + 1 = ((c + 1 : ℝ) : ℂ) + (y : ℂ) * I := by
    rw [hw]; push_cast; ring
  have hb := hC (c + 1) y (by linarith) (by linarith)
  rw [← hw1] at hb
  rw [hrel, norm_div, div_le_iff₀ (by linarith)]
  calc ‖Complex.Gamma (w + 1)‖ ≤ C * Real.exp (-|y|) := hb
    _ = 1 / η * C * Real.exp (-|y|) * η := by field_simp
    _ ≤ 1 / η * C * Real.exp (-|y|) * ‖w‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)

theorem exists_norm_integral_expDetIntegrand_le_of_gap {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ∃ (A B : ℝ) (N : ℕ), 0 ≤ A ∧ 0 ≤ B ∧ ∀ (X : ℕ) (ρ : ℂ) (Y L : ℝ), 1 / 2 + η ≤ ρ.re →
      ρ.re ≤ 1 → 1 ≤ Y → 0 ≤ L →
      ‖∫ y : ℝ, expDetIntegrand X ρ Y (((1 / 2 - ρ.re : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        Y ^ (1 / 2 - ρ.re) * (A + X * A *
          (∫ y in (-L)..L, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ.im + y : ℝ) : ℂ) * I)‖) +
          X * B * (1 + |ρ.im|) ^ N * Real.exp (-(L / 2))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_Gamma_le_exp_neg_abs
  obtain ⟨Cζ, N, hCζ, hζ⟩ := exists_norm_riemannZeta_half_le
  set E₁ : ℝ := ∫ y : ℝ, Real.exp (-(1 * |y|)) with hE₁
  set I₁ : ℝ := ∫ y : ℝ, Real.exp (-(|y| / 2)) * (1 + |y|) ^ N with hI₁
  have hE₁0 : 0 ≤ E₁ := integral_nonneg fun y => (Real.exp_pos _).le
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun y => by positivity
  refine ⟨(1 / η * C) * (E₁ + 1), (1 / η * C) * (Cζ * I₁), N, by positivity, by positivity, ?_⟩
  intro X ρ Y L hβ1 hβ2 hY hL
  set c : ℝ := 1 / 2 - ρ.re with hc
  set γ : ℝ := ρ.im with hγ
  have hY0 : 0 < Y := by linarith
  set g : ℝ → ℝ := fun y => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I)‖ with hg
  have hgcont : Continuous g := continuous_norm_riemannZeta_half_shift γ
  -- the pointwise bound
  have hpt : ∀ y : ℝ, ‖expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I)‖ ≤
      Y ^ c * ((1 / η * C) * (Real.exp (-(1 * |y|)) + X * (Real.exp (-(1 * |y|)) * g y))) := by
    intro y
    have hs : ρ + ((c : ℂ) + (y : ℂ) * I) = ((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hc, hγ]
    have hYw : ‖(Y : ℂ) ^ ((c : ℂ) + (y : ℂ) * I)‖ = Y ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY0]
      simp
    have hΓ := norm_Gamma_neg_line_le_of_gap hC0 hC hη (c := c) (by rw [hc]; linarith)
      (by rw [hc]; linarith) y
    have hM : ‖Sieve.inghamMollifier X (ρ + ((c : ℂ) + (y : ℂ) * I))‖ ≤ X :=
      Sieve.norm_inghamMollifier_le_nat X (by rw [hs]; norm_num)
    have hfac : ‖1 - Sieve.inghamMollifier X (ρ + ((c : ℂ) + (y : ℂ) * I)) *
        riemannZeta (ρ + ((c : ℂ) + (y : ℂ) * I))‖ ≤ 1 + X * g y := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_one, norm_mul]
      have hgy : ‖riemannZeta (ρ + ((c : ℂ) + (y : ℂ) * I))‖ = g y := by rw [hs]
      rw [hgy]
      gcongr
    unfold expDetIntegrand
    rw [norm_mul, norm_mul, hYw, one_mul]
    have hg0 : 0 ≤ g y := norm_nonneg _
    calc Y ^ c * ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ *
          ‖1 - Sieve.inghamMollifier X (ρ + ((c : ℂ) + (y : ℂ) * I)) *
            riemannZeta (ρ + ((c : ℂ) + (y : ℂ) * I))‖
        ≤ Y ^ c * ((1 / η * C) * Real.exp (-|y|)) * (1 + X * g y) := by
          gcongr
      _ = Y ^ c * ((1 / η * C) * (Real.exp (-|y|) + X * (Real.exp (-|y|) * g y))) := by ring
  -- integrability
  have hexp1 : Integrable (fun y : ℝ => Real.exp (-(1 * |y|))) :=
    integrable_exp_neg_mul_abs' one_pos
  have hgbound : ∀ y : ℝ, g y ≤ Cζ * (1 + |γ|) ^ N * (1 + |y|) ^ N := by
    intro y
    have h1 := hζ (γ + y)
    have h2 : (1 + |γ + y|) ^ N ≤ ((1 + |γ|) * (1 + |y|)) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [abs_add_le γ y, abs_nonneg γ, abs_nonneg y]
    calc g y ≤ Cζ * (1 + |γ + y|) ^ N := h1
      _ ≤ Cζ * ((1 + |γ|) * (1 + |y|)) ^ N := mul_le_mul_of_nonneg_left h2 hCζ
      _ = Cζ * (1 + |γ|) ^ N * (1 + |y|) ^ N := by rw [mul_pow]; ring
  have hIhalf := integrable_exp_neg_half_abs_mul_one_add_abs_pow N
  have hexpg : Integrable (fun y : ℝ => Real.exp (-(1 * |y|)) * g y) := by
    refine Integrable.mono' (hIhalf.const_mul (Cζ * (1 + |γ|) ^ N))
      ((by fun_prop : Continuous fun y : ℝ => Real.exp (-(1 * |y|))).mul
        hgcont).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have hg0 : 0 ≤ g y := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.exp (-(1 * |y|)) ≤ Real.exp (-(|y| / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg y])
    calc Real.exp (-(1 * |y|)) * g y
        ≤ Real.exp (-(|y| / 2)) * (Cζ * (1 + |γ|) ^ N * (1 + |y|) ^ N) :=
          mul_le_mul h1 (hgbound y) hg0 (Real.exp_pos _).le
      _ = Cζ * (1 + |γ|) ^ N * (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N) := by ring
  -- the integral of the majorant
  have hmaj_int : Integrable (fun y : ℝ =>
      Y ^ c * ((1 / η * C) * (Real.exp (-(1 * |y|)) + X * (Real.exp (-(1 * |y|)) * g y)))) :=
    ((hexp1.add (hexpg.const_mul (X : ℝ))).const_mul ((1 / η * C))).const_mul (Y ^ c)
  have hint : Integrable (fun y : ℝ => expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I)) :=
    integrable_expDetIntegrand_line X ρ (by linarith) hβ2 hY (x := c) (by rw [hc]; linarith)
      (by rw [hc]; linarith)
      (fun m hm => by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, Nat.cast_zero, neg_zero] at hm
          rw [hc] at hm
          linarith
        · have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
          rw [hc] at hm
          linarith) (by rw [hc]; linarith)
  have hstep1 := norm_integral_le_integral_norm (μ := volume)
    (fun y : ℝ => expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I))
  have hstep2 := integral_mono hint.norm hmaj_int hpt
  rw [integral_const_mul, integral_const_mul, integral_add hexp1 (hexpg.const_mul _),
    integral_const_mul] at hstep2
  -- the split of `∫ e^{-|y|} g`
  have hsplit := integral_add_compl (measurableSet_Icc (a := -L) (b := L)) hexpg
  have hIcc : ∫ y in Icc (-L) L, Real.exp (-(1 * |y|)) * g y ≤ ∫ y in (-L)..L, g y := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_mono_on hexpg.integrableOn
      (hgcont.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc ?_
    intro y _
    have hg0 : 0 ≤ g y := norm_nonneg _
    have h1 : Real.exp (-(1 * |y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg y])
    nlinarith
  have hcompl : ∫ y in (Icc (-L) L)ᶜ, Real.exp (-(1 * |y|)) * g y ≤
      Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁ := by
    have hmaj2 : Integrable (fun y : ℝ =>
        Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N)) :=
      hIhalf.const_mul _
    calc ∫ y in (Icc (-L) L)ᶜ, Real.exp (-(1 * |y|)) * g y
        ≤ ∫ y in (Icc (-L) L)ᶜ,
            Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N) := by
          refine setIntegral_mono_on hexpg.integrableOn hmaj2.integrableOn
            measurableSet_Icc.compl ?_
          intro y hy
          have hyL : L < |y| := by
            simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hy
            rcases hy with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; exact h
          have hg0 : 0 ≤ g y := norm_nonneg _
          have h1 : Real.exp (-(1 * |y|)) ≤ Real.exp (-(L / 2)) * Real.exp (-(|y| / 2)) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith)
          calc Real.exp (-(1 * |y|)) * g y
              ≤ (Real.exp (-(L / 2)) * Real.exp (-(|y| / 2))) *
                  (Cζ * (1 + |γ|) ^ N * (1 + |y|) ^ N) :=
                mul_le_mul h1 (hgbound y) hg0 (by positivity)
            _ = Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) *
                  (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N) := by ring
      _ ≤ ∫ y : ℝ,
            Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * (Real.exp (-(|y| / 2)) * (1 + |y|) ^ N) :=
          setIntegral_le_integral hmaj2 (Eventually.of_forall fun y => by positivity)
      _ = Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁ := by rw [integral_const_mul]
  have hEg : ∫ y : ℝ, Real.exp (-(1 * |y|)) * g y ≤
      (∫ y in (-L)..L, g y) + Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁ := by
    rw [← hsplit]
    exact add_le_add hIcc hcompl
  have hYc : 0 ≤ Y ^ c := Real.rpow_nonneg hY0.le _
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hint_g : 0 ≤ ∫ y in (-L)..L, g y :=
    intervalIntegral.integral_nonneg (by linarith) fun y _ => norm_nonneg _
  refine le_trans hstep1 (le_trans hstep2 ?_)
  apply mul_le_mul_of_nonneg_left _ hYc
  have hfinal : (1 / η * C) * (E₁ + X * ∫ y : ℝ, Real.exp (-(1 * |y|)) * g y) ≤
      (1 / η * C) * (E₁ + 1) + X * ((1 / η * C) * (E₁ + 1)) * (∫ y in (-L)..L, g y) +
        X * ((1 / η * C) * (Cζ * I₁)) * (1 + |γ|) ^ N * Real.exp (-(L / 2)) := by
    have h12 : 0 ≤ (1 / η * C) := by positivity
    have hXE : X * ∫ y : ℝ, Real.exp (-(1 * |y|)) * g y ≤
        X * ((∫ y in (-L)..L, g y) + Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁) :=
      mul_le_mul_of_nonneg_left hEg hX0
    have hA : (1 / η * C) * (E₁ + X * ∫ y : ℝ, Real.exp (-(1 * |y|)) * g y) ≤
        (1 / η * C) * (E₁ + X * ((∫ y in (-L)..L, g y) +
          Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁)) :=
      mul_le_mul_of_nonneg_left (by linarith) h12
    refine le_trans hA ?_
    have hgE : 0 ≤ X * ((1 / η * C)) * (∫ y in (-L)..L, g y) := by positivity
    have : (1 / η * C) * (E₁ + X * ((∫ y in (-L)..L, g y) +
          Cζ * (1 + |γ|) ^ N * Real.exp (-(L / 2)) * I₁)) =
        (1 / η * C) * E₁ + X * ((1 / η * C) * E₁) * 0 + X * ((1 / η * C)) * (∫ y in (-L)..L, g y) +
          X * ((1 / η * C) * (Cζ * I₁)) * (1 + |γ|) ^ N * Real.exp (-(L / 2)) := by ring
    rw [this]
    have hXEg : 0 ≤ X * ((1 / η * C) * E₁) * (∫ y in (-L)..L, g y) := by positivity
    nlinarith
  exact hfinal

/-- **The Type I / Type II dichotomy for general lengths, any `σ₁ > 1/2`.** -/
theorem exists_pDetector_dichotomy_of_gap {δ y σ₁ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hy0 : 0 < y)
    (hy1 : y ≤ 1) (hσ₁ : 1 / 2 < σ₁) :
    ∃ (K₀ c₀ T₀ : ℝ), 0 < c₀ ∧ 0 ≤ K₀ ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ ρ : ℂ,
      riemannZeta ρ = 0 → σ₁ ≤ ρ.re → ρ.re < 1 → T ≤ ρ.im → ρ.im ≤ 2 * T →
      1 / 8 ≤ ‖∑ n ∈ Finset.range (pDetCut y T + 1),
          expDetTerm (pDetMoll δ T) ρ (pDetSmooth y T) n‖ ∨
      c₀ * pDetSmooth y T ^ (ρ.re - 1 / 2) / pDetMoll δ T ≤
        ∫ t in (-(K₀ * Real.log T))..(K₀ * Real.log T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ.im + t : ℝ) : ℂ) * I)‖ := by
  obtain ⟨A, B, N, hA, hB, hJ⟩ := exists_norm_integral_expDetIntegrand_le_of_gap
    (η := min (σ₁ - 1 / 2) (1 / 2)) (lt_min (by linarith) (by norm_num)) (min_le_right _ _)
  obtain ⟨Cr, Nr, hCr, hr⟩ := exists_norm_expDetZetaResidue_le
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 2 * ((N : ℝ) + 2) := ⟨_, rfl⟩
  set e : ℝ := y * (σ₁ - 1 / 2) with he
  have he0 : 0 < e := by rw [he]; exact mul_pos hy0 (by linarith)
  have ev1 : ∀ᶠ T : ℝ in atTop, 6 ≤ Real.log T := Real.tendsto_log_atTop.eventually_ge_atTop 6
  have ev2 : ∀ᶠ T : ℝ in atTop,
      Cr * 2 ^ Nr * T ^ (Nr + 2) * Real.exp (-(Real.pi * T / 2)) ≤ 1 / 8 :=
    (tendsto_const_mul_pow_mul_exp_neg_pi (Cr * 2 ^ Nr) (Nr + 2)).eventually
      (ge_mem_nhds (by norm_num))
  have ev3 := eventually_const_mul_rpow_neg_le_one A he0
  have ev4 := eventually_const_mul_rpow_neg_le_one (B * 3 ^ N) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (ev1.and (ev2.and (ev3.and (ev4.and (eventually_ge_atTop (1 : ℝ))))))
  refine ⟨K₀, 1 / (A + 1), T₀, by positivity, by rw [hK₀]; positivity,
    (hT₀ T₀ le_rfl).2.2.2.2, fun T hT ρ hρ hβ1 hβ2 hγ1 hγ2 => ?_⟩
  obtain ⟨hlog, hres_small, hA_small, hB_small, hT1⟩ := hT₀ T hT
  have hT0 : 0 < T := by linarith
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ, X = pDetMoll δ T := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = pDetSmooth y T := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = K₀ * Real.log T := ⟨_, rfl⟩
  rw [← hXdef, ← hYdef, ← hLdef]
  have hX1 : 1 ≤ X := hXdef ▸ one_le_pDetMoll hδ0.le hT1
  have hXle : (X : ℝ) ≤ T ^ δ := hXdef ▸ pDetMoll_le hT1
  have hY1 : 1 ≤ Y := hYdef ▸ one_le_pDetSmooth hy0.le hT1
  have hY0 : 0 < Y := by linarith
  have hYT : Y = T ^ y := hYdef
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hL0 : 0 ≤ L := by rw [hLdef, hK₀]; positivity
  set γ := ρ.im with hγ
  have hγ0 : 0 < γ := by linarith
  set c : ℝ := 1 / 2 - ρ.re with hc
  have hid := tsum_moebiusZetaDefect_exp_eq X hX1 hρ (by linarith) hβ2 hY1 (c := c)
    (by rw [hc]; linarith) (by rw [hc]; linarith)
  have htail := (summable_expDetTerm_and_tail_le hX1 (by linarith) hY0 (pDetCut y T)).2
  have htail' : ‖(∑' n, expDetTerm X ρ Y n) -
      ∑ n ∈ Finset.range (pDetCut y T + 1), expDetTerm X ρ Y n‖ ≤ 1 / 8 := by
    refine le_trans htail ?_
    rw [hYdef]
    exact pDet_tail_small hy0.le hy1 hT1 hlog
  have hXT : (X : ℝ) ≤ T := le_trans hXle (by
    calc T ^ δ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hδ1
      _ = T := Real.rpow_one T)
  have hYT' : Y ≤ T := by
    rw [hYT]
    calc T ^ y ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hy1
      _ = T := Real.rpow_one T
  have hres : ‖expDetZetaResidue X ρ Y‖ ≤ 1 / 8 := by
    have h := hr X ρ Y (by linarith) hβ2 (by rw [← hγ, abs_of_pos hγ0]; linarith) hY1
    rw [← hγ, abs_of_pos hγ0] at h
    refine le_trans h (le_trans ?_ hres_small)
    have hγpow : γ ^ Nr ≤ (2 * T) ^ Nr := pow_le_pow_left₀ hγ0.le hγ2 Nr
    have hexp : Real.exp (-(Real.pi * γ / 2)) ≤ Real.exp (-(Real.pi * T / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    calc (X : ℝ) * Y * (Cr * γ ^ Nr * Real.exp (-(Real.pi * γ / 2)))
        ≤ T * T * (Cr * (2 * T) ^ Nr * Real.exp (-(Real.pi * T / 2))) := by
          gcongr
      _ = Cr * 2 ^ Nr * T ^ (Nr + 2) * Real.exp (-(Real.pi * T / 2)) := by ring
  have hJb := hJ X ρ Y L (by linarith [min_le_left (σ₁ - 1 / 2) (1 / 2)]) hβ2.le hY1 hL0
  rw [← hc] at hJb
  set Ig : ℝ := ∫ t in (-L)..L, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((γ + t : ℝ) : ℂ) * I)‖
    with hIg
  have hIg0 : 0 ≤ Ig := intervalIntegral.integral_nonneg (by linarith) fun t _ => norm_nonneg _
  have hYc : Y ^ c ≤ T ^ (-e) := by
    rw [hYT, ← Real.rpow_mul hT0.le]
    apply Real.rpow_le_rpow_of_exponent_le hT1
    rw [he, hc]
    nlinarith
  have hYc0 : 0 ≤ Y ^ c := Real.rpow_nonneg hY0.le _
  have hJA : Y ^ c * A ≤ 1 := by
    calc Y ^ c * A ≤ T ^ (-e) * A := mul_le_mul_of_nonneg_right hYc hA
      _ = A * T ^ (-e) := by ring
      _ ≤ 1 := hA_small
  have hYc1 : Y ^ c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY1 (by rw [hc]; linarith)
  have hJB : Y ^ c * (X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2))) ≤ 1 := by
    have hexpL : Real.exp (-(L / 2)) = T ^ (-((N : ℝ) + 2)) := by
      rw [Real.rpow_def_of_pos hT0, hLdef, hK₀]
      congr 1
      ring
    have hγ3 : (1 + |γ|) ^ N ≤ (3 * T) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      rw [abs_of_pos hγ0]
      linarith
    have hpow : T * (3 * T) ^ N * T ^ (-((N : ℝ) + 2)) = 3 ^ N * T ^ (-(1 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast T N]
      have e' : T * (3 ^ N * T ^ (N : ℝ)) * T ^ (-((N : ℝ) + 2)) =
          3 ^ N * (T ^ (1 : ℝ) * T ^ (N : ℝ) * T ^ (-((N : ℝ) + 2))) := by
        rw [Real.rpow_one]; ring
      rw [e', ← Real.rpow_add hT0, ← Real.rpow_add hT0]
      congr 2
      ring
    calc Y ^ c * (X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2)))
        ≤ 1 * (T * B * (3 * T) ^ N * T ^ (-((N : ℝ) + 2))) := by
          rw [hexpL]
          gcongr
      _ = B * 3 ^ N * T ^ (-(1 : ℝ)) := by
          rw [one_mul]
          calc T * B * (3 * T) ^ N * T ^ (-((N : ℝ) + 2))
              = B * (T * (3 * T) ^ N * T ^ (-((N : ℝ) + 2))) := by ring
            _ = B * (3 ^ N * T ^ (-(1 : ℝ))) := by rw [hpow]
            _ = B * 3 ^ N * T ^ (-(1 : ℝ)) := by ring
      _ ≤ 1 := hB_small
  -- the dichotomy
  by_cases hP : 1 / 8 ≤ ‖∑ n ∈ Finset.range (pDetCut y T + 1), expDetTerm X ρ Y n‖
  · exact Or.inl hP
  right
  push Not at hP
  obtain ⟨J, hJdef⟩ : ∃ J : ℂ,
      J = ∫ y : ℝ, expDetIntegrand X ρ Y ((c : ℂ) + (y : ℂ) * I) := ⟨_, rfl⟩
  rw [← hJdef] at hid hJb
  obtain ⟨P, hPdef⟩ : ∃ P : ℂ,
      P = ∑ n ∈ Finset.range (pDetCut y T + 1), expDetTerm X ρ Y n := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℂ, S = ∑' n, expDetTerm X ρ Y n := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ, R = expDetZetaResidue X ρ Y := ⟨_, rfl⟩
  rw [← hPdef] at hP htail'
  rw [← hSdef] at htail'
  rw [← hRdef] at hres
  have hS : S = 1 + R + ((1 / (2 * Real.pi) : ℝ) : ℂ) * J := by
    rw [hSdef, hRdef]
    simpa only [expDetTerm] using hid
  have hone : (1 : ℂ) = P + (S - P) - R - ((1 / (2 * Real.pi) : ℝ) : ℂ) * J := by
    rw [hS]; ring
  have hkey : ‖P + (S - P) - R - ((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ ≤
      ‖P‖ + ‖S - P‖ + ‖R‖ + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ := by
    calc ‖P + (S - P) - R - ((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖
        ≤ ‖P + (S - P) - R‖ + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ := norm_sub_le _ _
      _ ≤ (‖P + (S - P)‖ + ‖R‖) + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ((‖P‖ + ‖S - P‖) + ‖R‖) + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ := by
          gcongr; exact norm_add_le _ _
  have hJn : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * J‖ = (1 / (2 * Real.pi)) * ‖J‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hnorm1 : (1 : ℝ) ≤ ‖P‖ + 1 / 8 + 1 / 8 + (1 / (2 * Real.pi)) * ‖J‖ := by
    have h := congrArg norm hone
    rw [norm_one] at h
    refine le_trans h.le (le_trans hkey ?_)
    rw [hJn]
    linarith only [htail', hres]
  have hJbig : 3 ≤ ‖J‖ := by
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have h1 : 5 / 8 ≤ (1 / (2 * Real.pi)) * ‖J‖ := by linarith only [hnorm1, hP]
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h1
    linarith only [h1, Real.pi_gt_three]
  -- extract the critical-line integral
  have hmain : 1 ≤ Y ^ c * (X * A * Ig) := by
    have h := le_trans hJbig hJb
    have e : Y ^ c * (A + X * A * Ig + X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2))) =
        Y ^ c * A + Y ^ c * (X * A * Ig) +
          Y ^ c * (X * B * (1 + |γ|) ^ N * Real.exp (-(L / 2))) := by ring
    rw [e] at h
    linarith only [h, hJA, hJB]
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hYneg : Y ^ (ρ.re - 1 / 2) * Y ^ c = 1 := by
    rw [← Real.rpow_add hY0, hc]
    simp
  rw [div_le_iff₀ hX0]
  have hYpos : 0 < Y ^ (ρ.re - 1 / 2) := Real.rpow_pos_of_pos hY0 _
  calc 1 / (A + 1) * Y ^ (ρ.re - 1 / 2) = 1 / (A + 1) * Y ^ (ρ.re - 1 / 2) * 1 := by ring
    _ ≤ 1 / (A + 1) * Y ^ (ρ.re - 1 / 2) * (Y ^ c * (X * (A + 1) * Ig)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : Y ^ c * (X * A * Ig) ≤ Y ^ c * (X * (A + 1) * Ig) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith only) hX0.le) hIg0) hYc0
        exact le_trans hmain this
    _ = (Y ^ (ρ.re - 1 / 2) * Y ^ c) * (Ig * X) := by field_simp
    _ = Ig * X := by rw [hYneg, one_mul]

end RHTower

end
