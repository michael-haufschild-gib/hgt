import GaloisForLFunctions.RHTower.WeilZetaSquareBoundaryInequality
import GaloisForLFunctions.RHTower.WeilFiniteSupportRigidity

/-!
# Real twisted second moments of `ζ` on the notch window

Let `ω_L = blockWindow L (2L) (L/2)` (equal to `1` on `[L, 2L]`, supported in `[L/2, 5L/2]`) and
`Z(t) = |ζ(½+it)|²` (`zsq`). The real twisted moment `M_L(ξ) = ∫ ω_L Z cos(ξt)` (`momentRe`) is the
real part of the corpus `twistedMoment`.

* **Main term with an explicit error** (`exists_abs_momentRe_sub_le`). For coprime `h, k ≥ 1` and
  `L ≥ 16`, `|M_L(log h − log k) − (hk)^{−1/2} W(L)| ≤ C hk L`, where `W(L) = Re ∫ ω_L log t`
  (the window scale `δ = 1/(4√L)` in `exists_norm_twistedMoment_hk_sub_le`).
* **Window size** (`re_logWindow_le`): `W(L) ≤ 2L log(5L/2)`; with `re_logWindow_ge`,
  `L log L ≤ W(L)`.
* **Mean square on the window and on its support** (`exists_momentRe_zero_le`,
  `exists_intervalIntegral_zsq_le`): `∫ ω_L Z ≤ C L log L` and `∫_{L/2}^{5L/2} Z ≤ C L log L`,
  the latter by covering `[L/2, 5L/2]` with the cores of the windows at `L/2`, `L` and `5L/4`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilZetaSquare

open RHTower.ZetaNotch

/-- The real notch window `ω_L`. -/
abbrev win (L : ℝ) : ℝ → ℝ := blockWindow L (2 * L) (L / 2)

/-- `Z(t) = |ζ(½+it)|²`. -/
def zsq (t : ℝ) : ℝ := Complex.normSq (riemannZeta (linePt t))

theorem zsq_nonneg (t : ℝ) : 0 ≤ zsq t := Complex.normSq_nonneg _

theorem continuous_zeta_line : Continuous fun t : ℝ => riemannZeta (linePt t) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_zeta_line t).continuousAt

theorem continuous_zsq : Continuous zsq := Complex.continuous_normSq.comp continuous_zeta_line

theorem zetaSq_eq_zsq (t : ℝ) : zetaSq t = (zsq t : ℂ) := by
  rw [zetaSq_eq_normSq, zsq, Complex.normSq_eq_norm_sq]

theorem notchWindow_eq_win (L t : ℝ) : notchWindow L t = (win L t : ℂ) := rfl

theorem win_eq_zero {L t : ℝ} (hL : 0 < L) (ht : t ∉ Icc (L / 2) (5 * L / 2)) : win L t = 0 := by
  have h := notchWindow_eq_zero hL ht
  rw [notchWindow_eq_win] at h
  exact_mod_cast h

/-- The real twisted moment `∫ ω_L Z cos(ξt)`. -/
def momentRe (L ξ : ℝ) : ℝ := ∫ t, win L t * zsq t * Real.cos (ξ * t)

theorem integrable_win_mul {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun t => win L t * g t) := by
  have hc : Continuous fun t => win L t * g t :=
    (contDiff_blockWindow L (2 * L) (L / 2)).continuous.mul hg
  exact (hc.continuousOn.integrableOn_compact (isCompact_Icc (a := L / 2) (b := 5 * L / 2))).integrable_of_forall_notMem_eq_zero
    fun t ht => by rw [win_eq_zero hL ht, zero_mul]

theorem re_twistedMoment {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    (ZetaNotch.twistedMoment L ξ).re = momentRe L ξ := by
  unfold ZetaNotch.twistedMoment momentRe
  have hint : Integrable (fun t => notchWindow L t * zetaSq t * Complex.exp (-(ξ * t) * I)) := by
    have h := integrable_notchWindow_mul_of_continuousOn hL
      (f := fun t => zetaSq t * Complex.exp (-(ξ * t) * I))
      (by
        have : Continuous fun t : ℝ => zetaSq t * Complex.exp (-(ξ * t) * I) := by
          have hz : Continuous zetaSq := by
            have : zetaSq = fun t => (zsq t : ℂ) := funext zetaSq_eq_zsq
            rw [this]; exact Complex.continuous_ofReal.comp continuous_zsq
          fun_prop
        exact this.continuousOn)
    simpa only [mul_assoc] using h
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [notchWindow_eq_win, zetaSq_eq_zsq, ← Complex.ofReal_mul,
    show -((ξ : ℂ) * (t : ℂ)) * I = ((-(ξ * t) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-! ## The main term -/

theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hx (by linarith [Real.add_one_le_exp x])

/-- **Main term of a coprime twist with an explicit error**:
`|M_L(log h − log k) − (hk)^{−1/2} W(L)| ≤ C hk L`. -/
theorem exists_abs_momentRe_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ {h k : ℕ}, 0 < h → 0 < k → Nat.Coprime h k →
      |momentRe L (Real.log h - Real.log k) -
          (Real.sqrt ((h : ℝ) * k))⁻¹ * (logWindow L).re| ≤ C * ((h : ℝ) * k) * L := by
  obtain ⟨C, hC, hmain⟩ := exists_norm_twistedMoment_hk_sub_le 6
  refine ⟨26 * C + 4, by positivity, fun {L} hL {h k} hh hk hcop => ?_⟩
  have hL0 : 0 < L := by linarith
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsL1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  set δ : ℝ := 1 / (4 * Real.sqrt L) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hE := hmain hL hδ0 hδ4 hh hk hcop
  set N : ℝ := (h : ℝ) * k with hN
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hN1 : 1 ≤ N := by rw [hN]; nlinarith
  have hkN : (k : ℝ) ≤ N := by rw [hN]; nlinarith
  -- the real part
  have hre : momentRe L (Real.log h - Real.log k) - (Real.sqrt N)⁻¹ * (logWindow L).re =
      (ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
        (((Real.sqrt N)⁻¹ : ℝ) : ℂ) * logWindow L).re := by
    rw [Complex.sub_re, Complex.re_ofReal_mul, re_twistedMoment hL0]
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hE.trans ?_)
  unfold hkEnvelope
  rw [← hN]
  -- the four pieces
  have hw : (Real.sqrt N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1)
  have hw0 : 0 ≤ (Real.sqrt N)⁻¹ := by positivity
  have hlogN : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hT1 : (Real.sqrt N)⁻¹ * (2 * L * (C + 2 * Real.log N)) ≤ 2 * (C + 2) * N * L := by
    have h1 : (Real.sqrt N)⁻¹ * (2 * L * (C + 2 * Real.log N)) ≤ 2 * L * (C + 2 * Real.log N) := by
      have : 0 ≤ 2 * L * (C + 2 * Real.log N) := by positivity
      nlinarith
    have h2 : C ≤ C * N := le_mul_of_one_le_right hC hN1
    nlinarith
  have hT2 : 24 * δ * k * L * Real.sqrt L ≤ 6 * N * L := by
    have e : 24 * δ * k * L * Real.sqrt L = 6 * k * L := by
      rw [hδ]; field_simp; norm_num
    rw [e]; nlinarith
  have hT3 : L ^ 2 / (L * δ) ^ 6 ≤ 16 * N * L := by
    have e : L * δ = Real.sqrt L / 4 := by
      rw [hδ]; field_simp; nlinarith [hss]
    have hs6 : (Real.sqrt L) ^ 6 = L ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hL0.le]
    rw [e, div_pow, hs6]
    have hL3 : 0 < L ^ 3 := by positivity
    rw [div_div_eq_mul_div, div_le_iff₀ hL3]
    nlinarith [pow_pos hL0 3, pow_pos hL0 4]
  have hT4 : L ^ 2 * Real.exp (-(L ^ 2) / 32) ≤ 2 * N * L := by
    have hx : 0 < L ^ 2 / 32 := by positivity
    have he := exp_neg_le_inv hx
    rw [neg_div]
    calc L ^ 2 * Real.exp (-(L ^ 2 / 32)) ≤ L ^ 2 * (1 / (L ^ 2 / 32)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = 32 := by field_simp
      _ ≤ 2 * N * L := by nlinarith
  have hsum : 24 * δ * k * L * Real.sqrt L + L ^ 2 / (L * δ) ^ 6 +
      L ^ 2 * Real.exp (-(L ^ 2) / 32) ≤ 24 * N * L := by linarith
  calc (Real.sqrt N)⁻¹ * (2 * L * (C + 2 * Real.log N)) +
        C * (24 * δ * k * L * Real.sqrt L + L ^ 2 / (L * δ) ^ 6 +
          L ^ 2 * Real.exp (-(L ^ 2) / 32))
      ≤ 2 * (C + 2) * N * L + C * (24 * N * L) :=
        add_le_add hT1 (mul_le_mul_of_nonneg_left hsum hC)
    _ = (26 * C + 4) * N * L := by ring

/-! ## Window size and mean squares -/

/-- `W(L) = Re ∫ ω_L log t ≤ 2L log(5L/2)`. -/
theorem re_logWindow_le {L : ℝ} (hL : 2 ≤ L) : (logWindow L).re ≤ 2 * L * Real.log (5 * L / 2) := by
  have hL0 : 0 < L := by linarith
  have hη : (0 : ℝ) < L / 2 := by linarith
  have hint : Integrable (fun t => notchWindow L t * (Real.log t : ℂ)) :=
    integrable_notchWindow_mul_of_continuousOn hL0
      ((Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]
        linarith [ht.1])))
  have hre : (logWindow L).re = ∫ t, win L t * Real.log t := by
    unfold logWindow
    have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [notchWindow, blockWindowC]
  rw [hre]
  have hpt : ∀ t, win L t * Real.log t ≤
      (Icc (L / 2) (5 * L / 2)).indicator (fun _ => Real.log (5 * L / 2)) t := by
    intro t
    by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
    · rw [indicator_of_mem ht]
      have hlogt : Real.log t ≤ Real.log (5 * L / 2) := Real.log_le_log (by linarith [ht.1]) ht.2
      have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
      calc win L t * Real.log t ≤ 1 * Real.log t :=
            mul_le_mul_of_nonneg_right (blockWindow_le_one _ _ _ _) hlogt0
        _ ≤ Real.log (5 * L / 2) := by rw [one_mul]; exact hlogt
    · rw [indicator_of_notMem ht, win_eq_zero hL0 ht, zero_mul]
  have hi2 : Integrable (fun t => win L t * Real.log t) := by
    have := hint.re
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp [notchWindow, blockWindowC]
  calc ∫ t, win L t * Real.log t ≤
        ∫ t, (Icc (L / 2) (5 * L / 2)).indicator (fun _ => Real.log (5 * L / 2)) t :=
        integral_mono hi2 ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc) hpt
    _ = 2 * L * Real.log (5 * L / 2) := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const,
          Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring

/-- `∫ ω_L Z ≤ C L log L` for `L ≥ 16`. -/
theorem exists_momentRe_zero_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 16 ≤ L →
    momentRe L 0 ≤ C * L * Real.log L := by
  obtain ⟨C, hC, hmain⟩ := exists_abs_momentRe_sub_le
  refine ⟨C + 6, by positivity, fun {L} hL => ?_⟩
  have h := hmain hL (h := 1) (k := 1) one_pos one_pos (Nat.coprime_one_left 1)
  simp only [Nat.cast_one, Real.log_one, sub_self, mul_one, Real.sqrt_one, inv_one,
    one_mul] at h
  have hlog := re_logWindow_le (L := L) (by linarith)
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlog52 : Real.log (5 * L / 2) ≤ 2 * Real.log L := by
    have h1 : Real.log (5 * L / 2) = Real.log (5 / 2) + Real.log L := by
      rw [show 5 * L / 2 = (5 / 2) * L by ring, Real.log_mul (by norm_num) hL0.ne']
    have h2 : Real.log (5 / 2) ≤ 1 := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (by norm_num) (by linarith [Real.exp_one_gt_d9])
    linarith
  have hab := (abs_le.mp h).2
  have h2 : (logWindow L).re ≤ 4 * L * Real.log L := by
    have := mul_le_mul_of_nonneg_left hlog52 (by positivity : (0 : ℝ) ≤ 2 * L)
    linarith
  have h3 : C * L ≤ C * L * Real.log L := le_mul_of_one_le_right (by positivity) hlogL
  have h4 : 4 * L * Real.log L ≤ 6 * L * Real.log L := by
    have : 0 ≤ L * Real.log L := by positivity
    linarith
  calc momentRe L 0 ≤ (logWindow L).re + C * L := by linarith
    _ ≤ (C + 6) * L * Real.log L := by linarith

/-- `∫_{L/2}^{5L/2} Z ≤ C L log L` for `L ≥ 32`. -/
theorem exists_intervalIntegral_zsq_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 32 ≤ L →
    ∫ t in (L / 2)..(5 * L / 2), zsq t ≤ C * L * Real.log L := by
  obtain ⟨C, hC, hmom⟩ := exists_momentRe_zero_le
  refine ⟨4 * C, by positivity, fun {L} hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have hmom' : ∀ {L' : ℝ}, 16 ≤ L' → ∫ t, win L' t * zsq t ≤ C * L' * Real.log L' := by
    intro L' hL'
    have h := hmom hL'
    unfold momentRe at h
    simpa using h
  have hcover : ∀ t ∈ Icc (L / 2) (5 * L / 2),
      zsq t ≤ win (L / 2) t * zsq t + win L t * zsq t + win (5 * L / 4) t * zsq t := by
    intro t ht
    have hz := zsq_nonneg t
    have hn1 := blockWindow_nonneg (L / 2) (2 * (L / 2)) (L / 2 / 2) t
    have hn2 := blockWindow_nonneg L (2 * L) (L / 2) t
    have hn3 := blockWindow_nonneg (5 * L / 4) (2 * (5 * L / 4)) (5 * L / 4 / 2) t
    have hsum : 1 ≤ win (L / 2) t + win L t + win (5 * L / 4) t := by
      rcases le_total t L with h1 | h1
      · have : win (L / 2) t = 1 :=
          blockWindow_eq_one (by positivity) ht.1 (by linarith)
        linarith
      rcases le_total t (2 * L) with h2 | h2
      · have : win L t = 1 := blockWindow_eq_one (by positivity) h1 h2
        linarith
      · have : win (5 * L / 4) t = 1 :=
          blockWindow_eq_one (by positivity) (by linarith) (by linarith [ht.2])
        linarith
    nlinarith
  have hint : ∀ L' : ℝ, 0 < L' → Integrable (fun t => win L' t * zsq t) :=
    fun L' hL' => integrable_win_mul hL' continuous_zsq
  have hII : ∀ L' : ℝ, 0 < L' →
      ∫ t in (L / 2)..(5 * L / 2), win L' t * zsq t ≤ ∫ t, win L' t * zsq t := by
    intro L' hL'
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral (hint L' hL') (Eventually.of_forall fun t =>
      mul_nonneg (blockWindow_nonneg _ _ _ _) (zsq_nonneg t))
  have hcont : ∀ L' : ℝ, Continuous fun t => win L' t * zsq t := fun L' =>
    (contDiff_blockWindow L' (2 * L') (L' / 2)).continuous.mul continuous_zsq
  have hA : IntervalIntegrable (fun t => win (L / 2) t * zsq t + win L t * zsq t) volume
      (L / 2) (5 * L / 2) := ((hcont (L / 2)).add (hcont L)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t => win (5 * L / 4) t * zsq t) volume (L / 2) (5 * L / 2) :=
    (hcont (5 * L / 4)).intervalIntegrable _ _
  have hA1 : IntervalIntegrable (fun t => win (L / 2) t * zsq t) volume (L / 2) (5 * L / 2) :=
    (hcont (L / 2)).intervalIntegrable _ _
  have hA2 : IntervalIntegrable (fun t => win L t * zsq t) volume (L / 2) (5 * L / 2) :=
    (hcont L).intervalIntegrable _ _
  have hsum3 : ∫ t in (L / 2)..(5 * L / 2),
      (win (L / 2) t * zsq t + win L t * zsq t + win (5 * L / 4) t * zsq t) =
      (∫ t in (L / 2)..(5 * L / 2), win (L / 2) t * zsq t) +
        (∫ t in (L / 2)..(5 * L / 2), win L t * zsq t) +
        (∫ t in (L / 2)..(5 * L / 2), win (5 * L / 4) t * zsq t) := by
    rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_add hA1 hA2]
  have h1 := (hII (L / 2) (by positivity)).trans (hmom' (by linarith))
  have h2 := (hII L hL0).trans (hmom' (by linarith))
  have h3 := (hII (5 * L / 4) (by positivity)).trans (hmom' (by linarith))
  have hlogL1 : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hl1 : Real.log (L / 2) ≤ Real.log L := Real.log_le_log (by positivity) (by linarith)
  have hl3 : Real.log (5 * L / 4) ≤ 2 * Real.log L := by
    have e : Real.log (5 * L / 4) = Real.log (5 / 4) + Real.log L := by
      rw [show 5 * L / 4 = (5 / 4) * L by ring, Real.log_mul (by norm_num) hL0.ne']
    have h54 : Real.log (5 / 4) ≤ 1 := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (by norm_num) (by linarith [Real.exp_one_gt_d9])
    linarith
  have k1 : C * (L / 2) * Real.log (L / 2) ≤ C * (L / 2) * Real.log L :=
    mul_le_mul_of_nonneg_left hl1 (by positivity)
  have k3 : C * (5 * L / 4) * Real.log (5 * L / 4) ≤ C * (5 * L / 4) * (2 * Real.log L) :=
    mul_le_mul_of_nonneg_left hl3 (by positivity)
  calc ∫ t in (L / 2)..(5 * L / 2), zsq t
      ≤ ∫ t in (L / 2)..(5 * L / 2),
          (win (L / 2) t * zsq t + win L t * zsq t + win (5 * L / 4) t * zsq t) :=
        intervalIntegral.integral_mono_on (by linarith) (continuous_zsq.intervalIntegrable _ _)
          (hA.add hB) hcover
    _ ≤ 4 * C * L * Real.log L := by
        rw [hsum3]
        nlinarith

end RHTower.WeilZetaSquare
