import GaloisForLFunctions.RHTower.HardyTwoSeventhCensus

/-!
# The square-root critical-line census

**Theorem** (`exists_many_distinct_line_zeros_dyadic_sqrt`). There are `c > 0` and `T₁` such that
for every `T ≥ T₁` at least `c·√T/(1 + log T)²` distinct ordinates `τ ∈ (T, 2T]` carry
critical-line zeros `ζ(1/2 + iτ) = 0`.

**Proof (first moment instead of per-window Hölder).** Cut `[T, 2T]` into `K ≍ √T` windows of
length `H = T/K`.
- On a window without a critical-line zero, `Z` has constant sign, so `∫_W |Z| = |∫_W Z|`. This is
  at most the resonance-graded window mean `ME` (`exists_abs_integral_hardyZ_window_sharp_le`)
  with cutoff `x ≍ T`.
- The windows together carry `∫_T^{2T} |Z| ≥ 3T/4`. Since `K·ME ≤ 3T/8`, the windows that do
  contain a zero carry at least `3T/8`.
- By Cauchy–Schwarz and `(∫_W |Z|)² ≤ H ∫_W Z²`, the number of such windows is at least
  `(3T/8)²/(H ∫_T^{2T} Z²) ≫ K/(1 + log T)²`.

The per-window fourth-moment gap of the two-sevenths census is not needed. The first moment
`∫_T^{2T} ζ(1/2+it) dt = T + O(T/4)` together with the global second moment suffices.
-/

open Set MeasureTheory Complex Finset

namespace RHTower

noncomputable section

/-- **Constant sign on zero-free windows.** If `ζ(1/2 + iτ) ≠ 0` on `[a, b]`, then
`∫_a^b |Z| = |∫_a^b Z|`. -/
theorem integral_abs_hardyZ_eq_abs_integral {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ τ ∈ Icc a b, riemannZeta (linePt τ) ≠ 0) :
    (∫ τ in a..b, |hardyZ τ|) = |∫ τ in a..b, hardyZ τ| := by
  have hZne : ∀ τ ∈ Icc a b, hardyZ τ ≠ 0 := fun τ hτ h => by
    have := norm_riemannZeta_line_eq_abs_hardyZ τ
    rw [h, abs_zero, norm_eq_zero] at this
    exact hne τ hτ this
  have hcont := continuous_hardyZ
  rcases lt_or_gt_of_ne (hZne a ⟨le_rfl, hab⟩) with hneg | hpos
  · have hall : ∀ τ ∈ Icc a b, hardyZ τ < 0 := by
      intro τ hτ
      by_contra hc
      push Not at hc
      have hpos' : 0 < hardyZ τ := lt_of_le_of_ne hc (Ne.symm (hZne τ hτ))
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hτ.1 hcont.continuousOn
        (show (0 : ℝ) ∈ Icc (hardyZ a) (hardyZ τ) from ⟨hneg.le, hpos'.le⟩)
      exact hZne c ⟨hc.1, le_trans hc.2 hτ.2⟩ hc0
    have h1 : (∫ τ in a..b, |hardyZ τ|) = ∫ τ in a..b, -hardyZ τ := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le hab] at hτ
      exact abs_of_neg (hall τ hτ)
    have h2 : 0 ≤ ∫ τ in a..b, -hardyZ τ :=
      intervalIntegral.integral_nonneg hab fun τ hτ => by linarith [hall τ hτ]
    rw [intervalIntegral.integral_neg] at h2
    rw [h1, intervalIntegral.integral_neg, abs_of_nonpos (by linarith)]
  · have hall : ∀ τ ∈ Icc a b, 0 < hardyZ τ := by
      intro τ hτ
      by_contra hc
      push Not at hc
      have hneg' : hardyZ τ < 0 := lt_of_le_of_ne hc (hZne τ hτ)
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hτ.1 hcont.continuousOn
        (show (0 : ℝ) ∈ Icc (hardyZ τ) (hardyZ a) from ⟨hneg'.le, hpos.le⟩)
      exact hZne c ⟨hc.1, le_trans hc.2 hτ.2⟩ hc0
    have h1 : (∫ τ in a..b, |hardyZ τ|) = ∫ τ in a..b, hardyZ τ := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le hab] at hτ
      exact abs_of_pos (hall τ hτ)
    have h2 : 0 ≤ ∫ τ in a..b, hardyZ τ :=
      intervalIntegral.integral_nonneg hab fun τ hτ => (hall τ hτ).le
    rw [h1, abs_of_nonneg h2]

/-- **First moment of `Z` on a dyadic window.** `∫_T^{2T} |Z| ≥ 3T/4` for large `T`: the
window integral of `ζ(1/2+it)` is `T` up to `T/4`. -/
theorem exists_le_integral_abs_hardyZ :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      3 * T / 4 ≤ ∫ t in T..(2 * T), |hardyZ t| := by
  refine ⟨Real.exp 20000 + 100000, by positivity, ?_⟩
  intro T hT
  have hexp0 : (0 : ℝ) < Real.exp 20000 := Real.exp_pos _
  have hTbig : (100000 : ℝ) ≤ T := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hTexp : Real.exp 20000 ≤ T := by linarith
  have hlogT : (20000 : ℝ) ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).mpr hTexp
  have hlogTpos : (0 : ℝ) < Real.log T := by linarith
  set M : ℕ := ⌈T⌉₊ with hMdef
  set N : ℕ := ⌈65536 * T ^ 2⌉₊ with hNdef
  have hMge : T ≤ (M : ℝ) := Nat.le_ceil T
  have hMle : (M : ℝ) ≤ T + 1 := le_of_lt (Nat.ceil_lt_add_one hTpos.le)
  have hNge : 65536 * T ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 65536 * T ^ 2 + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hM2 : 2 ≤ M := by
    have : (2 : ℝ) ≤ (M : ℝ) := by linarith
    exact_mod_cast this
  have hMN : M ≤ N := by
    refine Nat.ceil_le_ceil ?_
    nlinarith [hTbig]
  -- square-root comparisons
  have hsqrtN_ge : 256 * T ≤ Real.sqrt N := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith [hNge]
  have hsqrtN_le : Real.sqrt N ≤ 257 * T := by
    refine (Real.sqrt_le_left (by linarith : (0:ℝ) ≤ 257 * T)).mpr ?_
    nlinarith [hNle, hTbig]
  have hsqrtM_le : Real.sqrt M ≤ T / 256 := by
    refine (Real.sqrt_le_left (by positivity : (0:ℝ) ≤ T / 256)).mpr ?_
    nlinarith [hMle, hTbig]
  -- logarithm comparisons
  have hlogM : Real.log T ≤ Real.log M := Real.log_le_log hTpos hMge
  have hlogN : 2 * Real.log T ≤ Real.log N := by
    have h1 : Real.log (65536 * T ^ 2) ≤ Real.log N := by
      refine Real.log_le_log (by positivity) hNge
    have h2 : Real.log (65536 * T ^ 2) = Real.log 65536 + 2 * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have h3 : (0 : ℝ) ≤ Real.log 65536 := Real.log_nonneg (by norm_num)
    linarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  -- the four error terms
  have hE1 : 4 * Real.sqrt M / Real.log 2 ≤ T / 16 := by
    have hnum : 4 * Real.sqrt M ≤ 4 * (T / 256) := by linarith
    have hpos : (0 : ℝ) < Real.log 2 := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith [Real.sqrt_nonneg (M : ℝ), hlog2, hnum, hTpos]
  have hE2 : 4 * Real.sqrt N / Real.log M ≤ T / 16 := by
    have hpos : (0 : ℝ) < Real.log M := lt_of_lt_of_le hlogTpos hlogM
    rw [div_le_iff₀ hpos]
    have h1 : 4 * Real.sqrt N ≤ 1028 * T := by linarith
    nlinarith [h1, hlogM, hlogT, hTpos]
  have hE3 : 3 * Real.sqrt N / (Real.log N * T) ≤ T / 16 := by
    have hposN : (0 : ℝ) < Real.log N := by linarith
    have hpos : (0 : ℝ) < Real.log N * T := by positivity
    rw [div_le_iff₀ hpos]
    have h1 : 3 * Real.sqrt N ≤ 771 * T := by linarith
    nlinarith [h1, hlogN, hlogT, hTpos, Real.sqrt_nonneg (N : ℝ)]
  have hE4 : (1 + 4 * T) / Real.sqrt N * T ≤ T / 16 := by
    have hsq : (0 : ℝ) < Real.sqrt N := lt_of_lt_of_le (by positivity) hsqrtN_ge
    rw [div_mul_eq_mul_div, div_le_iff₀ hsq]
    nlinarith [hsqrtN_ge, hTpos, hT1]
  -- the first-moment bound
  have hmain := norm_integral_riemannZeta_line_sub_le hM2 hMN hT1
  have hE : ‖(∫ t in T..(2*T), riemannZeta (linePt t)) - (T : ℂ)‖ ≤ T / 4 := by
    have : (4 * Real.sqrt M / Real.log 2 + 4 * Real.sqrt N / Real.log M)
        + 3 * Real.sqrt N / (Real.log N * T)
        + (1 + 4 * T) / Real.sqrt N * T ≤ T / 4 := by linarith
    linarith
  have hlower : 3 * T / 4 ≤ ‖∫ t in T..(2*T), riemannZeta (linePt t)‖ := by
    have hTnorm : ‖(T : ℂ)‖ = T := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
    have := norm_sub_norm_le (T : ℂ) (∫ t in T..(2*T), riemannZeta (linePt t))
    have hsymm : ‖(T : ℂ) - ∫ t in T..(2*T), riemannZeta (linePt t)‖
        = ‖(∫ t in T..(2*T), riemannZeta (linePt t)) - (T : ℂ)‖ := norm_sub_rev _ _
    rw [hsymm, hTnorm] at this
    linarith
  have hle : T ≤ 2 * T := by linarith
  have h1 : ‖∫ t in T..(2*T), riemannZeta (linePt t)‖
      ≤ ∫ t in T..(2*T), ‖riemannZeta (linePt t)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hle
  have heq : (∫ t in T..(2*T), ‖riemannZeta (linePt t)‖) = ∫ t in T..(2 * T), |hardyZ t| :=
    intervalIntegral.integral_congr fun t _ => norm_riemannZeta_line_eq_abs_hardyZ t
  linarith

/-- **The window census from the first moment.** If the windows carry total `|Z|`-mass at least
`A`, each window mean is at most `ME` and `K·ME ≤ A/2`, then the windows containing a
critical-line zero number at least `(A/2)²/((T/K)·M₂)`, where `M₂ ≥ ∫_T^{2T} Z²`. -/
theorem exists_zeroWindows_of_firstMoment {T : ℝ} {K : ℕ} (hK1 : 1 ≤ K) (hT0 : 0 < T)
    {A M2 ME : ℝ}
    (hA : A ≤ ∫ τ in T..(2 * T), |hardyZ τ|)
    (hM2 : (∫ τ in T..(2 * T), (hardyZ τ) ^ 2) ≤ M2)
    (hE : ∀ k : ℕ, k < K →
      |∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), hardyZ τ| ≤ ME)
    (hKME : (K : ℝ) * ME ≤ A / 2) :
    ∃ S : Finset ℕ,
      (∀ k ∈ S, k < K ∧ ∃ τ, ((T + k * (T / K) ≤ τ ∧ τ ≤ T + ((k + 1 : ℕ) : ℝ) * (T / K)) ∧
        riemannZeta (linePt τ) = 0)) ∧
      (A / 2) ^ 2 ≤ (S.card : ℝ) * ((T / K) * M2) := by
  classical
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hTK0 : (0 : ℝ) < T / K := by positivity
  set a : ℕ → ℝ := fun k => T + k * (T / K) with hadef
  have ha_le : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k; simp only [hadef]; push_cast; nlinarith [hTK0]
  have hlen : ∀ k : ℕ, a (k + 1) - a k = T / K := by
    intro k; simp only [hadef]; push_cast; ring
  set J : ℕ → ℝ := fun k => ∫ τ in (a k)..(a (k + 1)), |hardyZ τ| with hJdef
  set m : ℕ → ℝ := fun k => ∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2 with hmdef
  have hJ0 : ∀ k : ℕ, 0 ≤ J k := fun k =>
    intervalIntegral.integral_nonneg (ha_le k) fun u _ => abs_nonneg _
  have hm0 : ∀ k : ℕ, 0 ≤ m k := fun k =>
    intervalIntegral.integral_nonneg (ha_le k) fun u _ => sq_nonneg _
  have hz : T + ((0 : ℕ) : ℝ) * (T / K) = T := by push_cast; ring
  have hK' : T + (K : ℝ) * (T / K) = 2 * T := by field_simp; ring
  have hsumJ : ∑ k ∈ range K, J k = ∫ τ in T..(2 * T), |hardyZ τ| := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun τ => |hardyZ τ|) (μ := volume) (a := a) (n := K)
      (fun k _ => (continuous_hardyZ.abs.intervalIntegrable _ _))
    simp only [hadef] at h
    rw [hz, hK'] at h
    exact h
  have hsumm : ∑ k ∈ range K, m k = ∫ τ in T..(2 * T), (hardyZ τ) ^ 2 := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun τ => (hardyZ τ) ^ 2) (μ := volume) (a := a) (n := K)
      (fun k _ => ((continuous_hardyZ.pow 2).intervalIntegrable _ _))
    simp only [hadef] at h
    rw [hz, hK'] at h
    exact h
  set p : ℕ → Prop := fun k => ∃ τ, (a k ≤ τ ∧ τ ≤ a (k + 1)) ∧ riemannZeta (linePt τ) = 0
    with hpdef
  set S : Finset ℕ := (range K).filter p with hSdef
  refine ⟨S, fun k hk => ?_, ?_⟩
  · obtain ⟨hkr, hex⟩ := Finset.mem_filter.mp hk
    exact ⟨Finset.mem_range.mp hkr, hex⟩
  -- zero-free windows carry at most `ME`
  have hfree : ∀ k ∈ (range K).filter (fun k => ¬ p k), J k ≤ ME := by
    intro k hk
    obtain ⟨hkr, hkS⟩ := Finset.mem_filter.mp hk
    have hne : ∀ τ ∈ Icc (a k) (a (k + 1)), riemannZeta (linePt τ) ≠ 0 := by
      intro τ hτ h0
      exact hkS ⟨τ, hτ, h0⟩
    have heq := integral_abs_hardyZ_eq_abs_integral (ha_le k) hne
    simp only [hJdef]
    rw [heq]
    exact hE k (Finset.mem_range.mp hkr)
  have hME0 : 0 ≤ ME := le_trans (abs_nonneg _) (hE 0 (by omega))
  have hsplit : ∑ k ∈ range K, J k =
      ∑ k ∈ S, J k + ∑ k ∈ (range K).filter (fun k => ¬ p k), J k :=
    (Finset.sum_filter_add_sum_filter_not (range K) p J).symm
  have hfreesum : ∑ k ∈ (range K).filter (fun k => ¬ p k), J k ≤ K * ME := by
    calc ∑ k ∈ (range K).filter (fun k => ¬ p k), J k
        ≤ ∑ _k ∈ (range K).filter (fun k => ¬ p k), ME := Finset.sum_le_sum hfree
      _ = ((range K).filter (fun k => ¬ p k)).card * ME := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * ME := by
          apply mul_le_mul_of_nonneg_right _ hME0
          have := Finset.card_filter_le (range K) (fun k => ¬ p k)
          rw [Finset.card_range] at this
          exact_mod_cast this
  have hSJ : A / 2 ≤ ∑ k ∈ S, J k := by linarith
  -- Cauchy–Schwarz over the windows with a zero
  have hcs : (∑ k ∈ S, J k) ^ 2 ≤ (S.card : ℝ) * ∑ k ∈ S, (J k) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) J
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  have hwin : ∀ k : ℕ, (J k) ^ 2 ≤ (T / K) * m k := by
    intro k
    have hle := ha_le k
    have hf : IntegrableOn (fun τ => |hardyZ τ|) (Ioc (a k) (a (k + 1))) volume :=
      continuous_hardyZ.abs.integrableOn_Ioc
    have hf2 : IntegrableOn (fun τ => |hardyZ τ| ^ (2 : ℕ)) (Ioc (a k) (a (k + 1))) volume :=
      (continuous_hardyZ.abs.pow 2).integrableOn_Ioc
    have h := GaloisForLFunctions.HTGeometry.sq_integral_le_length_mul hle hf hf2
    rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle,
      hlen k] at h
    simp only [hJdef, hmdef]
    simpa only [sq_abs] using h
  have hmS : ∑ k ∈ S, m k ≤ M2 := by
    calc ∑ k ∈ S, m k ≤ ∑ k ∈ range K, m k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun k _ _ => hm0 k)
      _ = _ := hsumm
      _ ≤ M2 := hM2
  have hA2 : 0 ≤ A / 2 := by
    have : 0 ≤ (K : ℝ) * ME := by positivity
    linarith
  calc (A / 2) ^ 2 ≤ (∑ k ∈ S, J k) ^ 2 := pow_le_pow_left₀ hA2 hSJ 2
    _ ≤ (S.card : ℝ) * ∑ k ∈ S, (J k) ^ 2 := hcs
    _ ≤ (S.card : ℝ) * ∑ k ∈ S, (T / K) * m k := by
        gcongr with k hk
        exact hwin k
    _ = (S.card : ℝ) * ((T / K) * ∑ k ∈ S, m k) := by rw [← Finset.mul_sum]
    _ ≤ (S.card : ℝ) * ((T / K) * M2) := by gcongr

/-- **Second moment on a dyadic window**, from the fourth moment by Cauchy–Schwarz:
`∫_T^{2T} Z² ≤ C₂ T (1 + log T)²`. -/
theorem exists_integral_hardyZ_sq_dyadic_le :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ {T : ℝ}, 8 ≤ T →
      (∫ t in T..(2 * T), (hardyZ t) ^ 2) ≤ C₂ * T * (1 + Real.log T) ^ 2 := by
  obtain ⟨C, hC, hF⟩ := exists_integral_hardyZ_pow_four_dyadic_real_le
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun {T} hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hle : T ≤ 2 * T := by linarith
  have hf : IntegrableOn (fun t => (hardyZ t) ^ 2) (Ioc T (2 * T)) volume :=
    (continuous_hardyZ.pow 2).integrableOn_Ioc
  have hf2 : IntegrableOn (fun t => ((hardyZ t) ^ 2) ^ (2 : ℕ)) (Ioc T (2 * T)) volume :=
    ((continuous_hardyZ.pow 2).pow 2).integrableOn_Ioc
  have h := GaloisForLFunctions.HTGeometry.sq_integral_le_length_mul hle hf hf2
  rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle] at h
  have e : ∀ t : ℝ, ((hardyZ t) ^ 2) ^ (2 : ℕ) = (hardyZ t) ^ 4 := fun t => by ring
  simp only [e, show 2 * T - T = T by ring] at h
  have h4 := hF hT
  have hX0 : 0 ≤ ∫ t in T..(2 * T), (hardyZ t) ^ 2 :=
    intervalIntegral.integral_nonneg hle fun _ _ => sq_nonneg _
  set X := ∫ t in T..(2 * T), (hardyZ t) ^ 2
  set L := 1 + Real.log T
  have hL0 : 0 ≤ L := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T); linarith
  have hsq : X ^ 2 ≤ (Real.sqrt C * T * L ^ 2) ^ 2 := by
    have : (Real.sqrt C * T * L ^ 2) ^ 2 = C * T * T * L ^ 4 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hC]; ring
    rw [this]
    calc X ^ 2 ≤ T * ∫ t in T..(2 * T), (hardyZ t) ^ 4 := h
      _ ≤ T * (C * T * L ^ 4) := mul_le_mul_of_nonneg_left h4 hT0.le
      _ = C * T * T * L ^ 4 := by ring
  exact (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).mp hsq

/-- `1 + log T ≤ 4 T^{1/4}` for `T ≥ 1`. -/
theorem one_add_log_le_four_sqrt_sqrt {T : ℝ} (hT : 1 ≤ T) :
    1 + Real.log T ≤ 4 * Real.sqrt (Real.sqrt T) := by
  have hT0 : 0 < T := by linarith
  set y := Real.sqrt (Real.sqrt T) with hy
  have hy0 : 0 < y := by positivity
  have hy4 : y ^ 4 = T := by
    rw [hy, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hT0.le]
  have hlog : Real.log T = 4 * Real.log y := by
    rw [← hy4, Real.log_pow]; push_cast; ring
  have := Real.log_le_sub_one_of_pos hy0
  linarith

/-- `(1 + log T)² ≤ 64 T^{1/4}` for `T ≥ 1`. -/
theorem one_add_log_sq_le_sqrt_sqrt {T : ℝ} (hT : 1 ≤ T) :
    (1 + Real.log T) ^ 2 ≤ 64 * Real.sqrt (Real.sqrt T) := by
  have hT0 : 0 < T := by linarith
  set y := Real.sqrt (Real.sqrt (Real.sqrt T)) with hy
  have hy0 : 0 < y := by positivity
  have hy2 : y ^ 2 = Real.sqrt (Real.sqrt T) := by
    rw [hy, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hy8 : y ^ 8 = T := by
    rw [show (8 : ℕ) = 2 * 2 * 2 by rfl, pow_mul, pow_mul, hy2,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hT0.le]
  have hlog : Real.log T = 8 * Real.log y := by
    rw [← hy8, Real.log_pow]; push_cast; ring
  have h1 := Real.log_le_sub_one_of_pos hy0
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hle : 1 + Real.log T ≤ 8 * y := by linarith
  calc (1 + Real.log T) ^ 2 ≤ (8 * y) ^ 2 := pow_le_pow_left₀ (by linarith) hle 2
    _ = 64 * Real.sqrt (Real.sqrt T) := by rw [mul_pow, hy2]; norm_num

/-- The window budget: `K · ME ≤ 3T/8` for `K ≤ √T/(64Q²)`, `x = 16QT`, `T^{1/4} ≥ 16Q`. -/
private theorem window_budget_le {T CS Q s4 sT L K x : ℝ} (hT0 : 0 < T) (hQ : Q = CS + 1)
    (hCS : 0 ≤ CS) (hs40 : 0 < s4) (hs4sq : s4 * s4 = sT) (hsTsq : sT * sT = T)
    (hKle : K ≤ sT / (64 * Q ^ 2)) (hK0 : 0 < K) (hlogL : L ≤ 4 * s4) (hL0 : 0 ≤ L)
    (hs4_16 : 16 * Q ≤ s4) (hx : x = 16 * Q * T) (hsqrtx : Real.sqrt x = 4 * Real.sqrt Q * sT) :
    K * (CS * (s4 * L + (T / K) / s4 + Real.sqrt x + (T / K) * T / x)) ≤ 3 * T / 4 / 2 := by
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  have hsT0 : 0 < sT := by nlinarith
  have hCSQ : CS ≤ Q := by linarith
  have hsqrtQ : Real.sqrt Q ≤ Q := by rw [Real.sqrt_le_left hQ0.le]; nlinarith
  have hx0 : 0 < x := by rw [hx]; positivity
  have e1 : K * (CS * (s4 * L + (T / K) / s4 + Real.sqrt x + (T / K) * T / x)) =
      CS * (K * s4 * L) + CS * (T / s4) + CS * (K * Real.sqrt x) + CS * (T * T / x) := by
    field_simp
  have p1 : CS * (K * s4 * L) ≤ T / 16 := by
    have h1 : K * s4 * L ≤ sT / (64 * Q ^ 2) * s4 * (4 * s4) := by
      have := mul_le_mul_of_nonneg_right hKle hs40.le
      exact mul_le_mul this hlogL hL0 (by positivity)
    have h2 : sT / (64 * Q ^ 2) * s4 * (4 * s4) = T / (16 * Q ^ 2) := by
      field_simp; nlinarith [hsTsq, hs4sq]
    have h3 : CS * (K * s4 * L) ≤ Q * (T / (16 * Q ^ 2)) :=
      mul_le_mul hCSQ (h1.trans h2.le) (by positivity) hQ0.le
    have h4 : Q * (T / (16 * Q ^ 2)) = T / (16 * Q) := by
      rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]; ring
    have h5 : T / (16 * Q) ≤ T / 16 := div_le_div_of_nonneg_left hT0.le (by norm_num)
      (by linarith)
    linarith
  have p2 : CS * (T / s4) ≤ T / 16 := by
    have : CS / s4 ≤ 1 / 16 := by rw [div_le_iff₀ hs40]; linarith
    calc CS * (T / s4) = T * (CS / s4) := by ring
      _ ≤ T * (1 / 16) := mul_le_mul_of_nonneg_left this hT0.le
      _ = T / 16 := by ring
  have p3 : CS * (K * Real.sqrt x) ≤ T / 16 := by
    rw [hsqrtx]
    have h1 : K * (4 * Real.sqrt Q * sT) ≤ sT / (64 * Q ^ 2) * (4 * Real.sqrt Q * sT) :=
      mul_le_mul_of_nonneg_right hKle (by positivity)
    have h2 : sT / (64 * Q ^ 2) * (4 * Real.sqrt Q * sT) = Real.sqrt Q * T / (16 * Q ^ 2) := by
      field_simp; nlinarith [hsTsq]
    have h3 : CS * (K * (4 * Real.sqrt Q * sT)) ≤ Q * (Q * T / (16 * Q ^ 2)) := by
      have h4 : Real.sqrt Q * T / (16 * Q ^ 2) ≤ Q * T / (16 * Q ^ 2) := by gcongr
      exact mul_le_mul hCSQ ((h1.trans h2.le).trans h4) (by positivity) hQ0.le
    have h5 : Q * (Q * T / (16 * Q ^ 2)) = T / 16 := by field_simp
    linarith
  have p4 : CS * (T * T / x) ≤ T / 16 := by
    have h1 : T * T / x = T / (16 * Q) := by rw [hx]; field_simp
    rw [h1]
    calc CS * (T / (16 * Q)) ≤ Q * (T / (16 * Q)) := by gcongr
      _ = T / 16 := by field_simp
  rw [e1]; linarith

/-- The final count: from `(3T/8)² ≤ |S|·(T/K)·(D T L²)` with `K ≥ √T/(128Q²)` and
`|S| ≤ 2|τS| + 1`, `|τS| ≥ (c₀/2)√T/L²` once `c₀ T^{1/4} ≥ 64` and `L² ≤ 64 T^{1/4}`. -/
private theorem final_count_le {T sT s4 L Q D K Sc τc : ℝ} (hT0 : 0 < T) (hQ0 : 0 < Q)
    (hD0 : 0 < D) (hs40 : 0 < s4) (hs4sq : s4 * s4 = sT)
    (hL1 : 1 ≤ L) (hK0 : 0 < K) (hKge : sT / (128 * Q ^ 2) ≤ K)
    (hcount : (3 * T / 4 / 2) ^ 2 ≤ Sc * ((T / K) * (D * T * L ^ 2)))
    (hcard : Sc ≤ 2 * τc + 1) (hL2s : L ^ 2 ≤ 64 * s4)
    (hs4c : 64 / (9 / (16384 * Q ^ 2 * D)) ≤ s4) :
    9 / (16384 * Q ^ 2 * D) / 2 * sT / L ^ 2 ≤ τc := by
  set c₀ : ℝ := 9 / (16384 * Q ^ 2 * D) with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  have hsT0 : 0 < sT := by nlinarith
  have hL2 : 0 < L ^ 2 := by positivity
  -- `|S| ≥ 2c₀ √T / L²`
  have hS : 2 * c₀ * sT / L ^ 2 ≤ Sc := by
    have hden : 0 < (T / K) * (D * T * L ^ 2) := by positivity
    have hS' : (3 * T / 4 / 2) ^ 2 / ((T / K) * (D * T * L ^ 2)) ≤ Sc := by
      rw [div_le_iff₀ hden]; exact hcount
    refine le_trans ?_ hS'
    have heq : (3 * T / 4 / 2) ^ 2 / ((T / K) * (D * T * L ^ 2)) = 9 * K / (64 * D * L ^ 2) := by
      field_simp; ring
    rw [heq]
    calc 2 * c₀ * sT / L ^ 2 = 9 / (64 * D * L ^ 2) * (sT / (128 * Q ^ 2)) := by
          rw [hc₀]; field_simp; ring
      _ ≤ 9 / (64 * D * L ^ 2) * K := mul_le_mul_of_nonneg_left hKge (by positivity)
      _ = 9 * K / (64 * D * L ^ 2) := by ring
  -- `c₀ √T / L² ≥ 1`
  have hbig : 1 ≤ c₀ * sT / L ^ 2 := by
    rw [le_div_iff₀ hL2]
    have h64 : 64 ≤ c₀ * s4 := by rw [div_le_iff₀ hc₀0] at hs4c; linarith
    calc 1 * L ^ 2 ≤ 64 * s4 := by linarith
      _ ≤ c₀ * s4 * s4 := by nlinarith
      _ = c₀ * sT := by rw [mul_assoc, hs4sq]
  have e : c₀ / 2 * sT / L ^ 2 = (c₀ * sT / L ^ 2) / 2 := by ring
  have e2 : 2 * c₀ * sT / L ^ 2 = 2 * (c₀ * sT / L ^ 2) := by ring
  rw [e]
  rw [e2] at hS
  linarith

/-- **The square-root critical-line census.** For large `T`, at least `c·√T/(1 + log T)²`
distinct ordinates in `(T, 2T]` carry critical-line zeros of `ζ`. -/
theorem exists_many_distinct_line_zeros_dyadic_sqrt :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      ∃ τS : Finset ℝ, (∀ τ ∈ τS, T < τ ∧ τ ≤ 2 * T ∧ riemannZeta (linePt τ) = 0) ∧
        c * Real.sqrt T / (1 + Real.log T) ^ 2 ≤ (τS.card : ℝ) := by
  classical
  obtain ⟨T₀, hT₀, hfirst⟩ := exists_le_integral_abs_hardyZ
  obtain ⟨CS, hCS, hsharp⟩ := exists_abs_integral_hardyZ_window_sharp_le
  obtain ⟨C₂, hC₂, hsecond⟩ := exists_integral_hardyZ_sq_dyadic_le
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = CS + 1 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C₂ + 1 := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by linarith
  have hD0 : 0 < D := by linarith
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 9 / (16384 * Q ^ 2 * D) := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ,
      T₁ = max (max (max T₀ 256) ((128 * Q ^ 2) ^ 2)) (max ((16 * Q) ^ 4) ((64 / c₀) ^ 4)) :=
    ⟨_, rfl⟩
  have h256 : (256 : ℝ) ≤ T₁ := by
    rw [hT₁]; exact le_trans (le_max_right T₀ 256) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨c₀ / 2, by positivity, T₁, by linarith, fun T hT => ?_⟩
  have hmax := hT; rw [hT₁] at hmax
  have hTT₀ : T₀ ≤ T := le_trans (le_trans (le_max_left T₀ 256)
    (le_trans (le_max_left _ _) (le_max_left _ _))) hmax
  have hT256 : 256 ≤ T := le_trans h256 hT
  have hTK : (128 * Q ^ 2) ^ 2 ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hmax
  have hT16 : (16 * Q) ^ 4 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmax
  have hTc : (64 / c₀) ^ 4 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hmax
  have hT0 : 0 < T := by linarith
  obtain ⟨sT, hsT⟩ : ∃ sT : ℝ, sT = Real.sqrt T := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ s4 : ℝ, s4 = Real.sqrt sT := ⟨_, rfl⟩
  have hsT0 : 0 < sT := by rw [hsT]; exact Real.sqrt_pos.mpr hT0
  have hs40 : 0 < s4 := by rw [hs4]; exact Real.sqrt_pos.mpr hsT0
  have hsTsq : sT * sT = T := by rw [hsT]; exact Real.mul_self_sqrt hT0.le
  have hs4sq : s4 * s4 = sT := by rw [hs4]; exact Real.mul_self_sqrt hsT0.le
  have hsTK : 128 * Q ^ 2 ≤ sT := by rw [hsT]; exact Real.le_sqrt_of_sq_le hTK
  have hs4_16 : 16 * Q ≤ s4 := by
    rw [hs4, hsT]
    refine Real.le_sqrt_of_sq_le (Real.le_sqrt_of_sq_le ?_)
    calc ((16 * Q) ^ 2) ^ 2 = (16 * Q) ^ 4 := by ring
      _ ≤ T := hT16
  have hs4_c : 64 / c₀ ≤ s4 := by
    rw [hs4, hsT]
    refine Real.le_sqrt_of_sq_le (Real.le_sqrt_of_sq_le ?_)
    calc ((64 / c₀) ^ 2) ^ 2 = (64 / c₀) ^ 4 := by ring
      _ ≤ T := hTc
  -- windows
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = sT / (64 * Q ^ 2) := ⟨_, rfl⟩
  have hy2 : 2 ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; nlinarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = ⌊y⌋₊ := ⟨_, rfl⟩
  have hKle : (K : ℝ) ≤ y := by rw [hKdef]; exact Nat.floor_le (by linarith only [hy2])
  have hKge : y / 2 ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one y; rw [← hKdef] at this; linarith only [this, hy2]
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast this
  have hKR0 : (0 : ℝ) < K := by exact_mod_cast hK1
  -- cutoff
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 16 * Q * T := ⟨_, rfl⟩
  have hx1 : 1 ≤ x := by rw [hx]; nlinarith
  have hxe : x ≤ Real.exp T := by
    have hq := Real.quadratic_le_exp_of_nonneg hT0.le
    have h16 : (2 : ℝ) ≤ 16 * Q := by linarith
    have hsq : 32 * Q ≤ (16 * Q) ^ 2 := by nlinarith
    have hsq4 : (16 * Q) ^ 2 ≤ (16 * Q) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hQT : 32 * Q ≤ T := le_trans hsq (le_trans hsq4 hT16)
    have hmul : 16 * Q * T ≤ T ^ 2 / 2 := by nlinarith
    rw [hx]; linarith only [hq, hmul, hT0]
  have hsqrtx : Real.sqrt x = 4 * Real.sqrt Q * sT := by
    rw [hx, hsT, show 16 * Q * T = (4 : ℝ) ^ 2 * Q * T by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 + Real.log T := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hL]; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T); linarith
  -- window means
  have hE : ∀ k : ℕ, k < K →
      |∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), hardyZ τ| ≤
        CS * (s4 * L + (T / K) / s4 + Real.sqrt x + (T / K) * T / x) := by
    intro k hk
    have hkK : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
    have hH0 : 0 < T / K := by positivity
    have ha : T ≤ T + k * (T / K) := by
      have : (0 : ℝ) ≤ k * (T / K) := by positivity
      linarith
    have hsplit : ((k + 1 : ℕ) : ℝ) * (T / K) = k * (T / K) + T / K := by push_cast; ring
    have hab : T + k * (T / K) ≤ T + ((k + 1 : ℕ) : ℝ) * (T / K) := by
      rw [hsplit]; linarith only [hH0]
    have hb : T + ((k + 1 : ℕ) : ℝ) * (T / K) ≤ 2 * T := by
      have h1 : ((k + 1 : ℕ) : ℝ) * (T / K) ≤ K * (T / K) := by
        push_cast; exact mul_le_mul_of_nonneg_right hkK hH0.le
      have h2 : (K : ℝ) * (T / K) = T := by field_simp
      linarith only [h1, h2]
    have h := hsharp hT256 ha hab hb hx1 hxe
    have hlen : T + ((k + 1 : ℕ) : ℝ) * (T / K) - (T + k * (T / K)) = T / K := by
      rw [hsplit]; ring
    rw [hlen, ← hsT, ← hs4, ← hL] at h
    exact h
  have hlogL : L ≤ 4 * s4 := by
    rw [hL, hs4, hsT]; exact one_add_log_le_four_sqrt_sqrt (by linarith only [hT256])
  have hKle' : (K : ℝ) ≤ sT / (64 * Q ^ 2) := by rw [← hy]; exact hKle
  have hKME := window_budget_le hT0 hQ hCS hs40 hs4sq hsTsq hKle' hKR0 hlogL
    (by linarith only [hL1]) hs4_16 hx hsqrtx
  have hM2 : (∫ τ in T..(2 * T), (hardyZ τ) ^ 2) ≤ D * T * L ^ 2 := by
    have h := hsecond (T := T) (by linarith only [hT256])
    rw [← hL] at h
    have : C₂ * T * L ^ 2 ≤ D * T * L ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hD]) hT0.le)
        (sq_nonneg L)
    exact h.trans this
  obtain ⟨S, hS, hcount⟩ :=
    exists_zeroWindows_of_firstMoment hK1 hT0 (hfirst T hTT₀) hM2 hE hKME
  obtain ⟨τS, hτS, hcard⟩ := exists_distinct_ordinates hT0 hK1 S hS
  refine ⟨τS, hτS, ?_⟩
  have hKge' : sT / (128 * Q ^ 2) ≤ (K : ℝ) := by
    have : sT / (128 * Q ^ 2) = y / 2 := by rw [hy]; field_simp; ring
    rw [this]; exact hKge
  have hcardR : (S.card : ℝ) ≤ 2 * (τS.card : ℝ) + 1 := by exact_mod_cast hcard
  have hL2s : L ^ 2 ≤ 64 * s4 := by
    rw [hL, hs4, hsT]; exact one_add_log_sq_le_sqrt_sqrt (by linarith only [hT256])
  have h := final_count_le hT0 hQ0 hD0 hs40 hs4sq hL1 hKR0 hKge' hcount hcardR hL2s
    (by rw [← hc₀]; exact hs4_c)
  rw [← hc₀, hsT, hL] at h
  exact h

/-- **Square-root census difference.** The number of critical-line zeros of `xi` with ordinate in
`(T, 2T]`, counted with multiplicity, is at least `c·√T/(1 + log T)²` for all large `T`. -/
theorem exists_sqrtRoot_le_xiPosCriticalZeroCount_sub :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      c * Real.sqrt T / (1 + Real.log T) ^ 2
        ≤ (xiPosCriticalZeroCount (2 * T) : ℝ) - (xiPosCriticalZeroCount T : ℝ) := by
  obtain ⟨c, hc, T₁, hT₁, h⟩ := exists_many_distinct_line_zeros_dyadic_sqrt
  refine ⟨c, hc, T₁, hT₁, fun T hT => ?_⟩
  obtain ⟨τS, hmemS, hcard⟩ := h T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hinj := xiPosCriticalZeroCount_add_card_le hT0 τS hmemS
  have hcast : (xiPosCriticalZeroCount T : ℝ) + (τS.card : ℝ)
      ≤ (xiPosCriticalZeroCount (2 * T) : ℝ) := by exact_mod_cast hinj
  linarith only [hcard, hcast]

/-- **The square-root critical-line census.** Unconditionally, `N₀(T) ≥ c·√T/(1 + log T)²` for all
large `T`, where `N₀(T)` counts critical-line zeros of `xi` with ordinate in `(0, T]`, with
multiplicity. -/
theorem exists_sqrtRoot_le_xiPosCriticalZeroCount :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      c * Real.sqrt T / (1 + Real.log T) ^ 2 ≤ (xiPosCriticalZeroCount T : ℝ) := by
  obtain ⟨c, hc, T₁, hT₁, h⟩ := exists_sqrtRoot_le_xiPosCriticalZeroCount_sub
  refine ⟨c / 2, by positivity, max (2 * T₁) 2, ?_, fun T hT => ?_⟩
  · have h1 := le_max_right (2 * T₁) 2
    linarith
  have hT2 : (2 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT20 : (0 : ℝ) < T / 2 := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hhalf : T₁ ≤ T / 2 := by
    have h1 := le_trans (le_max_left (2 * T₁) 2) hT
    linarith
  have hspec := h (T / 2) hhalf
  rw [show 2 * (T / 2) = T by ring] at hspec
  have hl1 : (0 : ℝ) ≤ Real.log (T / 2) := Real.log_nonneg (by linarith)
  have hl2 : Real.log (T / 2) ≤ Real.log T := Real.log_le_log hT20 (by linarith)
  have hp1 : (0 : ℝ) < 1 + Real.log (T / 2) := by linarith
  have hp2 : (0 : ℝ) < 1 + Real.log T := by linarith
  have hlogc : (1 + Real.log (T / 2)) ^ 2 ≤ (1 + Real.log T) ^ 2 :=
    pow_le_pow_left₀ hp1.le (by linarith) 2
  have hchain : Real.sqrt T ≤ 2 * Real.sqrt (T / 2) := by
    have h1 : Real.sqrt T = Real.sqrt 2 * Real.sqrt (T / 2) := by
      rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
    have h2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [h1]
    exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
  have hfinal : c / 2 * Real.sqrt T / (1 + Real.log T) ^ 2
      ≤ c * Real.sqrt (T / 2) / (1 + Real.log (T / 2)) ^ 2 := by
    have hq1 : (0 : ℝ) < (1 + Real.log T) ^ 2 := pow_pos hp2 2
    have hq2 : (0 : ℝ) < (1 + Real.log (T / 2)) ^ 2 := pow_pos hp1 2
    rw [div_le_div_iff₀ hq1 hq2]
    have hprod : Real.sqrt T * (1 + Real.log (T / 2)) ^ 2
        ≤ (2 * Real.sqrt (T / 2)) * (1 + Real.log T) ^ 2 :=
      mul_le_mul hchain hlogc hq2.le (by positivity)
    have hscale := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ c / 2)
    calc c / 2 * Real.sqrt T * (1 + Real.log (T / 2)) ^ 2
        = c / 2 * (Real.sqrt T * (1 + Real.log (T / 2)) ^ 2) := by ring
      _ ≤ c / 2 * ((2 * Real.sqrt (T / 2)) * (1 + Real.log T) ^ 2) := hscale
      _ = c * Real.sqrt (T / 2) * (1 + Real.log T) ^ 2 := by ring
  have hcnn : (0 : ℝ) ≤ (xiPosCriticalZeroCount (T / 2) : ℝ) := Nat.cast_nonneg _
  calc c / 2 * Real.sqrt T / (1 + Real.log T) ^ 2
      ≤ c * Real.sqrt (T / 2) / (1 + Real.log (T / 2)) ^ 2 := hfinal
    _ ≤ (xiPosCriticalZeroCount T : ℝ) - (xiPosCriticalZeroCount (T / 2) : ℝ) := hspec
    _ ≤ (xiPosCriticalZeroCount T : ℝ) := by linarith

end

end RHTower
