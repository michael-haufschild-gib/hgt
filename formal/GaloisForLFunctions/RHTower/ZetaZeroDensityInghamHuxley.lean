import GaloisForLFunctions.RHTower.ZetaZeroDensityWindowClassCount
import GaloisForLFunctions.RHTower.ZetaZeroDensityHypothesisFiveSixths
import GaloisForLFunctions.RHTower.ZetaZeroDetectorNearLineDichotomy

/-!
# The Ingham–Huxley zero-density estimate

For `1/2 < σ ≤ 1` put

`A(σ) = 3/(2 - σ)` for `σ ≤ 3/4`, `A(σ) = 3/(3σ - 1)` for `3/4 < σ ≤ 5/6`, `A(σ) = 2` for `σ > 5/6`.

For every `0 < ε ≤ 1` there are `D, B, T₀` with
`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^B T^{(A(σ) + ε)(1 - σ)}` for `T ≥ T₀`
(`exists_zeroHeightBox_ncard_le_ingham_huxley`).

The detector runs with the ratio-`3/2` window at `a = (A + ε/2)/3`, smoothing `T^{3a/4}` and
mollifier `T^{ε/32}` (`exists_zeroHeightBox_ncard_le_window`); the detector dichotomy near the
line is `exists_pDetector_dichotomy_of_gap`.  The exponent `A` is exactly where
the window's binding term meets the target:

* Ingham: `1 + (A/3)(1 - 2σ) = A(1 - σ)` iff `A(2 - σ) = 3` (mean value range);
* Huxley: `1 + (A/3)(4 - 6σ) = A(1 - σ)` iff `A(3σ - 1) = 3` (Huxley range, threshold `σ > 3/4`);
* the Type II count needs `A ≥ 2`, which holds on `[1/2, 5/6]` for both formulas.
-/

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve

/-- **The Type II count for a window.** -/
theorem card_typeTwo_le_window {K₀ c₀ D₄ T σ E δ y : ℝ} (hK₀ : 0 ≤ K₀) (hc₀ : 0 < c₀)
    (hD₄ : 0 ≤ D₄) (hδ0 : 0 ≤ δ) (hy0 : 0 ≤ y) (hT2 : 2 ≤ T) (hLT : K₀ * Real.log T ≤ T)
    (hII : 1 + 4 * δ + y * (2 - 4 * σ) ≤ E)
    (h4 : ∫ u in (-(3 * T))..(3 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 4 ≤
      D₄ * T * (1 + Real.log T) ^ 4)
    {W : Finset ℝ} (hW : ∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T)
    (hsep : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|)
    (hbig : ∀ t ∈ W, c₀ * pDetSmooth y T ^ (σ - 1 / 2) / pDetMoll δ T ≤
      ∫ s in (-(K₀ * Real.log T))..(K₀ * Real.log T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((t + s : ℝ) : ℂ) * I)‖) :
    (W.card : ℝ) ≤ (8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4) * (1 + Real.log T) ^ 8 * T ^ E := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (pDetMoll δ T : ℝ) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = pDetSmooth y T := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = K₀ * Real.log T := ⟨_, rfl⟩
  rw [← hX, ← hY, ← hL] at hbig
  rw [← hL] at hLT
  have hX1 : 1 ≤ X := by rw [hX]; exact_mod_cast one_le_pDetMoll hδ0 hT1
  have hXle : X ≤ T ^ δ := by rw [hX]; exact pDetMoll_le hT1
  have hY1 : 1 ≤ Y := by rw [hY]; exact one_le_pDetSmooth hy0 hT1
  have hYT : Y = T ^ y := hY
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = c₀ * Y ^ (σ - 1 / 2) / X := ⟨_, rfl⟩
  rw [← hV] at hbig
  have hYp : 0 < Y ^ (σ - 1 / 2) := Real.rpow_pos_of_pos hY0 _
  have hV0 : 0 < V := by rw [hV]; positivity
  have hcount := card_mul_pow_four_le_typeTwo hL0 hLT hW hsep hV0.le hbig
  have hl1 : 0 ≤ 1 + Real.log T := by linarith
  have hLlog : L ≤ K₀ * (1 + Real.log T) := by rw [hL]; nlinarith
  have hpre : (2 * L) ^ 3 * (2 * L + 1) ≤ 8 * K₀ ^ 3 * (2 * K₀ + 1) * (1 + Real.log T) ^ 4 := by
    have h1 : (2 * L) ^ 3 ≤ (2 * (K₀ * (1 + Real.log T))) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    have h2 : 2 * L + 1 ≤ (2 * K₀ + 1) * (1 + Real.log T) := by nlinarith
    calc (2 * L) ^ 3 * (2 * L + 1) ≤ (2 * (K₀ * (1 + Real.log T))) ^ 3 *
          ((2 * K₀ + 1) * (1 + Real.log T)) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 8 * K₀ ^ 3 * (2 * K₀ + 1) * (1 + Real.log T) ^ 4 := by ring
  have hX4 : X ^ 4 ≤ T ^ (4 * δ) := by
    calc X ^ 4 ≤ (T ^ δ) ^ 4 := pow_le_pow_left₀ (by linarith) hXle 4
      _ = T ^ (4 * δ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
  have hTY : T ^ E * (Y ^ (σ - 1 / 2)) ^ 4 = T ^ (E + 4 * y * (σ - 1 / 2)) := by
    rw [hYT, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le, ← Real.rpow_mul hT0.le,
      ← Real.rpow_add hT0]
    congr 1
    push_cast
    ring
  have hheight : T * X ^ 4 ≤ T ^ E * (Y ^ (σ - 1 / 2)) ^ 4 := by
    rw [hTY]
    calc T * X ^ 4 ≤ T * T ^ (4 * δ) := mul_le_mul_of_nonneg_left hX4 hT0.le
      _ = T ^ (1 + 4 * δ) := by rw [Real.rpow_add hT0, Real.rpow_one]
      _ ≤ T ^ (E + 4 * y * (σ - 1 / 2)) := by
          apply Real.rpow_le_rpow_of_exponent_le hT1
          linarith
  have hV4 : V ^ 4 = c₀ ^ 4 * (Y ^ (σ - 1 / 2)) ^ 4 / X ^ 4 := by rw [hV]; ring
  have hX0 : 0 < X := by linarith
  have hfinal : (W.card : ℝ) * V ^ 4 ≤
      (8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4) * (1 + Real.log T) ^ 8 * T ^ E * V ^ 4 := by
    refine le_trans hcount (le_trans (mul_le_mul hpre h4 (by
      exact intervalIntegral.integral_nonneg (by linarith) fun u _ => by positivity)
      (by positivity)) ?_)
    rw [hV4]
    have e : 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4 * (1 + Real.log T) ^ 8 *
        T ^ E * (c₀ ^ 4 * (Y ^ (σ - 1 / 2)) ^ 4 / X ^ 4) =
        8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ * (1 + Real.log T) ^ 8 *
          (T ^ E * (Y ^ (σ - 1 / 2)) ^ 4) / X ^ 4 := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    calc 8 * K₀ ^ 3 * (2 * K₀ + 1) * (1 + Real.log T) ^ 4 * (D₄ * T * (1 + Real.log T) ^ 4) *
          X ^ 4
        = 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ * (1 + Real.log T) ^ 8 * (T * X ^ 4) := by ring
      _ ≤ 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ * (1 + Real.log T) ^ 8 *
            (T ^ E * (Y ^ (σ - 1 / 2)) ^ 4) :=
          mul_le_mul_of_nonneg_left hheight (by positivity)
  exact le_of_mul_le_mul_right hfinal (by positivity)

/-- **The box count for a ratio-`3/2` window at a fixed `σ > 1/2`.** -/
theorem exists_zeroHeightBox_ncard_le_window {a δ σ E κ : ℝ} {M : ℕ} (ha0 : 0 < a)
    (ha1 : a ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hM : 2 * a / δ ≤ M) (hM2 : 2 ≤ M) (hκ : 0 < κ)
    (hσ₁ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hdiag : (3 * a + κ) * (1 - σ) ≤ E)
    (hreg : 1 + a * (1 - 2 * σ) ≤ E ∨ (1 + a * (4 - 6 * σ) ≤ E ∧ a * (3 / 2 - 2 * σ) < 0))
    (hII : 1 + 4 * δ + 3 * a / 4 * (2 - 4 * σ) ≤ E) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D * (1 + Real.log T) ^ (windowLogExponent M + 4) * T ^ E := by
  have hy0 : 0 < 3 * a / 4 := by positivity
  obtain ⟨K₀, c₀, T₁, hc₀, hK₀, hT₁, hdich⟩ :=
    exists_pDetector_dichotomy_of_gap hδ0 hδ1 hy0 (by linarith) hσ₁
  obtain ⟨T₂, hcls⟩ :=
    exists_window_class_card_le ha0 ha1 hδ0 hM hM2 hκ (by linarith) hσ1 hdiag hreg
  obtain ⟨D₄, hD₄, h4⟩ := exists_integral_norm_riemannZeta_half_pow_four_le
  obtain ⟨TA, hTA⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 2 (c := 1 / 4) (by norm_num) 1)
  obtain ⟨TK, hTK⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 1 (c := 1) (by norm_num) K₀)
  obtain ⟨TY, hTY⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hy0).eventually_ge_atTop 2)
  set F₀ : ℝ := 21 * (16 * (|xiLineTwoLogDerivConstant| + 3)) with hF₀
  set K₂ : ℝ := 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4 with hK₂
  have hF₀0 : 0 ≤ F₀ := by rw [hF₀]; have := abs_nonneg xiLineTwoLogDerivConstant; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hCC0 := windowCountConstant_nonneg M
  refine ⟨F₀ * (windowCountConstant M + K₂), by positivity,
    max (max T₁ T₂) (max (max TA TK) (max TY 4)), le_trans (by norm_num)
      (le_trans (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro T hT
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTTA : TA ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hT
  have hTTK : TK ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hT
  have hTTY : TY ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hT
  have hT4 : (4 : ℝ) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hTA' : Real.log T ^ 2 ≤ T ^ (1 / 4 : ℝ) := by
    have h := hTA T hTTA
    rw [one_mul] at h
    exact le_trans (pow_le_pow_left₀ hlog0 (by linarith) 2) h
  have hZT : T ^ (3 * a / 4) * Real.log T ^ 2 ≤ T := by
    calc T ^ (3 * a / 4) * Real.log T ^ 2 ≤ T ^ (3 / 4 : ℝ) * T ^ (1 / 4 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hTA' (by positivity)
            (Real.rpow_nonneg hT0.le _)
      _ = T := by rw [← Real.rpow_add hT0]; norm_num
  have hLT : K₀ * Real.log T ≤ T := by
    have h := hTK T hTTK
    simp only [pow_one, Real.rpow_one] at h
    nlinarith
  set Zc := pDetCut (3 * a / 4) T with hZc
  have hZle : (Zc : ℝ) ≤ T ^ (3 * a / 4) * Real.log T ^ 2 := Nat.floor_le (by positivity)
  have hZ2 : 2 ≤ Zc := by
    have h2 : (2 : ℝ) ≤ T ^ (3 * a / 4) * Real.log T ^ 2 :=
      le_trans (hTY T hTTY) (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    rw [hZc, pDetCut]
    exact Nat.le_floor (by exact_mod_cast h2)
  have hZTR : (Zc : ℝ) ≤ T := le_trans hZle hZT
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log T := ⟨_, rfl⟩
  obtain ⟨Ex, hEx⟩ : ∃ Ex : ℕ, Ex = windowLogExponent M := ⟨_, rfl⟩
  rw [← hℓ, ← hEx]
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hE8 : 8 ≤ Ex := by
    rw [hEx, windowLogExponent]
    have := Nat.one_le_two_pow (n := 4 * M)
    omega
  have hX1 : 1 ≤ pDetMoll δ T := one_le_pDetMoll hδ0.le hT1
  have hY1 : 1 ≤ pDetSmooth (3 * a / 4) T := one_le_pDetSmooth hy0.le hT1
  obtain ⟨W, hWT, hWsep, hcase, hcount⟩ :=
    exists_separated_gDet_class (hdich T hTT₁) hc₀ hX1 hY1 hZ2 hT0 le_rfl (by linarith)
  have hpre := gDet_prefactor_le hT1 hZ2 hZTR
  rw [← hℓ] at hpre
  have hWcard : (W.card : ℝ) ≤ (windowCountConstant M + K₂) * ℓ ^ Ex * T ^ E := by
    have hℓ8 : ℓ ^ 8 ≤ ℓ ^ Ex := pow_le_pow_right₀ hℓ1 hE8
    have hTE : 0 ≤ T ^ E := Real.rpow_nonneg hT0.le _
    rcases hcase with h2 | ⟨j, hj, i, hi, m, hm, h1⟩
    · have hc := card_typeTwo_le_window hK₀ hc₀ hD₄ hδ0.le hy0.le (by linarith) hLT hII
        (h4 (by linarith)) hWT hWsep h2
      rw [← hℓ, ← hK₂] at hc
      calc (W.card : ℝ) ≤ K₂ * ℓ ^ 8 * T ^ E := hc
        _ ≤ K₂ * ℓ ^ Ex * T ^ E := by gcongr
        _ ≤ (windowCountConstant M + K₂) * ℓ ^ Ex * T ^ E := by
            gcongr
            linarith
    · have hΛ0 : 0 ≤ gDetLog Zc :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Zc))
      have hσσ' : σ ≤ σ + m / gDetLog Zc :=
        le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hΛ0)
      have hc := hcls T hTT₂ j i _ hσσ' W hWT hWsep h1
      rw [← hℓ, ← hEx] at hc
      calc (W.card : ℝ) ≤ windowCountConstant M * ℓ ^ Ex * T ^ E := hc
        _ ≤ (windowCountConstant M + K₂) * ℓ ^ Ex * T ^ E := by
            gcongr
            linarith
  calc ((zeroHeightBox σ T).ncard : ℝ)
      ≤ ((gDetBlockCount Zc * (gDetBlockCount Zc + 8) * (⌊gDetLog Zc⌋₊ + 1) + 1 : ℕ) : ℝ) *
          densityWindowCapacity T * W.card := hcount
    _ ≤ (F₀ * ℓ ^ 4) * ((windowCountConstant M + K₂) * ℓ ^ Ex * T ^ E) :=
        mul_le_mul hpre hWcard (Nat.cast_nonneg _) (by positivity)
    _ = F₀ * (windowCountConstant M + K₂) * ℓ ^ (Ex + 4) * T ^ E := by
        rw [pow_add]
        ring

/-- The Ingham–Huxley exponent. -/
def inghamHuxleyExponent (σ : ℝ) : ℝ :=
  if σ ≤ 3 / 4 then 3 / (2 - σ) else if σ ≤ 5 / 6 then 3 / (3 * σ - 1) else 2

/-- **The Ingham–Huxley zero-density estimate.** -/
theorem exists_zeroHeightBox_ncard_le_ingham_huxley {σ ε : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D * (1 + Real.log T) ^ B * T ^ ((inghamHuxleyExponent σ + ε) * (1 - σ)) := by
  set A := inghamHuxleyExponent σ with hAdef
  set a : ℝ := (A + ε / 2) / 3 with ha
  set δ : ℝ := ε / 32 with hδ
  set M : ℕ := ⌈2 * a / δ⌉₊ + 2 with hMdef
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  have hM : 2 * a / δ ≤ M := by
    rw [hMdef]; push_cast; linarith [Nat.le_ceil (2 * a / δ)]
  have hM2 : 2 ≤ M := by rw [hMdef]; omega
  -- the three regimes give `2 ≤ A ≤ 12/5` and the binding identity
  have hcases : (σ ≤ 3 / 4 ∧ A * (2 - σ) = 3) ∨ (3 / 4 < σ ∧ σ ≤ 5 / 6 ∧ A * (3 * σ - 1) = 3)
      ∨ (5 / 6 < σ ∧ A = 2) := by
    rw [hAdef, inghamHuxleyExponent]
    by_cases h1 : σ ≤ 3 / 4
    · left
      rw [if_pos h1]
      have hne : (2 - σ) ≠ 0 := by linarith
      exact ⟨h1, by field_simp⟩
    · right
      rw [if_neg h1]
      by_cases h2 : σ ≤ 5 / 6
      · left
        rw [if_pos h2]
        have hne : (3 * σ - 1) ≠ 0 := by
          have := lt_of_not_ge h1
          linarith
        exact ⟨lt_of_not_ge h1, h2, by field_simp⟩
      · right
        rw [if_neg h2]
        exact ⟨lt_of_not_ge h2, rfl⟩
  have hA2 : 2 ≤ A := by
    rcases hcases with ⟨h1, hA⟩ | ⟨h1, h2, hA⟩ | ⟨h1, hA⟩
    · nlinarith
    · nlinarith
    · linarith
  have hA12 : A ≤ 12 / 5 := by
    rcases hcases with ⟨h1, hA⟩ | ⟨h1, h2, hA⟩ | ⟨h1, hA⟩
    · nlinarith
    · nlinarith
    · linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have hdiag : (3 * a + ε / 2) * (1 - σ) ≤ (A + ε) * (1 - σ) := by
    rw [ha]
    apply le_of_eq
    ring
  have hII : 1 + 4 * δ + 3 * a / 4 * (2 - 4 * σ) ≤ (A + ε) * (1 - σ) := by
    rw [ha, hδ]
    nlinarith
  have hreg : 1 + a * (1 - 2 * σ) ≤ (A + ε) * (1 - σ) ∨
      (1 + a * (4 - 6 * σ) ≤ (A + ε) * (1 - σ) ∧ a * (3 / 2 - 2 * σ) < 0) := by
    rcases hcases with ⟨h1, hA⟩ | ⟨h1, h2, hA⟩ | ⟨h1, hA⟩
    · left
      have key : 1 + a * (1 - 2 * σ) - (A + ε) * (1 - σ) = ε * ((1 - 2 * σ) / 6 - (1 - σ)) := by
        rw [ha]
        linear_combination (-1 / 3 : ℝ) * hA
      nlinarith
    · right
      refine ⟨?_, by nlinarith⟩
      have key : 1 + a * (4 - 6 * σ) - (A + ε) * (1 - σ) = -(ε / 3) := by
        rw [ha]
        linear_combination (-1 / 3 : ℝ) * hA
      linarith
    · right
      refine ⟨?_, by nlinarith⟩
      have key : 1 + a * (4 - 6 * σ) - (A + ε) * (1 - σ) = 5 / 3 - 2 * σ - ε / 3 := by
        rw [ha, hA]
        ring
      linarith
  obtain ⟨D, hD, T₀, hT₀, hbound⟩ := exists_zeroHeightBox_ncard_le_window ha0 ha1 hδ0 hδ1 hM hM2
    (by positivity : (0 : ℝ) < ε / 2) hσ hσ1 hdiag hreg hII
  exact ⟨D, hD, windowLogExponent M + 4, T₀, hT₀, hbound⟩

end RHTower

end
