import GaloisForLFunctions.RHTower.ZetaZeroDensityHypothesisClassCount
import GaloisForLFunctions.RHTower.ZetaZeroDensityTwelveFifths

/-!
# The density hypothesis on `σ ≥ 5/6`

For every `0 < ε ≤ 1` there are `D ≥ 0` and `T₀` such that for all `T ≥ T₀` and `5/6 ≤ σ ≤ 1`,

`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^{B+4} T^{(2 + ε)(1 - σ)}`

(zeros counted with multiplicity, `B = dhLogExponent ε`;
`exists_zeroHeightBox_ncard_le_density_hypothesis`).

The detector runs with `X = ⌊T^{ε/16}⌋`, `Y = T^{1/2+ε/8}`.  The separated class of
`exists_separated_gDet_class` is either a Type I class, counted by `exists_dh_class_card_le`, or a
Type II set `W`, counted by the critical fourth moment:
`#W ≪ (log T)⁸ T X⁴ Y^{2-4σ} ≤ (log T)⁸ T^{1 + ε/4 - (2 + ε/2)(σ - 1/2)} ≤ (log T)⁸ T^{(2+ε)(1-σ)}`,
the last step being `(ε/2)(1 - σ) ≥ 0`.
-/

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve

/-- **The Type II count on `σ ≥ 5/6`.** -/
theorem card_typeTwo_le_dh {K₀ c₀ D₄ T σ ε : ℝ} (hK₀ : 0 ≤ K₀) (hc₀ : 0 < c₀)
    (hD₄ : 0 ≤ D₄) (hε : 0 < ε) (hT2 : 2 ≤ T) (hLT : K₀ * Real.log T ≤ T) (hσ1 : σ ≤ 1)
    (h4 : ∫ u in (-(3 * T))..(3 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 4 ≤
      D₄ * T * (1 + Real.log T) ^ 4)
    {W : Finset ℝ} (hW : ∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T)
    (hsep : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|)
    (hbig : ∀ t ∈ W, c₀ * pDetSmooth (dhSmoothExp ε) T ^ (σ - 1 / 2)
        / pDetMoll (dhMollExp ε) T ≤
      ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖) :
    (W.card : ℝ) ≤ (8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4) * (1 + Real.log T) ^ 8 *
      T ^ ((2 + ε) * (1 - σ)) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (pDetMoll (dhMollExp ε) T : ℝ) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = pDetSmooth (dhSmoothExp ε) T := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = K₀ * Real.log T := ⟨_, rfl⟩
  rw [← hX, ← hY, ← hL] at hbig
  rw [← hL] at hLT
  have hX1 : 1 ≤ X := by
    rw [hX]; exact_mod_cast one_le_pDetMoll (by unfold dhMollExp; positivity) hT1
  have hXle : X ≤ T ^ (ε / 16) := by rw [hX]; exact pDetMoll_le hT1
  have hY1 : 1 ≤ Y := by
    rw [hY]; exact one_le_pDetSmooth (by unfold dhSmoothExp; positivity) hT1
  have hYT : Y = T ^ (1 / 2 + ε / 8) := hY
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
  -- the height exponent
  have hX4 : X ^ 4 ≤ T ^ (ε / 4) := by
    calc X ^ 4 ≤ (T ^ (ε / 16)) ^ 4 := pow_le_pow_left₀ (by linarith) hXle 4
      _ = T ^ (ε / 4) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
  have hTY : T ^ ((2 + ε) * (1 - σ)) * (Y ^ (σ - 1 / 2)) ^ 4
      = T ^ ((2 + ε) * (1 - σ) + (2 + ε / 2) * (σ - 1 / 2)) := by
    rw [hYT, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le, ← Real.rpow_mul hT0.le,
      ← Real.rpow_add hT0]
    congr 1
    push_cast
    ring
  have hheight : T * X ^ 4 ≤ T ^ ((2 + ε) * (1 - σ)) * (Y ^ (σ - 1 / 2)) ^ 4 := by
    rw [hTY]
    calc T * X ^ 4 ≤ T * T ^ (ε / 4) := mul_le_mul_of_nonneg_left hX4 hT0.le
      _ = T ^ (1 + ε / 4) := by rw [Real.rpow_add hT0, Real.rpow_one]
      _ ≤ T ^ ((2 + ε) * (1 - σ) + (2 + ε / 2) * (σ - 1 / 2)) := by
          apply Real.rpow_le_rpow_of_exponent_le hT1
          nlinarith
  have hV4 : V ^ 4 = c₀ ^ 4 * (Y ^ (σ - 1 / 2)) ^ 4 / X ^ 4 := by rw [hV]; ring
  have hX0 : 0 < X := by linarith
  have hfinal : (W.card : ℝ) * V ^ 4 ≤
      (8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4) * (1 + Real.log T) ^ 8 *
        T ^ ((2 + ε) * (1 - σ)) * V ^ 4 := by
    refine le_trans hcount (le_trans (mul_le_mul hpre h4 (by
      exact intervalIntegral.integral_nonneg (by linarith) fun u _ => by positivity)
      (by positivity)) ?_)
    rw [hV4]
    have e : 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4 * (1 + Real.log T) ^ 8 *
        T ^ ((2 + ε) * (1 - σ)) * (c₀ ^ 4 * (Y ^ (σ - 1 / 2)) ^ 4 / X ^ 4) =
        8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ * (1 + Real.log T) ^ 8 *
          (T ^ ((2 + ε) * (1 - σ)) * (Y ^ (σ - 1 / 2)) ^ 4) / X ^ 4 := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    calc 8 * K₀ ^ 3 * (2 * K₀ + 1) * (1 + Real.log T) ^ 4 * (D₄ * T * (1 + Real.log T) ^ 4) *
          X ^ 4
        = 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ * (1 + Real.log T) ^ 8 * (T * X ^ 4) := by ring
      _ ≤ 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ * (1 + Real.log T) ^ 8 *
            (T ^ ((2 + ε) * (1 - σ)) * (Y ^ (σ - 1 / 2)) ^ 4) :=
          mul_le_mul_of_nonneg_left hheight (by positivity)
  exact le_of_mul_le_mul_right hfinal (by positivity)

/-- The class-count prefactor `(J(J+8)(⌊Λ⌋+1) + 1)·16(|C| + log(2T+5))` is `O((1 + log T)⁴)`
whenever `2 ≤ Z ≤ T`. -/
theorem gDet_prefactor_le {Z : ℕ} {T : ℝ} (hT1 : 1 ≤ T) (hZ : 2 ≤ Z) (hZT : (Z : ℝ) ≤ T) :
    ((gDetBlockCount Z * (gDetBlockCount Z + 8) * (⌊gDetLog Z⌋₊ + 1) + 1 : ℕ) : ℝ) *
        densityWindowCapacity T ≤
      21 * (16 * (|xiLineTwoLogDerivConstant| + 3)) * (1 + Real.log T) ^ 4 := by
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hJ := gDetBlockCount_le_log hZ hZT
  have hΛ : gDetLog Z ≤ Real.log T := by
    unfold gDetLog
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < Z)) hZT
  have hΛ0 : 0 ≤ gDetLog Z := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Z))
  have hM : ((⌊gDetLog Z⌋₊ + 1 : ℕ) : ℝ) ≤ 1 + Real.log T := by
    push_cast
    have := Nat.floor_le hΛ0
    linarith
  have hcap := densityWindowCapacity_le hT1
  have hcap0 : 0 ≤ densityWindowCapacity T := by
    unfold densityWindowCapacity
    have := abs_nonneg xiLineTwoLogDerivConstant
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T + 5 by linarith)
    positivity
  set ℓ := 1 + Real.log T with hℓ
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hJ0 : (0 : ℝ) ≤ gDetBlockCount Z := Nat.cast_nonneg _
  have hcount : ((gDetBlockCount Z * (gDetBlockCount Z + 8) * (⌊gDetLog Z⌋₊ + 1) + 1 : ℕ) :
      ℝ) ≤ 21 * ℓ ^ 3 := by
    push_cast
    push_cast at hM
    have h1 : (gDetBlockCount Z : ℝ) * ((gDetBlockCount Z : ℝ) + 8) ≤ 2 * ℓ * (10 * ℓ) :=
      mul_le_mul hJ (by linarith) (by positivity) (by positivity)
    have h2 : (gDetBlockCount Z : ℝ) * ((gDetBlockCount Z : ℝ) + 8) *
        ((⌊gDetLog Z⌋₊ : ℝ) + 1) ≤ 2 * ℓ * (10 * ℓ) * ℓ :=
      mul_le_mul h1 hM (by positivity) (by positivity)
    have h3 : (1 : ℝ) ≤ ℓ ^ 3 := one_le_pow₀ hℓ1
    nlinarith
  calc ((gDetBlockCount Z * (gDetBlockCount Z + 8) * (⌊gDetLog Z⌋₊ + 1) + 1 : ℕ) : ℝ) *
        densityWindowCapacity T
      ≤ (21 * ℓ ^ 3) * (16 * (|xiLineTwoLogDerivConstant| + 3) * ℓ) :=
        mul_le_mul hcount hcap hcap0 (by positivity)
    _ = 21 * (16 * (|xiLineTwoLogDerivConstant| + 3)) * ℓ ^ 4 := by ring

/-- **The density hypothesis on `σ ≥ 5/6`.** -/
theorem exists_zeroHeightBox_ncard_le_density_hypothesis {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 5 / 6 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D * (1 + Real.log T) ^ (dhLogExponent ε + 4) * T ^ ((2 + ε) * (1 - σ)) := by
  have hδ0 : 0 < dhMollExp ε := by unfold dhMollExp; positivity
  have hδ1 : dhMollExp ε ≤ 1 := by unfold dhMollExp; linarith
  have hy0 : 0 < dhSmoothExp ε := by unfold dhSmoothExp; positivity
  have hy1 : dhSmoothExp ε ≤ 5 / 8 := by unfold dhSmoothExp; linarith
  obtain ⟨K₀, c₀, T₁, hc₀, hK₀, hT₁, hdich⟩ :=
    exists_pDetector_dichotomy hδ0 hδ1 hy0 (by linarith) (show (7 : ℝ) / 12 ≤ 5 / 6 by norm_num)
  obtain ⟨T₂, hcls⟩ := exists_dh_class_card_le hε hε1
  obtain ⟨D₄, hD₄, h4⟩ := exists_integral_norm_riemannZeta_half_pow_four_le
  obtain ⟨TA, hTA⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 2 (c := 3 / 8) (by norm_num) 1)
  obtain ⟨TK, hTK⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 1 (c := 1) (by norm_num) K₀)
  set F₀ : ℝ := 21 * (16 * (|xiLineTwoLogDerivConstant| + 3)) with hF₀
  set K₂ : ℝ := 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4 with hK₂
  have hF₀0 : 0 ≤ F₀ := by rw [hF₀]; have := abs_nonneg xiLineTwoLogDerivConstant; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hCC0 := dhCountConstant_nonneg ε
  refine ⟨F₀ * (dhCountConstant ε + K₂), by positivity,
    max (max T₁ T₂) (max (max TA TK) 4), le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro T hT σ hσ1 hσ2
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTTA : TA ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hT
  have hTTK : TK ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hT
  have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT)
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hTA' : Real.log T ^ 2 ≤ T ^ (3 / 8 : ℝ) := by
    have h := hTA T hTTA
    rw [one_mul] at h
    exact le_trans (pow_le_pow_left₀ hlog0 (by linarith) 2) h
  have hZT : T ^ dhSmoothExp ε * Real.log T ^ 2 ≤ T := by
    calc T ^ dhSmoothExp ε * Real.log T ^ 2 ≤ T ^ (5 / 8 : ℝ) * T ^ (3 / 8 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 hy1) hTA' (by positivity)
            (Real.rpow_nonneg hT0.le _)
      _ = T := by rw [← Real.rpow_add hT0]; norm_num
  have hLT : K₀ * Real.log T ≤ T := by
    have h := hTK T hTTK
    simp only [pow_one, Real.rpow_one] at h
    nlinarith
  set Zc := pDetCut (dhSmoothExp ε) T with hZc
  have hZle : (Zc : ℝ) ≤ T ^ dhSmoothExp ε * Real.log T ^ 2 := Nat.floor_le (by positivity)
  have hZ2 : 2 ≤ Zc := by
    have hTy : (2 : ℝ) ≤ T ^ dhSmoothExp ε := by
      calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hT4 (by norm_num)
        _ ≤ T ^ dhSmoothExp ε :=
            Real.rpow_le_rpow_of_exponent_le hT1 (by unfold dhSmoothExp; linarith)
    have h2 : (2 : ℝ) ≤ T ^ dhSmoothExp ε * Real.log T ^ 2 :=
      le_trans hTy (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    rw [hZc, pDetCut]
    exact Nat.le_floor (by exact_mod_cast h2)
  have hZTR : (Zc : ℝ) ≤ T := le_trans hZle hZT
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log T := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = dhLogExponent ε := ⟨_, rfl⟩
  rw [← hℓ, ← hE]
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hX1 : 1 ≤ pDetMoll (dhMollExp ε) T := one_le_pDetMoll hδ0.le hT1
  have hY1 : 1 ≤ pDetSmooth (dhSmoothExp ε) T := one_le_pDetSmooth hy0.le hT1
  obtain ⟨W, hWT, hWsep, hcase, hcount⟩ :=
    exists_separated_gDet_class (hdich T hTT₁) hc₀ hX1 hY1 hZ2 hT0 hσ1 (by linarith)
  have hpre := gDet_prefactor_le hT1 hZ2 hZTR
  rw [← hℓ] at hpre
  have hM1 : 1 ≤ dhPowerBound ε := by
    have h32 : (32 : ℝ) ≤ 32 / ε := by rw [le_div_iff₀ hε]; linarith
    have hc : (32 / ε : ℝ) ≤ dhPowerBound ε := Nat.le_ceil _
    have : (1 : ℝ) ≤ dhPowerBound ε := by linarith
    exact_mod_cast this
  have hE8 : 8 ≤ E := by
    rw [hE, dhLogExponent]
    have := Nat.one_le_two_pow (n := 4 * dhPowerBound ε)
    omega
  have hWcard : (W.card : ℝ) ≤ (dhCountConstant ε + K₂) * ℓ ^ E *
      T ^ ((2 + ε) * (1 - σ)) := by
    have hℓ8 : ℓ ^ 8 ≤ ℓ ^ E := pow_le_pow_right₀ hℓ1 hE8
    rcases hcase with h2 | ⟨j, hj, i, hi, m, hm, h1⟩
    · have hc := card_typeTwo_le_dh hK₀ hc₀ hD₄ hε (by linarith) hLT hσ2
        (h4 (by linarith)) hWT hWsep h2
      rw [← hℓ, ← hK₂] at hc
      calc (W.card : ℝ) ≤ K₂ * ℓ ^ 8 * T ^ ((2 + ε) * (1 - σ)) := hc
        _ ≤ K₂ * ℓ ^ E * T ^ ((2 + ε) * (1 - σ)) := by gcongr
        _ ≤ (dhCountConstant ε + K₂) * ℓ ^ E * T ^ ((2 + ε) * (1 - σ)) := by
            gcongr
            linarith
    · have hΛ0 : 0 ≤ gDetLog Zc :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Zc))
      have hσσ' : σ ≤ σ + m / gDetLog Zc :=
        le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hΛ0)
      have hc := hcls T hTT₂ σ hσ1 hσ2 j i _ hσσ' W hWT hWsep h1
      rw [← hℓ, ← hE] at hc
      calc (W.card : ℝ) ≤ dhCountConstant ε * ℓ ^ E * T ^ ((2 + ε) * (1 - σ)) := hc
        _ ≤ (dhCountConstant ε + K₂) * ℓ ^ E * T ^ ((2 + ε) * (1 - σ)) := by
            gcongr
            linarith
  calc ((zeroHeightBox σ T).ncard : ℝ)
      ≤ ((gDetBlockCount Zc * (gDetBlockCount Zc + 8) * (⌊gDetLog Zc⌋₊ + 1) + 1 : ℕ) : ℝ) *
          densityWindowCapacity T * W.card := hcount
    _ ≤ (F₀ * ℓ ^ 4) * ((dhCountConstant ε + K₂) * ℓ ^ E * T ^ ((2 + ε) * (1 - σ))) :=
        mul_le_mul hpre hWcard (Nat.cast_nonneg _) (by positivity)
    _ = F₀ * (dhCountConstant ε + K₂) * ℓ ^ (E + 4) * T ^ ((2 + ε) * (1 - σ)) := by
        rw [pow_add]
        ring

end RHTower

end
