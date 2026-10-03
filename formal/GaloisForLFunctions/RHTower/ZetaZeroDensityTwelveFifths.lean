import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorClassCount
import GaloisForLFunctions.RHTower.ZetaZeroDensityThirtyThreeThirteenths

/-!
# Huxley's zero-density estimate: exponent `12/5 + ε`

For every `0 < ε ≤ 1` there are `D ≥ 0` and `T₀` such that for all `T ≥ T₀` and `σ ∈ [1/2, 1]`,

`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^{E+4} T^{(12/5 + ε)(1 - σ)}`,

counting zeros with multiplicity, `E = expDetCountLogExponent`.

* For `σ < 7/12` the box has `O(T log T)` zeros (the global rectangle count through the fibre
  bound), and `(12/5)(1 - σ) ≥ 1`.
* For `σ ≥ 7/12` the separated detector class (`exists_separated_expDet_class`) is either a Type I
  class, counted by `exists_expDet_class_card_le`, or a Type II set `W`, counted by the critical
  fourth moment: `#W ≪ (log T)⁸ T X⁴ Y^{2-4σ} ≤ (log T)⁸ T^{(35-36σ)/15} ≤ (log T)⁸ T^{(12/5)(1-σ)}`
  with `X = T^{1/30}`, `Y = T^{3/5}`.

The class count and the local capacity contribute `(1 + log T)⁴`.
-/

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve

/-- The box holds `O(T log T)` zero copies. -/
theorem exists_ncard_zeroHeightBox_le_global :
    ∃ C : ℝ, 0 < C ∧ ∀ {σ T : ℝ}, 1 / 2 ≤ σ → 1 ≤ T →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ C * (2 * T + 4) * Real.log (2 * T + 5) := by
  obtain ⟨C, hC, hglob⟩ := exists_zetaResidueUnitClosedRectangleMultiplicity_le_global
  refine ⟨C, hC, fun {σ T} hσ hT => ?_⟩
  have h1 := ncard_zeroHeightBox_le_zetaLittlewoodZeroCountAbove (σ := σ) (T := T)
    (c := 1 / 4) (H := 2 * T) (by norm_num) (by linarith) (by linarith) le_rfl
  refine le_trans h1 ?_
  have h2 := hglob (c := 1 / 4) (T := 2 * T) (by norm_num) (by norm_num) (by linarith)
  refine le_trans ?_ h2
  unfold zetaLittlewoodZeroCountAbove
  have hcast : (((4 : ℝ) : ℂ) + ((2 * T : ℝ) : ℂ) * I) = ((4 : ℂ) + ((2 * T : ℝ) : ℂ) * I) := by
    norm_num
  rw [hcast]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.cast_nonneg _)

/-- **The Type II count in the density exponent.** -/
theorem card_typeTwo_le_twelve_fifths {K₀ c₀ D₄ T σ : ℝ} (hK₀ : 0 ≤ K₀) (hc₀ : 0 < c₀)
    (hD₄ : 0 ≤ D₄) (hT2 : 2 ≤ T) (hLT : K₀ * Real.log T ≤ T)
    (h4 : ∫ u in (-(3 * T))..(3 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 4 ≤
      D₄ * T * (1 + Real.log T) ^ 4)
    {W : Finset ℝ} (hW : ∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T)
    (hsep : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|)
    (hbig : ∀ t ∈ W, c₀ * expDetSmooth T ^ (σ - 1 / 2) / expDetMoll T ≤
      ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖) :
    (W.card : ℝ) ≤ (8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4) * (1 + Real.log T) ^ 8 *
      T ^ ((12 / 5) * (1 - σ)) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (expDetMoll T : ℝ) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = expDetSmooth T := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = K₀ * Real.log T := ⟨_, rfl⟩
  rw [← hX, ← hY, ← hL] at hbig
  rw [← hL] at hLT
  have hX1 : 1 ≤ X := by rw [hX]; exact_mod_cast one_le_expDetMoll hT1
  have hXle : X ≤ T ^ (1 / 30 : ℝ) := by rw [hX]; exact expDetMoll_le hT1
  have hY1 : 1 ≤ Y := by rw [hY]; exact one_le_expDetSmooth hT1
  have hYT : Y = T ^ (3 / 5 : ℝ) := hY
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = c₀ * Y ^ (σ - 1 / 2) / X := ⟨_, rfl⟩
  rw [← hV] at hbig
  have hYp : 0 < Y ^ (σ - 1 / 2) := Real.rpow_pos_of_pos hY0 _
  have hV0 : 0 < V := by rw [hV]; positivity
  have hcount := card_mul_pow_four_le_typeTwo hL0 hLT hW hsep hV0.le hbig
  -- the polylog prefactor
  have hl1 : 0 ≤ 1 + Real.log T := by linarith
  have hLlog : L ≤ K₀ * (1 + Real.log T) := by rw [hL]; nlinarith
  have hpre : (2 * L) ^ 3 * (2 * L + 1) ≤ 8 * K₀ ^ 3 * (2 * K₀ + 1) * (1 + Real.log T) ^ 4 := by
    have h1 : (2 * L) ^ 3 ≤ (2 * (K₀ * (1 + Real.log T))) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    have h2 : 2 * L + 1 ≤ (2 * K₀ + 1) * (1 + Real.log T) := by nlinarith
    calc (2 * L) ^ 3 * (2 * L + 1) ≤ (2 * (K₀ * (1 + Real.log T))) ^ 3 *
          ((2 * K₀ + 1) * (1 + Real.log T)) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 8 * K₀ ^ 3 * (2 * K₀ + 1) * (1 + Real.log T) ^ 4 := by ring
  -- the height exponent: `T X⁴ ≤ T^{(12/5)(1-σ)} Y^{4σ-2}`
  have hX4 : X ^ 4 ≤ T ^ (2 / 15 : ℝ) := by
    calc X ^ 4 ≤ (T ^ (1 / 30 : ℝ)) ^ 4 := pow_le_pow_left₀ (by linarith) hXle 4
      _ = T ^ (2 / 15 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hTY : T ^ ((12 / 5) * (1 - σ)) * (Y ^ (σ - 1 / 2)) ^ 4 = T ^ (6 / 5 : ℝ) := by
    rw [hYT, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le, ← Real.rpow_mul hT0.le,
      ← Real.rpow_add hT0]
    congr 1
    push_cast
    ring
  have hheight : T * X ^ 4 ≤ T ^ ((12 / 5) * (1 - σ)) * (Y ^ (σ - 1 / 2)) ^ 4 := by
    rw [hTY]
    calc T * X ^ 4 ≤ T * T ^ (2 / 15 : ℝ) := mul_le_mul_of_nonneg_left hX4 hT0.le
      _ = T ^ (17 / 15 : ℝ) := by
          rw [← Real.rpow_one_add' hT0.le (by norm_num)]
          norm_num
      _ ≤ T ^ (6 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  -- assemble
  have hV4 : V ^ 4 = c₀ ^ 4 * (Y ^ (σ - 1 / 2)) ^ 4 / X ^ 4 := by rw [hV]; ring
  have hX0 : 0 < X := by linarith
  have hfinal : (W.card : ℝ) * V ^ 4 ≤
      (8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4) * (1 + Real.log T) ^ 8 *
        T ^ ((12 / 5) * (1 - σ)) * V ^ 4 := by
    refine le_trans hcount (le_trans (mul_le_mul hpre h4 (by
      exact intervalIntegral.integral_nonneg (by linarith) fun u _ => by positivity)
      (by positivity)) ?_)
    rw [hV4]
    have hK : 0 ≤ 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ := by positivity
    have e : 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4 * (1 + Real.log T) ^ 8 *
        T ^ ((12 / 5) * (1 - σ)) * (c₀ ^ 4 * (Y ^ (σ - 1 / 2)) ^ 4 / X ^ 4) =
        8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ * (1 + Real.log T) ^ 8 *
          (T ^ ((12 / 5) * (1 - σ)) * (Y ^ (σ - 1 / 2)) ^ 4) / X ^ 4 := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    calc 8 * K₀ ^ 3 * (2 * K₀ + 1) * (1 + Real.log T) ^ 4 * (D₄ * T * (1 + Real.log T) ^ 4) *
          X ^ 4
        = 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ * (1 + Real.log T) ^ 8 * (T * X ^ 4) := by ring
      _ ≤ 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ * (1 + Real.log T) ^ 8 *
            (T ^ ((12 / 5) * (1 - σ)) * (Y ^ (σ - 1 / 2)) ^ 4) :=
          mul_le_mul_of_nonneg_left hheight (by positivity)
  exact le_of_mul_le_mul_right hfinal (by positivity)

/-- The class-count prefactor `(J(J+8)(⌊Λ⌋+1) + 1)·16(|C| + log(2T+5))` is `O((1 + log T)⁴)`. -/
theorem expDet_prefactor_le {T : ℝ} (hT4 : 4 ≤ T) (hZT : T ^ (3 / 5 : ℝ) * Real.log T ^ 2 ≤ T) :
    ((expDetBlockCount T * (expDetBlockCount T + 8) * (⌊expDetLog T⌋₊ + 1) + 1 : ℕ) : ℝ) *
        densityWindowCapacity T ≤
      21 * (16 * (|xiLineTwoLogDerivConstant| + 3)) * (1 + Real.log T) ^ 4 := by
  have hT1 : 1 ≤ T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hJ := expDetBlockCount_le_log hT4 hZT
  have hZ := two_le_expDetCut hT4
  have hΛ : expDetLog T ≤ Real.log T := by
    unfold expDetLog
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < expDetCut T))
      (le_trans (expDetCut_le hT1) hZT)
  have hΛ0 : 0 ≤ expDetLog T := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ expDetCut T))
  have hM : ((⌊expDetLog T⌋₊ + 1 : ℕ) : ℝ) ≤ 1 + Real.log T := by
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
  have hJ0 : (0 : ℝ) ≤ expDetBlockCount T := Nat.cast_nonneg _
  have hcount : ((expDetBlockCount T * (expDetBlockCount T + 8) * (⌊expDetLog T⌋₊ + 1) + 1 : ℕ) :
      ℝ) ≤ 21 * ℓ ^ 3 := by
    push_cast
    push_cast at hM
    have h1 : (expDetBlockCount T : ℝ) * ((expDetBlockCount T : ℝ) + 8) ≤ 2 * ℓ * (10 * ℓ) :=
      mul_le_mul hJ (by linarith) (by positivity) (by positivity)
    have h2 : (expDetBlockCount T : ℝ) * ((expDetBlockCount T : ℝ) + 8) *
        ((⌊expDetLog T⌋₊ : ℝ) + 1) ≤ 2 * ℓ * (10 * ℓ) * ℓ :=
      mul_le_mul h1 hM (by positivity) (by positivity)
    have h3 : (1 : ℝ) ≤ ℓ ^ 3 := one_le_pow₀ hℓ1
    nlinarith
  calc ((expDetBlockCount T * (expDetBlockCount T + 8) * (⌊expDetLog T⌋₊ + 1) + 1 : ℕ) : ℝ) *
        densityWindowCapacity T
      ≤ (21 * ℓ ^ 3) * (16 * (|xiLineTwoLogDerivConstant| + 3) * ℓ) :=
        mul_le_mul hcount hcap hcap0 (by positivity)
    _ = 21 * (16 * (|xiLineTwoLogDerivConstant| + 3)) * ℓ ^ 4 := by ring

/-- **Huxley's zero-density estimate with exponent `12/5 + ε`.** -/
theorem exists_zeroHeightBox_ncard_le_twelve_fifths {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D * (1 + Real.log T) ^ (expDetCountLogExponent + 4) * T ^ ((12 / 5 + ε) * (1 - σ)) := by
  obtain ⟨K₀, c₀, T₁, hc₀, hK₀, hT₁, hdich⟩ := exists_expDetector_dichotomy
  obtain ⟨T₂, hcls⟩ := exists_expDet_class_card_le hε hε1
  obtain ⟨D₄, hD₄, h4⟩ := exists_integral_norm_riemannZeta_half_pow_four_le
  obtain ⟨Cg, hCg, hglob⟩ := exists_ncard_zeroHeightBox_le_global
  obtain ⟨TA, hTA⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 2 (c := 2 / 5) (by norm_num) 1)
  obtain ⟨TK, hTK⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 1 (c := 1) (by norm_num) K₀)
  set F₀ : ℝ := 21 * (16 * (|xiLineTwoLogDerivConstant| + 3)) with hF₀
  set K₂ : ℝ := 8 * K₀ ^ 3 * (2 * K₀ + 1) * D₄ / c₀ ^ 4 with hK₂
  have hF₀0 : 0 ≤ F₀ := by rw [hF₀]; have := abs_nonneg xiLineTwoLogDerivConstant; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hCC0 : 0 ≤ expDetCountConstant := by unfold expDetCountConstant; positivity
  refine ⟨18 * Cg + F₀ * (expDetCountConstant + K₂), by positivity,
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
  have hTA' : Real.log T ^ 2 ≤ T ^ (2 / 5 : ℝ) := by
    have h := hTA T hTTA
    rw [one_mul] at h
    exact le_trans (pow_le_pow_left₀ hlog0 (by linarith) 2) h
  have hZT : T ^ (3 / 5 : ℝ) * Real.log T ^ 2 ≤ T := by
    calc T ^ (3 / 5 : ℝ) * Real.log T ^ 2 ≤ T ^ (3 / 5 : ℝ) * T ^ (2 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_left hTA' (Real.rpow_nonneg hT0.le _)
      _ = T := by rw [← Real.rpow_add hT0]; norm_num
  have hLT : K₀ * Real.log T ≤ T := by
    have h := hTK T hTTK
    simp only [pow_one, Real.rpow_one] at h
    nlinarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log T := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = expDetCountLogExponent := ⟨_, rfl⟩
  rw [← hℓ, ← hE]
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hE8 : 8 ≤ E := by rw [hE]; unfold expDetCountLogExponent; norm_num
  have hTA0 : 0 ≤ T ^ ((12 / 5 + ε) * (1 - σ)) := Real.rpow_nonneg hT0.le _
  have hℓE : ℓ ^ 4 ≤ ℓ ^ (E + 4) := pow_le_pow_right₀ hℓ1 (by omega)
  have hℓ0 : 0 ≤ ℓ ^ (E + 4) := pow_nonneg (by linarith) _
  by_cases hσ7 : σ < 7 / 12
  · -- the trivial range
    have h1 := hglob hσ1 hT1
    have hlog25 : Real.log (2 * T + 5) ≤ 3 * ℓ := by
      have h := Real.log_le_log (by linarith) (show 2 * T + 5 ≤ 4 * T by linarith)
      rw [Real.log_mul (by norm_num) hT0.ne'] at h
      have h4 : Real.log 4 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
        have h2 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith [Real.log_two_lt_d9]
      rw [hℓ]
      linarith
    have hTpow : T ≤ T ^ ((12 / 5 + ε) * (1 - σ)) := by
      calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
        _ ≤ T ^ ((12 / 5 + ε) * (1 - σ)) := Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
    have hℓ1E : ℓ ≤ ℓ ^ (E + 4) := by
      calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
        _ ≤ ℓ ^ (E + 4) := pow_le_pow_right₀ hℓ1 (by omega)
    calc ((zeroHeightBox σ T).ncard : ℝ) ≤ Cg * (2 * T + 4) * Real.log (2 * T + 5) := h1
      _ ≤ Cg * (3 * T) * (3 * ℓ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCg.le) hlog25
            (Real.log_nonneg (by linarith)) (by positivity)
      _ = 9 * Cg * (ℓ * T) := by ring
      _ ≤ 9 * Cg * (ℓ ^ (E + 4) * T ^ ((12 / 5 + ε) * (1 - σ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hℓ1E hTpow hT0.le hℓ0) (by positivity)
      _ ≤ (18 * Cg + F₀ * (expDetCountConstant + K₂)) * ℓ ^ (E + 4) *
            T ^ ((12 / 5 + ε) * (1 - σ)) := by
          have : 0 ≤ F₀ * (expDetCountConstant + K₂) := by positivity
          have h' : 0 ≤ ℓ ^ (E + 4) * T ^ ((12 / 5 + ε) * (1 - σ)) := by positivity
          nlinarith
  · push Not at hσ7
    obtain ⟨W, hWT, hWsep, hcase, hcount⟩ :=
      exists_separated_expDet_class hdich hc₀ hTT₁ hT4 hσ7
    have hpre := expDet_prefactor_le hT4 hZT
    rw [← hℓ] at hpre
    have hWcard : (W.card : ℝ) ≤ (expDetCountConstant + K₂) * ℓ ^ E *
        T ^ ((12 / 5 + ε) * (1 - σ)) := by
      have hℓ8 : ℓ ^ 8 ≤ ℓ ^ E := pow_le_pow_right₀ hℓ1 hE8
      rcases hcase with h2 | ⟨j, hj, i, hi, m, hm, h1⟩
      · have hc := card_typeTwo_le_twelve_fifths hK₀ hc₀ hD₄ (by linarith) hLT
          (h4 (by linarith)) hWT hWsep h2
        rw [← hℓ, ← hK₂] at hc
        have hTe : T ^ ((12 / 5) * (1 - σ)) ≤ T ^ ((12 / 5 + ε) * (1 - σ)) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
        calc (W.card : ℝ) ≤ K₂ * ℓ ^ 8 * T ^ ((12 / 5) * (1 - σ)) := hc
          _ ≤ K₂ * ℓ ^ E * T ^ ((12 / 5 + ε) * (1 - σ)) := by gcongr
          _ ≤ (expDetCountConstant + K₂) * ℓ ^ E * T ^ ((12 / 5 + ε) * (1 - σ)) := by
              gcongr
              linarith
      · have hΛ0 : 0 ≤ expDetLog T :=
          Real.log_nonneg (by exact_mod_cast (by have := two_le_expDetCut hT4; omega :
            1 ≤ expDetCut T))
        have hσσ' : σ ≤ σ + m / expDetLog T :=
          le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hΛ0)
        have hc := hcls T hTT₂ σ hσ1 hσ2 j i _ hσσ' W hWT hWsep h1
        rw [← hℓ, ← hE] at hc
        calc (W.card : ℝ) ≤ expDetCountConstant * ℓ ^ E * T ^ ((12 / 5 + ε) * (1 - σ)) := hc
          _ ≤ (expDetCountConstant + K₂) * ℓ ^ E * T ^ ((12 / 5 + ε) * (1 - σ)) := by
              gcongr
              linarith
    calc ((zeroHeightBox σ T).ncard : ℝ)
        ≤ ((expDetBlockCount T * (expDetBlockCount T + 8) * (⌊expDetLog T⌋₊ + 1) + 1 : ℕ) : ℝ) *
            densityWindowCapacity T * W.card := hcount
      _ ≤ (F₀ * ℓ ^ 4) * ((expDetCountConstant + K₂) * ℓ ^ E *
            T ^ ((12 / 5 + ε) * (1 - σ))) :=
          mul_le_mul hpre hWcard (Nat.cast_nonneg _) (by positivity)
      _ = F₀ * (expDetCountConstant + K₂) * (ℓ ^ 4 * ℓ ^ E) * T ^ ((12 / 5 + ε) * (1 - σ)) := by
          ring
      _ = F₀ * (expDetCountConstant + K₂) * ℓ ^ (E + 4) * T ^ ((12 / 5 + ε) * (1 - σ)) := by
          rw [← pow_add, add_comm 4 E]
      _ ≤ (18 * Cg + F₀ * (expDetCountConstant + K₂)) * ℓ ^ (E + 4) *
            T ^ ((12 / 5 + ε) * (1 - σ)) := by
          gcongr
          linarith

end RHTower
