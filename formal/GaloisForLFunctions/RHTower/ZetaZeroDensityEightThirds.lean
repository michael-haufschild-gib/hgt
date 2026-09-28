import GaloisForLFunctions.RHTower.ZetaZeroClassCardBound

/-!
# The zero-density estimate with exponent `8/3 + ε`

For every `ε ∈ (0, 1]` there is `T₀` such that for all `T ≥ T₀` and `σ ∈ [1/2, 1]`,

`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ C (1 + log T)^{E + 4} T^{(8/3 + ε)(1 - σ)}`,

counting zeros with multiplicity, with the explicit constants `C` and `E` of
`exists_class_card_le`.  The box count is the number of detection classes times the unit-window
capacity times the separated class count (`exists_separated_class_of_zeroHeightBox`).  All three
factors are logarithmic except the last.
-/

namespace RHTower

noncomputable section

open Complex Finset Filter RHTower.Sieve

/-- The logarithmic size of the detection length: `⌊log(Ny)⌋ + 1 ≤ 3(1 + log T)`. -/
theorem floor_log_add_one_le {T : ℝ} (hT : (2 : ℝ) ^ (120 : ℕ) ≤ T) :
    ((⌊Real.log ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ)⌋₊ + 1 : ℕ) : ℝ)
      ≤ 3 * (1 + Real.log T) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hT1 : 1 ≤ T := le_trans (one_le_pow₀ (by norm_num)) hT
  have hup := densityParameters_upper hT
  obtain ⟨_, _, _, _, hNy⟩ := densityParameters hT
  have hpos : (0 : ℝ) < ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < densityBlockLength T * densityMollifierLength T)
  have hlog : Real.log ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ)
      ≤ Real.log 2 + (249 / 200) * Real.log T := by
    have := Real.log_le_log hpos hup
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hT0 _).ne', Real.log_rpow hT0] at this
    exact this
  have hl2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hfl := Nat.floor_le (Real.log_nonneg (by exact_mod_cast
    (by omega : 1 ≤ densityBlockLength T * densityMollifierLength T) :
      (1 : ℝ) ≤ ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ)))
  rw [Nat.cast_add, Nat.cast_one]
  linarith

/-- The unit-window capacity is logarithmic. -/
theorem densityWindowCapacity_le {T : ℝ} (hT : 1 ≤ T) :
    densityWindowCapacity T ≤ 16 * (|xiLineTwoLogDerivConstant| + 3) * (1 + Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have h1 : Real.log (2 * T + 5) ≤ 3 + Real.log T := by
    have h := Real.log_le_log (by linarith) (show 2 * T + 5 ≤ 7 * T by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne'] at h
    have h7 : Real.log 7 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have he : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h2]
      nlinarith
    linarith
  unfold densityWindowCapacity
  have hC := abs_nonneg xiLineTwoLogDerivConstant
  nlinarith

/-- The constant of the density estimate. -/
def zeroDensityConstant : ℝ :=
  3 * 11 * 3 * (16 * (|xiLineTwoLogDerivConstant| + 3)) * classCountConstant

/-- **The zero-density estimate with exponent `8/3 + ε`.** -/
theorem exists_zeroHeightBox_ncard_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ zeroDensityConstant * (1 + Real.log T) ^ (classCountLogExponent + 4)
          * T ^ ((8 / 3 + ε) * (1 - σ)) := by
  obtain ⟨T₁, hT₁⟩ := exists_class_card_le hε hε1
  refine ⟨max T₁ ((2 : ℝ) ^ (400 : ℕ)), ?_⟩
  intro T hT σ hσ1 hσ2
  have hT400 : (2 : ℝ) ^ (400 : ℕ) ≤ T := le_trans (le_max_right _ _) hT
  have hT120 : (2 : ℝ) ^ (120 : ℕ) ≤ T :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hT400
  have hT1 : (1 : ℝ) ≤ T := le_trans (one_le_pow₀ (by norm_num)) hT400
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  -- the logarithmic factors, before any huge exponent enters the context
  set LT : ℝ := 1 + Real.log T with hLT
  have hLT1 : 1 ≤ LT := by rw [hLT]; linarith [Real.log_nonneg hT1]
  have hJ := detBlockCount_le_log hT120
  have hJ8 : (detBlockCount (densityBlockLength T) (densityMollifierLength T) : ℝ) + 8
      ≤ 11 * LT := by linarith
  have hM := floor_log_add_one_le hT120
  have hCap := densityWindowCapacity_le hT1
  have hCap0 : 0 ≤ 16 * (|xiLineTwoLogDerivConstant| + 3) := by
    have := abs_nonneg xiLineTwoLogDerivConstant
    positivity
  have hCap00 : 0 ≤ densityWindowCapacity T := by
    unfold densityWindowCapacity
    have := abs_nonneg xiLineTwoLogDerivConstant
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T + 5 from
      le_add_of_nonneg_of_le (by positivity) (by norm_num))
    positivity
  obtain ⟨j, hj, i, hi, m, hm, W, hWT, hWsep, hWbig, hcount⟩ :=
    exists_separated_class_of_zeroHeightBox hT120 hσ1
  have hΛ0 : 0 ≤ Real.log ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ) :=
    Real.log_nonneg (by
      obtain ⟨_, _, _, _, hNy⟩ := densityParameters hT120
      exact_mod_cast (by omega : 1 ≤ densityBlockLength T * densityMollifierLength T))
  have hσσ' : σ ≤ σ + m / Real.log ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ) :=
    le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hΛ0)
  have hW := hT₁ T (le_trans (le_max_left _ _) hT) σ hσ1 hσ2 j i _ hσσ' W hWT hWsep hWbig
  set E : ℕ := classCountLogExponent with hE
  set J : ℕ := detBlockCount (densityBlockLength T) (densityMollifierLength T) with hJdef
  set M : ℕ := ⌊Real.log ((densityBlockLength T * densityMollifierLength T : ℕ) : ℝ)⌋₊ + 1
    with hMdef
  have hcountR : ((zeroHeightBox σ T).ncard : ℝ)
      ≤ ((J : ℝ) * ((J : ℝ) + 8) * (M : ℝ)) * densityWindowCapacity T * W.card := by
    have h := hcount
    push_cast at h
    exact h
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hfac : (J : ℝ) * ((J : ℝ) + 8) * (M : ℝ) ≤ (3 * LT) * (11 * LT) * (3 * LT) :=
    mul_le_mul (mul_le_mul hJ hJ8 (by positivity) (by positivity)) hM (Nat.cast_nonneg _)
      (by positivity)
  have hCapT : densityWindowCapacity T ≤ 16 * (|xiLineTwoLogDerivConstant| + 3) * LT := hCap
  have hWc0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hTA : 0 ≤ T ^ ((8 / 3 + ε) * (1 - σ)) := Real.rpow_nonneg hT0.le _
  have hLTE : 0 ≤ LT ^ E := pow_nonneg (by linarith) _
  have hcc : 0 ≤ classCountConstant := by
    unfold classCountConstant
    exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
  calc ((zeroHeightBox σ T).ncard : ℝ)
      ≤ ((J : ℝ) * ((J : ℝ) + 8) * (M : ℝ)) * densityWindowCapacity T * W.card := hcountR
    _ ≤ ((3 * LT) * (11 * LT) * (3 * LT)) * (16 * (|xiLineTwoLogDerivConstant| + 3) * LT)
          * (classCountConstant * LT ^ E * T ^ ((8 / 3 + ε) * (1 - σ))) :=
        mul_le_mul (mul_le_mul hfac hCapT hCap00 (by positivity)) hW hWc0 (by positivity)
    _ = zeroDensityConstant * (LT ^ 4 * LT ^ E) * T ^ ((8 / 3 + ε) * (1 - σ)) := by
        unfold zeroDensityConstant
        ring
    _ = zeroDensityConstant * LT ^ (E + 4) * T ^ ((8 / 3 + ε) * (1 - σ)) := by
        rw [← pow_add, add_comm 4 E]

end

end RHTower
