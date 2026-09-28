import GaloisForLFunctions.RHTower.ZetaZeroClassExponentBookkeeping
import GaloisForLFunctions.RHTower.ZetaZeroClassCardArithmetic

/-!
# The count of a detection class: exponent `8/3 + ε`

Let `ε ∈ (0, 1]`.  For all large `T`, every `σ ∈ [1/2, 1]` and every class `(j, i, σ')` with
`σ ≤ σ'`, a `1`-separated set `W ⊆ [T, 2T]` on which the class polynomial is at least `1/(12J)` has

`#W ≤ C (1 + log T)^E T^{(8/3 + ε)(1 - σ)}`,

with `E = 3·2^{136} + 300` and `C = 2^{300} 36^E`.  The class polynomial is raised to the power `ℓ ≤ 34`
that puts `X = (2^j)^ℓ` in `[T^{2/3}, T^{4/3}]`.  Then:

* for `σ ≤ 3/4 + ε/32` the mean value count gives `T X^{1-2σ} + X^{2-2σ}`, and
  `T X^{1-2σ} ≤ T^{1 + (2/3)(1-2σ)} ≤ T^{(8/3+ε)(1-σ)}`;
* for `σ > 3/4 + ε/32` Huxley's threshold holds, because `X^{3/2-2σ} ≤ T^{-ε/24}` beats every
  logarithmic factor, and the Huxley count gives `T X^{4-6σ} + X^{2-2σ} ≤ 2T^{(8/3)(1-σ)}`.
-/

namespace RHTower

noncomputable section

open Complex Finset Filter RHTower.Sieve

/-- The logarithmic exponent of the class count. -/
def classCountLogExponent : ℕ := 3 * 2 ^ 136 + 300

/-- The constant of the class count. -/
def classCountConstant : ℝ := 2 ^ 300 * 36 ^ classCountLogExponent

/-- The facts about the logarithmic unit `Q` and `P = Q^{2^{136}}` that involve huge exponents,
kept in one structure so that linear arithmetic never normalizes them. -/
structure ClassBigFacts (Q P T ε : ℝ) : Prop where
  threshold : 3 * 34 ^ 2 * 1537 * 2 ^ 51 * (Q ^ 68 * P) ≤ T ^ (ε / 24)
  meanValue : Q ^ 68 * Q * Q * P ≤ Q ^ classCountLogExponent
  cube : Q ^ 136 * P ^ 3 ≤ Q ^ (136 + 3 * 2 ^ 136)
  single : P ≤ Q ^ (136 + 3 * 2 ^ 136)
  huxley : Q ^ 68 * Q ^ (136 + 3 * 2 ^ 136) * Q ≤ Q ^ classCountLogExponent
  split : Q ^ classCountLogExponent
    = 36 ^ classCountLogExponent * (1 + Real.log T) ^ classCountLogExponent

/-- The huge-exponent facts hold at every height beyond the threshold `TH` of
`eventually_const_mul_polylog_le_rpow`. -/
theorem exists_classBigFacts {ε : ℝ} (hε : 0 < ε) :
    ∃ TH : ℝ, ∀ T : ℝ, TH ≤ T → 1 ≤ T →
      ClassBigFacts (36 * (1 + Real.log T)) ((36 * (1 + Real.log T)) ^ (2 ^ 136)) T ε := by
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℕ, e₀ = 68 + 2 ^ 136 := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 3 * 34 ^ 2 * 1537 * 2 ^ 51 * 36 ^ e₀ := ⟨_, rfl⟩
  obtain ⟨TH, hTH⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow e₀ (c := ε / 24) (by positivity) c₀)
  refine ⟨TH, fun T hT hT1 => ?_⟩
  have hQ1 : 1 ≤ 36 * (1 + Real.log T) := by
    have := Real.log_nonneg hT1
    linarith
  have hQpow : ∀ a b : ℕ, a ≤ b → (36 * (1 + Real.log T)) ^ a ≤ (36 * (1 + Real.log T)) ^ b :=
    fun a b hab => pow_le_pow_right₀ hQ1 hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← pow_add, ← he₀, mul_pow, ← mul_assoc, ← hc₀]
    exact hTH T hT
  · rw [← pow_succ, ← pow_succ, ← pow_add]
    exact hQpow _ _ (by unfold classCountLogExponent; omega)
  · rw [← pow_mul, ← pow_add, mul_comm (2 ^ 136) 3]
  · exact hQpow _ _ (by omega)
  · rw [← pow_add, ← pow_succ]
    exact hQpow _ _ (by unfold classCountLogExponent; omega)
  · rw [mul_pow]

/-- **The class count.** -/
theorem exists_class_card_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ (j i : ℕ) (σ' : ℝ), σ ≤ σ' → ∀ W : Finset ℝ,
        (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) →
        (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
        (∀ t ∈ W, 1 / (12 * (detBlockCount (densityBlockLength T) (densityMollifierLength T) : ℝ))
          ≤ ‖abscissaTaylorPoly (detDyadicBlock (densityBlockLength T) (densityMollifierLength T) j)
              (detCoeffC (densityBlockLength T) (densityMollifierLength T))
              (Real.log (densityBlockLength T * densityMollifierLength T : ℕ)) i σ' t‖) →
        (W.card : ℝ) ≤ classCountConstant * (1 + Real.log T) ^ classCountLogExponent
          * T ^ ((8 / 3 + ε) * (1 - σ)) := by
  obtain ⟨TH, hTH⟩ := exists_classBigFacts hε
  refine ⟨max ((2 : ℝ) ^ (400 : ℕ)) TH, ?_⟩
  intro T hT σ hσ1 hσ2 j i σ' hσσ' W hW hsep hbig
  have hT400 : (2 : ℝ) ^ (400 : ℕ) ≤ T := le_trans (le_max_left _ _) hT
  have hT120 : (2 : ℝ) ^ (120 : ℕ) ≤ T :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hT400
  have hT1 : (1 : ℝ) ≤ T := le_trans (one_le_pow₀ (by norm_num)) hT400
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  have hBig := hTH T (le_trans (le_max_right _ _) hT) hT1
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 36 * (1 + Real.log T) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Q ^ (2 ^ 136) := ⟨_, rfl⟩
  rw [← hQdef, ← hPdef] at hBig
  have hQlow : 36 * (1 + Real.log T) ≤ Q := hQdef.symm.le
  have hQ1 : 1 ≤ Q := by
    have := Real.log_nonneg hT1
    linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ1
  have hP0 : 0 ≤ P := by rw [hPdef]; exact pow_nonneg hQ0.le _
  set N := densityBlockLength T with hNdef
  set y := densityMollifierLength T with hydef
  set J := detBlockCount N y with hJdef
  have hJpos : (0 : ℝ) < J := by
    rw [hJdef, detBlockCount]
    positivity
  have hJQ : 12 * (J : ℝ) ≤ Q := by
    have := detBlockCount_le_log hT120
    linarith
  set V : ℝ := 1 / (12 * (J : ℝ)) with hVdef
  have hV0 : 0 < V := by positivity
  have hVQ : 1 / Q ≤ V := by
    rw [hVdef]
    exact one_div_le_one_div_of_le (by positivity) hJQ
  rcases W.eq_empty_or_nonempty with hWe | ⟨t₀, ht₀⟩
  · rw [hWe, card_empty, Nat.cast_zero]
    unfold classCountConstant
    have hl : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
      (pow_nonneg hl _)) (Real.rpow_nonneg hT0.le _)
  have hbig' : ∀ t ∈ W, V ≤ ‖dpoly (classCoeff N y (Real.log (N * y : ℕ)) i σ')
      (detDyadicBlock N y j) t‖ := by
    intro t ht
    rw [← abscissaTaylorPoly_eq_dpoly]
    exact hbig t ht
  obtain ⟨hK1, hK2⟩ := block_bounds_of_large hT400 hV0 (hbig' t₀ ht₀)
  obtain ⟨ℓ, hℓ1, hℓ34, hX1, hX2⟩ := exists_pow_mem_two_thirds_four_thirds
      (lt_of_lt_of_le (one_lt_pow₀ one_lt_two (by norm_num)) hT400) hK1 hK2
  obtain ⟨hy1, _, _, _, hNy⟩ := densityParameters hT120
  replace hy1 : 1 ≤ y := hy1
  have hN1 : 1 ≤ N := by
    by_contra h
    have h0 : N = 0 := by omega
    rw [hNdef] at h0
    rw [h0] at hNy
    simp at hNy
  set X : ℝ := (((2 ^ j : ℕ) : ℝ)) ^ ℓ with hXdef
  have hXge1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast Nat.one_le_two_pow)
  have hσ0 : (0 : ℝ) ≤ σ := le_trans (by norm_num) hσ1
  have hmass := classPowerMass_le (σ := σ) hT1 hℓ1 hℓ34 hX2
  rw [← hXdef, ← hQdef, ← hPdef] at hmass
  have hLcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * X := by
    rw [hXdef]
    push_cast
    ring
  have hL34 : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ 2 ^ 34 * X := by
    rw [hLcast]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hℓ34) (by linarith)
  have hL1 : (1 : ℝ) ≤ (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by positivity)
  have hlogL := one_add_log_raised_le hT1 hℓ34 hX2
  rw [← hQdef] at hlogL
  have hVl : 1 / Q ^ 34 ≤ V ^ ℓ := by
    calc 1 / Q ^ 34 ≤ 1 / Q ^ ℓ := one_div_le_one_div_of_le (pow_pos hQ0 _)
          (pow_le_pow_right₀ hQ1 hℓ34)
      _ = (1 / Q) ^ ℓ := by rw [one_div_pow]
      _ ≤ V ^ ℓ := pow_le_pow_left₀ (by positivity) hVQ ℓ
  have hG0 : 0 ≤ classPowerMass j ℓ σ := by unfold classPowerMass; positivity
  clear_value N y J V X
  clear hQdef hPdef
  have hl : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
  by_cases hcase : σ ≤ 3 / 4 + ε / 32
  · have hmvt := card_mul_pow_le_class_mvt (N := N) (y := y) (j := j) (i := i) (ℓ := ℓ)
      (σ := σ) (σ' := σ') (T := T) (V := V) (W := W) hN1 hy1 hℓ1 hσ0 hσσ' hT0.le hV0.le hW hsep
      hbig'
    have hc := class_count_mvt_arith hT1 hX1 hX2 hXge1 hσ1 hcase hε hε1 hQ1 hP0 hL1 hL34 hlogL
      hG0 hmass hVl (Nat.cast_nonneg _) hmvt
    refine le_trans hc ?_
    calc 2 ^ 35 * (2 + 2 ^ 36) * (Q ^ 68 * Q * Q * P) * T ^ ((8 / 3 + ε) * (1 - σ))
        ≤ 2 ^ 35 * (2 + 2 ^ 36) * Q ^ classCountLogExponent * T ^ ((8 / 3 + ε) * (1 - σ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0.le _)
          exact mul_le_mul_of_nonneg_left hBig.meanValue (by norm_num)
      _ = 2 ^ 35 * (2 + 2 ^ 36) * 36 ^ classCountLogExponent
            * (1 + Real.log T) ^ classCountLogExponent * T ^ ((8 / 3 + ε) * (1 - σ)) := by
          rw [hBig.split]
          ring
      _ ≤ classCountConstant * (1 + Real.log T) ^ classCountLogExponent
            * T ^ ((8 / 3 + ε) * (1 - σ)) := by
          unfold classCountConstant
          have hK : (2 : ℝ) ^ 35 * (2 + 2 ^ 36) ≤ 2 ^ 300 := by
            calc (2 : ℝ) ^ 35 * (2 + 2 ^ 36) ≤ 2 ^ 35 * 2 ^ 37 :=
                  mul_le_mul_of_nonneg_left (by norm_num) (by norm_num)
              _ = 2 ^ 72 := by rw [← pow_add]
              _ ≤ 2 ^ 300 := pow_le_pow_right₀ (by norm_num) (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hK (pow_nonneg (by norm_num) _)) (pow_nonneg hl _))
            (Real.rpow_nonneg hT0.le _)
  · push Not at hcase
    have hVlpos : 0 < V ^ ℓ := pow_pos hV0 ℓ
    have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    have hℓR34 : (ℓ : ℝ) ≤ 34 := by exact_mod_cast hℓ34
    obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = ℓ / V ^ ℓ := ⟨_, rfl⟩
    have hU0 : 0 < U := by rw [hUdef]; positivity
    have hU : U ≤ 34 * Q ^ 34 := by
      rw [hUdef, div_le_iff₀ hVlpos]
      have h1 : 1 ≤ Q ^ 34 * V ^ ℓ := by
        have := mul_le_mul_of_nonneg_left hVl (pow_nonneg hQ0.le 34)
        rwa [mul_one_div_cancel (pow_pos hQ0 _).ne'] at this
      nlinarith [pow_pos hQ0 34]
    have hVU : V ^ ℓ / ℓ = 1 / U := by rw [hUdef, one_div_div]
    have hthr := class_huxley_threshold_arith hT1 hX1 hXge1 hcase.le hε hQ1 hP0 hL1 hL34 hmass
      hU0 hU hBig.threshold
    rw [← hVU] at hthr
    have hhux := card_mul_pow_le_class_huxley (N := N) (y := y) (j := j) (i := i) (ℓ := ℓ)
      (σ := σ) (σ' := σ') (T := T) (V := V) (W := W) hN1 hy1 hℓ1 hσ0 hσσ' hT0.le hV0 hW hsep
      hbig' hthr
    rw [hVU] at hhux
    have hc := class_count_huxley_arith hT1 hX1 hX2 hXge1 (by linarith) hσ2 hε hQ1 hQlow hP0
      hBig.cube hBig.single hL1 hL34 hG0 hmass hU0 hU hℓR34 hhux
    refine le_trans hc ?_
    calc classHuxleyConstant * (Q ^ 68 * Q ^ (136 + 3 * 2 ^ 136) * Q)
          * T ^ ((8 / 3 + ε) * (1 - σ))
        ≤ classHuxleyConstant * Q ^ classCountLogExponent * T ^ ((8 / 3 + ε) * (1 - σ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0.le _)
          exact mul_le_mul_of_nonneg_left hBig.huxley (by unfold classHuxleyConstant; norm_num)
      _ = classHuxleyConstant * 36 ^ classCountLogExponent
            * (1 + Real.log T) ^ classCountLogExponent * T ^ ((8 / 3 + ε) * (1 - σ)) := by
          rw [hBig.split]
          ring
      _ ≤ classCountConstant * (1 + Real.log T) ^ classCountLogExponent
            * T ^ ((8 / 3 + ε) * (1 - σ)) := by
          unfold classCountConstant
          have hK : classHuxleyConstant ≤ 2 ^ 300 := by
            have h34 : (34 : ℝ) ≤ 2 ^ 6 := by norm_num
            have h1284 : (1284 : ℝ) ≤ 2 ^ 11 := by norm_num
            have h6 : (6 : ℝ) ≤ 2 ^ 3 := by norm_num
            have h68 : (2 : ℝ) ^ 68 ≤ 2 ^ 182 := pow_le_pow_right₀ (by norm_num) (by norm_num)
            have hin : (1284 : ℝ) ^ 2 * 34 ^ 4 * 2 ^ 136 ≤ 2 ^ 182 := by
              calc (1284 : ℝ) ^ 2 * 34 ^ 4 * 2 ^ 136 ≤ (2 ^ 11) ^ 2 * (2 ^ 6) ^ 4 * 2 ^ 136 := by
                    gcongr
                _ = 2 ^ 182 := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
            calc classHuxleyConstant
                = 34 ^ 3 * 6 * (1284 ^ 2 * 34 ^ 4 * 2 ^ 136 + 2 ^ 68) := rfl
              _ ≤ (2 ^ 6) ^ 3 * 2 ^ 3 * (2 ^ 182 + 2 ^ 182) := by gcongr
              _ = 2 ^ 204 := by
                  rw [← two_mul, ← pow_succ', ← pow_mul, ← pow_add, ← pow_add]
              _ ≤ 2 ^ 300 := pow_le_pow_right₀ (by norm_num) (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hK (pow_nonneg (by norm_num) _)) (pow_nonneg hl _))
            (Real.rpow_nonneg hT0.le _)

end

end RHTower
