import GaloisForLFunctions.RHTower.Sieve.MoebiusMultiRangeWindow

/-!
# Cofactor mean squares on the first-small sets

On the first-small set of the first range the cofactor is paid by the mean value theorem.  On the
first-small set of range `j + 1` it is amplified by a large block of range `j`: with `S` the scale
of the amplifying block, `T` the scale of the current block and `ℓ = ⌈log T/log S⌉`,

`T^{2-2β}·V_S^{-2ℓ}·(mean value factor)·(coincidence energy) ≤ 15(8ℓ+8)^ℓ·S·M²·T^{2α-2β}`,

`V_S = S^{1-α}`, `V_T = T^{1-β}`: the saving is the power `T^{-2(β-α)}` of the gap between the two
threshold exponents.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- **One amplified block pair, in closed form.** -/
theorem amplified_pair_le {S T M W X Bmax cB α β : ℝ} {ℓ : ℕ} (hS : 1 ≤ S) (hT : 1 ≤ T)
    (hM : 0 < M) (hW0 : 0 ≤ W) (hWM : W ≤ M) (hℓ : 1 ≤ ℓ) (hlow : S ^ (ℓ - 1) ≤ T)
    (hhigh : T ≤ S ^ ℓ) (hα : α ≤ 1 / 2) (hX0 : 0 ≤ X) (hX : X ≤ M / T) (hB0 : 0 ≤ Bmax)
    (hB : Bmax ≤ 2 * S) (hc0 : 0 ≤ cB) (hc : cB ≤ 2 * S) :
    T ^ (2 - 2 * β) * ((S ^ (1 - α)) ^ (2 * ℓ))⁻¹
        * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (Bmax ^ ℓ * X))
          * (cB ^ ℓ * X * (cB + ℓ * Bmax) ^ ℓ / S ^ ℓ))
      ≤ 15 * (8 * ℓ + 8 : ℝ) ^ ℓ * S * M ^ 2 * T ^ (2 * α - 2 * β) := by
  have hS0 : 0 < S := by linarith
  have hT0 : 0 < T := by linarith
  have hSl : 0 < S ^ ℓ := pow_pos hS0 ℓ
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  -- `S^ℓ ≤ S·T`
  have hSlT : S ^ ℓ ≤ S * T := by
    have : S ^ ℓ = S * S ^ (ℓ - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; exact mul_le_mul_of_nonneg_left hlow hS0.le
  -- the coincidence energy
  have hE : cB ^ ℓ * X * (cB + ℓ * Bmax) ^ ℓ / S ^ ℓ ≤ (4 * ℓ + 4 : ℝ) ^ ℓ * S ^ ℓ * (M / T) := by
    have h1 : cB ^ ℓ ≤ (2 * S) ^ ℓ := pow_le_pow_left₀ hc0 hc ℓ
    have h2 : (cB + ℓ * Bmax) ^ ℓ ≤ ((2 * ℓ + 2) * S) ^ ℓ := by
      refine pow_le_pow_left₀ (by positivity) ?_ ℓ
      nlinarith
    have hprod : cB ^ ℓ * X * (cB + ℓ * Bmax) ^ ℓ ≤ (2 * S) ^ ℓ * (M / T) * ((2 * ℓ + 2) * S) ^ ℓ := by
      have hMT : 0 ≤ M / T := by positivity
      calc cB ^ ℓ * X * (cB + ℓ * Bmax) ^ ℓ ≤ (2 * S) ^ ℓ * X * ((2 * ℓ + 2) * S) ^ ℓ := by
            gcongr
        _ ≤ (2 * S) ^ ℓ * (M / T) * ((2 * ℓ + 2) * S) ^ ℓ := by gcongr
    rw [div_le_iff₀ hSl]
    calc cB ^ ℓ * X * (cB + ℓ * Bmax) ^ ℓ ≤ (2 * S) ^ ℓ * (M / T) * ((2 * ℓ + 2) * S) ^ ℓ := hprod
      _ = (4 * ℓ + 4 : ℝ) ^ ℓ * S ^ ℓ * (M / T) * S ^ ℓ := by
          rw [mul_pow, mul_pow, show (4 * ℓ + 4 : ℝ) = 2 * (2 * ℓ + 2) by ring, mul_pow]; ring
  -- the mean value factor
  have hF : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (Bmax ^ ℓ * X) ≤ 15 * 2 ^ ℓ * S * M := by
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
    have h1 : Bmax ^ ℓ * X ≤ 2 ^ ℓ * S * M := by
      calc Bmax ^ ℓ * X ≤ (2 * S) ^ ℓ * (M / T) := by
            have := pow_le_pow_left₀ hB0 hB ℓ
            gcongr
        _ = 2 ^ ℓ * (S ^ ℓ / T) * M := by rw [mul_pow]; ring
        _ ≤ 2 ^ ℓ * S * M := by
            gcongr
            rw [div_le_iff₀ hT0]; exact hSlT
    have h2 : (1 : ℝ) ≤ 2 ^ ℓ * S := by
      have : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
      nlinarith
    have hBX0 : 0 ≤ Bmax ^ ℓ * X := by positivity
    have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
    have he' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hSM : M ≤ 2 ^ ℓ * S * M := by nlinarith
    have t1 : 5 * Real.pi / 2 * W ≤ 7.875 * (2 ^ ℓ * S * M) := by
      have : 5 * Real.pi / 2 * W ≤ 7.875 * W := by nlinarith
      nlinarith
    have t2 : 5 * Real.exp 1 / 2 * (Bmax ^ ℓ * X) ≤ 6.8 * (2 ^ ℓ * S * M) := by
      have : 5 * Real.exp 1 / 2 * (Bmax ^ ℓ * X) ≤ 6.8 * (Bmax ^ ℓ * X) := by nlinarith
      nlinarith
    have h0 : 0 ≤ 2 ^ ℓ * S * M := by positivity
    nlinarith
  have hE0 : 0 ≤ cB ^ ℓ * X * (cB + ℓ * Bmax) ^ ℓ / S ^ ℓ := by positivity
  have hFE : (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (Bmax ^ ℓ * X))
        * (cB ^ ℓ * X * (cB + ℓ * Bmax) ^ ℓ / S ^ ℓ)
      ≤ 15 * (8 * ℓ + 8 : ℝ) ^ ℓ * S * M ^ 2 * (S ^ ℓ / T) := by
    calc _ ≤ (15 * 2 ^ ℓ * S * M) * ((4 * ℓ + 4 : ℝ) ^ ℓ * S ^ ℓ * (M / T)) :=
          mul_le_mul hF hE hE0 (by positivity)
      _ = _ := by
          rw [show (8 * ℓ + 8 : ℝ) = 2 * (4 * ℓ + 4) by ring, mul_pow]; ring
  -- the powers of `S` and `T`
  have hpow : T ^ (2 - 2 * β) * ((S ^ (1 - α)) ^ (2 * ℓ))⁻¹ * (S ^ ℓ / T) ≤ T ^ (2 * α - 2 * β) := by
    have e1 : (S ^ (1 - α)) ^ (2 * ℓ) = (S ^ ℓ) ^ (2 - 2 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le, ← Real.rpow_natCast S ℓ,
        ← Real.rpow_mul hS0.le]
      push_cast; ring_nf
    have e2 : (S ^ ℓ) / ((S ^ ℓ) ^ (2 - 2 * α)) = (S ^ ℓ) ^ (2 * α - 1) := by
      have hne : (S ^ ℓ) ^ (2 - 2 * α) ≠ 0 := (Real.rpow_pos_of_pos hSl _).ne'
      rw [div_eq_iff hne, ← Real.rpow_add hSl]
      conv_lhs => rw [← Real.rpow_one (S ^ ℓ)]
      congr 1; ring
    have hmono : (S ^ ℓ) ^ (2 * α - 1) ≤ T ^ (2 * α - 1) :=
      Real.rpow_le_rpow_of_nonpos hT0 hhigh (by linarith)
    calc T ^ (2 - 2 * β) * ((S ^ (1 - α)) ^ (2 * ℓ))⁻¹ * (S ^ ℓ / T)
        = T ^ (2 - 2 * β) * T⁻¹ * ((S ^ ℓ) / ((S ^ ℓ) ^ (2 - 2 * α))) := by
          rw [e1]; field_simp
      _ = T ^ (2 - 2 * β) * T⁻¹ * (S ^ ℓ) ^ (2 * α - 1) := by rw [e2]
      _ ≤ T ^ (2 - 2 * β) * T⁻¹ * T ^ (2 * α - 1) := by gcongr
      _ = T ^ (2 * α - 2 * β) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hT0, ← Real.rpow_add hT0]; congr 1; ring
  have hA0 : 0 ≤ T ^ (2 - 2 * β) * ((S ^ (1 - α)) ^ (2 * ℓ))⁻¹ := by positivity
  calc T ^ (2 - 2 * β) * ((S ^ (1 - α)) ^ (2 * ℓ))⁻¹
        * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (Bmax ^ ℓ * X))
          * (cB ^ ℓ * X * (cB + ℓ * Bmax) ^ ℓ / S ^ ℓ))
      ≤ T ^ (2 - 2 * β) * ((S ^ (1 - α)) ^ (2 * ℓ))⁻¹
          * (15 * (8 * ℓ + 8 : ℝ) ^ ℓ * S * M ^ 2 * (S ^ ℓ / T)) :=
        mul_le_mul_of_nonneg_left hFE hA0
    _ = 15 * (8 * ℓ + 8 : ℝ) ^ ℓ * S * M ^ 2
          * (T ^ (2 - 2 * β) * ((S ^ (1 - α)) ^ (2 * ℓ))⁻¹ * (S ^ ℓ / T)) := by ring
    _ ≤ 15 * (8 * ℓ + 8 : ℝ) ^ ℓ * S * M ^ 2 * T ^ (2 * α - 2 * β) := by
        gcongr

/-- The cofactors of a common block lie in `[1, ⌊M/T⌋]`. -/
theorem mem_geomCofactorBlock_bounds {M : ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {v m : ℕ}
    (hm : m ∈ geomCofactorBlock M Q η v) :
    1 ≤ m ∧ m ≤ ⌊(M : ℝ) / (Q * (1 + η) ^ v)⌋₊ := by
  refine ⟨pos_of_mem_geomCofactorBlock hQ hη hm, ?_⟩
  rw [geomCofactorBlock, Finset.mem_Icc] at hm
  exact hm.2

/-- **The cofactor on a later first-small set, amplified by the previous range.** -/
theorem setIntegral_firstSmall_succ_cofactor_le (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (M : ℕ) {W : ℝ} (hW : 1 ≤ W) (j v : ℕ) (hR : 0 < R j) (hη : 0 ≤ η j)
    (hR' : 0 < R (j + 1)) (hη' : 0 ≤ η (j + 1)) (hPprime : ∀ q ∈ P j, q.Prime)
    (hV : ∀ r ∈ Finset.range (L j), 0 < V j r) (ℓ : ℕ → ℕ) :
    (∫ w in rangeFirstSmall P R η L V W (j + 1),
        ‖logPoly (ramareCofactorCoeff (P (j + 1))) (geomCofactorBlock M (R (j + 1)) (η (j + 1)) v) w‖
          ^ (2 : ℕ))
      ≤ ∑ r ∈ Finset.range (L j), (V j r ^ (2 * ℓ r))⁻¹
          * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2
                * ((⌊R j * (1 + η j) ^ r * (1 + η j)⌋₊ ^ ℓ r
                    * ⌊(M : ℝ) / (R (j + 1) * (1 + η (j + 1)) ^ v)⌋₊ : ℕ) : ℝ))
            * (((geomBlock (P j) (R j) (1 + η j) r).card : ℝ) ^ ℓ r
                * (⌊(M : ℝ) / (R (j + 1) * (1 + η (j + 1)) ^ v)⌋₊ : ℝ)
                * (((geomBlock (P j) (R j) (1 + η j) r).card : ℝ)
                  + ℓ r * (⌊R j * (1 + η j) ^ r * (1 + η j)⌋₊ : ℝ)) ^ ℓ r
                / (R j * (1 + η j) ^ r) ^ ℓ r)) := by
  have hcover := rangeFirstSmall_subset_someBlockLarge P R η L V W j
  refine (setIntegral_normSq_le_sum_amplified (Finset.range (L j)) (continuous_logPoly _ _)
    (fun r => geomBlock (P j) (R j) (1 + η j) r) (V j) hV ℓ hcover).trans ?_
  refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (by
    have := hV r ‹_›; positivity)
  have hSr : 0 < R j * (1 + η j) ^ r := by
    have : (0 : ℝ) < 1 + η j := by linarith
    positivity
  refine integral_normSq_primeBlockPoly_pow_mul_logPoly_le
    (fun p hp => hPprime p (geomBlock_subset _ _ _ _ hp)) (norm_ramareCofactorCoeff_le_one _)
    (fun m hm => mem_geomCofactorBlock_bounds hR' hη' hm) hSr
    (fun p hp => ?_) (fun p hp => ?_) (ℓ r) hW
  · rw [geomBlock, Finset.mem_filter] at hp
    exact hp.2.1.le
  · rw [geomBlock, Finset.mem_filter] at hp
    refine Nat.le_floor ?_
    have := hp.2.2
    rw [pow_succ] at this
    linarith

/-- The amplification exponent `ℓ = ⌈log T/log S⌉` brackets `T` between `S^{ℓ-1}` and `S^ℓ`. -/
theorem ceil_log_ratio_spec {S T : ℝ} (hS : 1 < S) (hT : 1 ≤ T) :
    S ^ (⌈Real.log T / Real.log S⌉₊ - 1) ≤ T ∧ T ≤ S ^ ⌈Real.log T / Real.log S⌉₊ := by
  have hS0 : 0 < S := by linarith
  have hT0 : 0 < T := by linarith
  have hlS : 0 < Real.log S := Real.log_pos hS
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  set x := Real.log T / Real.log S with hx
  have hx0 : 0 ≤ x := div_nonneg hlT hlS.le
  constructor
  · rcases Nat.eq_zero_or_pos ⌈x⌉₊ with h | h
    · rw [h]; simpa using hT
    · have hlt : ((⌈x⌉₊ - 1 : ℕ) : ℝ) ≤ x := by
        have := Nat.ceil_lt_add_one hx0
        rw [Nat.cast_sub (by omega)]
        push_cast; linarith
      rw [← Real.log_le_log_iff (by positivity) hT0, Real.log_pow]
      calc ((⌈x⌉₊ - 1 : ℕ) : ℝ) * Real.log S ≤ x * Real.log S := by gcongr
        _ = Real.log T := by rw [hx]; field_simp
  · rw [← Real.log_le_log_iff hT0 (by positivity), Real.log_pow]
    calc Real.log T = x * Real.log S := by rw [hx]; field_simp
      _ ≤ (⌈x⌉₊ : ℝ) * Real.log S := by gcongr; exact Nat.le_ceil x

theorem one_le_ceil_log_ratio {S T : ℝ} (hS : 1 < S) (hT : 1 < T) :
    1 ≤ ⌈Real.log T / Real.log S⌉₊ :=
  Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr
    (div_pos (Real.log_pos hT) (Real.log_pos hS))).ne'

/-- The cardinality of a block is at most its integer top. -/
theorem card_geomBlock_le_floor (P : Finset ℕ) {Q r : ℝ} (j : ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p) :
    ((geomBlock P Q r j).card : ℝ) ≤ (⌊Q * r ^ j * r⌋₊ : ℝ) := by
  have hsub : geomBlock P Q r j ⊆ Finset.Icc 1 ⌊Q * r ^ j * r⌋₊ := by
    intro p hp
    have hpP := geomBlock_subset P Q r j hp
    rw [geomBlock, Finset.mem_filter] at hp
    refine Finset.mem_Icc.mpr ⟨hP p hpP, Nat.le_floor ?_⟩
    have := hp.2.2
    rw [pow_succ] at this
    linarith
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc, add_tsub_cancel_right] at this
  exact_mod_cast this

/-- **The amplified cost of one block of a later range.**  With power thresholds
`V_{j,r} = S_r^{1-α}` and `V_{j+1,v} = T_v^{1-β}`,
`V_{j+1,v}²·∫_{T_{j+1}} ‖C_{j+1,v}‖² ≤ ∑_r 15(8ℓ_r+8)^{ℓ_r} S_r M² T_v^{2α-2β}`. -/
theorem rangeSucc_block_cost_le (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (M : ℕ) (hM : 0 < M) {W α β : ℝ} (hW : 1 ≤ W) (hWM : W ≤ M)
    (hα : α ≤ 1 / 2) (j v : ℕ) (hR : 1 < R j) (hη : 0 ≤ η j) (hη1 : η j ≤ 1)
    (hR' : 1 < R (j + 1)) (hη' : 0 ≤ η (j + 1)) (hPprime : ∀ q ∈ P j, q.Prime)
    (hVj : ∀ r, V j r = (R j * (1 + η j) ^ r) ^ (1 - α))
    (hVj' : V (j + 1) v = (R (j + 1) * (1 + η (j + 1)) ^ v) ^ (1 - β)) :
    V (j + 1) v ^ (2 : ℕ) * (∫ w in rangeFirstSmall P R η L V W (j + 1),
        ‖logPoly (ramareCofactorCoeff (P (j + 1))) (geomCofactorBlock M (R (j + 1)) (η (j + 1)) v) w‖
          ^ (2 : ℕ))
      ≤ ∑ r ∈ Finset.range (L j),
          15 * (8 * ⌈Real.log (R (j + 1) * (1 + η (j + 1)) ^ v)
                / Real.log (R j * (1 + η j) ^ r)⌉₊ + 8 : ℝ)
              ^ ⌈Real.log (R (j + 1) * (1 + η (j + 1)) ^ v) / Real.log (R j * (1 + η j) ^ r)⌉₊
            * (R j * (1 + η j) ^ r) * (M : ℝ) ^ 2
            * (R (j + 1) * (1 + η (j + 1)) ^ v) ^ (2 * α - 2 * β) := by
  set T := R (j + 1) * (1 + η (j + 1)) ^ v with hTdef
  have h1η : (1 : ℝ) ≤ 1 + η j := by linarith
  have h1η' : (1 : ℝ) ≤ 1 + η (j + 1) := by linarith
  have hT1 : 1 < T := by
    have : R (j + 1) ≤ T := le_mul_of_one_le_right (by linarith) (one_le_pow₀ h1η')
    linarith
  have hS1 : ∀ r, 1 < R j * (1 + η j) ^ r := fun r => by
    have : R j ≤ R j * (1 + η j) ^ r := le_mul_of_one_le_right (by linarith) (one_le_pow₀ h1η)
    linarith
  set ℓ : ℕ → ℕ := fun r => ⌈Real.log T / Real.log (R j * (1 + η j) ^ r)⌉₊ with hℓ
  have hVpos : ∀ r ∈ Finset.range (L j), 0 < V j r := fun r _ => by
    rw [hVj r]; exact Real.rpow_pos_of_pos (by linarith [hS1 r]) _
  have hbase := setIntegral_firstSmall_succ_cofactor_le P R η L V M hW j v (by linarith)
    hη (by linarith) hη' hPprime hVpos ℓ
  have hV2 : V (j + 1) v ^ (2 : ℕ) = T ^ (2 - 2 * β) := by
    rw [hVj', ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
  have hV20 : 0 ≤ V (j + 1) v ^ (2 : ℕ) := by positivity
  refine (mul_le_mul_of_nonneg_left hbase hV20).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  set S := R j * (1 + η j) ^ r with hSdef
  have hS := hS1 r
  obtain ⟨hlow, hhigh⟩ := ceil_log_ratio_spec hS hT1.le
  have hℓ1 := one_le_ceil_log_ratio hS hT1
  have hB0 : (0 : ℝ) ≤ (⌊S * (1 + η j)⌋₊ : ℝ) := Nat.cast_nonneg _
  have hBle : (⌊S * (1 + η j)⌋₊ : ℝ) ≤ 2 * S := by
    have := Nat.floor_le (show 0 ≤ S * (1 + η j) by positivity)
    nlinarith
  have hcard := card_geomBlock_le_floor (P j) (Q := R j) (r := 1 + η j) r
    (fun p hp => (hPprime p hp).one_lt.le)
  have hX0 : (0 : ℝ) ≤ (⌊(M : ℝ) / T⌋₊ : ℝ) := Nat.cast_nonneg _
  have hX : (⌊(M : ℝ) / T⌋₊ : ℝ) ≤ (M : ℝ) / T := Nat.floor_le (by positivity)
  have hkey := amplified_pair_le (S := S) (T := T) (M := M) (W := W)
    (X := (⌊(M : ℝ) / T⌋₊ : ℝ)) (Bmax := (⌊S * (1 + η j)⌋₊ : ℝ))
    (cB := ((geomBlock (P j) (R j) (1 + η j) r).card : ℝ)) (α := α) (β := β) (ℓ := ℓ r)
    hS.le hT1.le (by exact_mod_cast hM) (by linarith) hWM hℓ1 hlow hhigh hα hX0 hX hB0 hBle
    (Nat.cast_nonneg _) (hcard.trans hBle)
  rw [hV2, hVj r]
  push_cast
  calc T ^ (2 - 2 * β) * (((S ^ (1 - α)) ^ (2 * ℓ r))⁻¹
        * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2
            * ((⌊S * (1 + η j)⌋₊ : ℝ) ^ ℓ r * (⌊(M : ℝ) / T⌋₊ : ℝ)))
          * (((geomBlock (P j) (R j) (1 + η j) r).card : ℝ) ^ ℓ r * (⌊(M : ℝ) / T⌋₊ : ℝ)
            * (((geomBlock (P j) (R j) (1 + η j) r).card : ℝ)
              + (ℓ r : ℝ) * (⌊S * (1 + η j)⌋₊ : ℝ)) ^ ℓ r / S ^ ℓ r)))
      = T ^ (2 - 2 * β) * ((S ^ (1 - α)) ^ (2 * ℓ r))⁻¹
        * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2
            * ((⌊S * (1 + η j)⌋₊ : ℝ) ^ ℓ r * (⌊(M : ℝ) / T⌋₊ : ℝ)))
          * (((geomBlock (P j) (R j) (1 + η j) r).card : ℝ) ^ ℓ r * (⌊(M : ℝ) / T⌋₊ : ℝ)
            * (((geomBlock (P j) (R j) (1 + η j) r).card : ℝ)
              + (ℓ r : ℝ) * (⌊S * (1 + η j)⌋₊ : ℝ)) ^ ℓ r / S ^ ℓ r)) := by ring
    _ ≤ _ := hkey

end

end RHTower.Sieve
