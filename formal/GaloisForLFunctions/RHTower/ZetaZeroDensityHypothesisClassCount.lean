import GaloisForLFunctions.RHTower.ZetaZeroDetectorGenericClasses
import GaloisForLFunctions.RHTower.ZetaZeroDetectorParametricDichotomy
import GaloisForLFunctions.RHTower.ZetaZeroClassCountGeneralPower

/-!
# The detector class count on `σ ≥ 5/6`: exponent `2 + ε`

Fix `0 < ε ≤ 1` and the detector lengths `X = ⌊T^{ε/16}⌋`, `Y = T^y`, `Z = ⌊T^y (log T)²⌋` with
`y = 1/2 + ε/8`.  A Type I block `2^j` lies in `[T^{ε/32}, Z]`, so a power `ℓ ≤ M = ⌈32/ε⌉` puts
`X' = (2^j)^ℓ` in the window `[T^{4y/3}, T^{2y}(log T)⁴]` (`ℓ = 2` above `T^{2y/3}`, the first power
past `T^{4y/3}` below).  For `5/6 ≤ σ ≤ 1`:

* `X'^{2-2σ} ≤ T^{(2 + ε/2)(1-σ)} (log T)^{8(1-σ)} ≤ T^{(2+ε)(1-σ)}`;
* the Huxley term `T X'^{4-6σ} ≤ T^{1 + (2/3 + ε/6)(4-6σ)} ≤ T^{(2+ε)(1-σ)}`, the difference of
  exponents being `2σ - 5/3 + ε/3 ≥ 0`;
* Huxley's threshold holds: `X'^{3/2-2σ} ≤ T^{-1/9}`.

The class count is `#W ≤ C_M (1 + log T)^{B_M} T^{(2+ε)(1-σ)}` (`exists_dh_class_card_le`).
-/

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve

/-- The mollifier exponent `ε/16`. -/
def dhMollExp (ε : ℝ) : ℝ := ε / 16

/-- The smoothing exponent `y = 1/2 + ε/8`. -/
def dhSmoothExp (ε : ℝ) : ℝ := 1 / 2 + ε / 8

/-- The largest power `M = ⌈32/ε⌉`. -/
def dhPowerBound (ε : ℝ) : ℕ := ⌈32 / ε⌉₊

/-- The logarithmic exponent `6M + 3·2^{4M} + 1`. -/
def dhLogExponent (ε : ℝ) : ℕ := 6 * dhPowerBound ε + 3 * 2 ^ (4 * dhPowerBound ε) + 1

/-- The constant `C_M (M + 100)^{B_M}`. -/
def dhCountConstant (ε : ℝ) : ℝ :=
  classHuxleyConstantOf (dhPowerBound ε) * ((dhPowerBound ε : ℝ) + 100) ^ dhLogExponent ε

theorem dhCountConstant_nonneg (ε : ℝ) : 0 ≤ dhCountConstant ε := by
  unfold dhCountConstant
  have := classHuxleyConstantOf_nonneg (dhPowerBound ε)
  positivity

/-- A block with a large class value has a nonzero coefficient, so `X < 2·2^j ≤ 2Z`. -/
theorem gDetBlock_bounds_of_large {X Z j i : ℕ} {Y Λ σ' t V : ℝ} (hV : 0 < V)
    (hbig : V ≤ ‖abscissaTaylorPoly (gDetBlock Z j) (fun k => ((gDetCoeff X Y k : ℝ) : ℂ))
      Λ i σ' t‖) :
    X < 2 * 2 ^ j ∧ 2 ^ j ≤ Z := by
  have hne : ∃ k ∈ gDetBlock Z j, gDetCoeff X Y k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : abscissaTaylorPoly (gDetBlock Z j) (fun k => ((gDetCoeff X Y k : ℝ) : ℂ))
        Λ i σ' t = 0 := by
      unfold abscissaTaylorPoly
      refine Finset.sum_eq_zero fun k hk => ?_
      simp [hcon k hk]
    rw [hzero, norm_zero] at hbig
    linarith
  obtain ⟨k, hk, hkne⟩ := hne
  have hb := mem_gDetBlock_bounds hk
  exact ⟨gDetMoll_lt_of_coeff_ne_zero hk hkne, le_trans hb.2.2.1 hb.2.1⟩

/-- `J ≤ 2(1 + log T)` once `2 ≤ Z ≤ T`. -/
theorem gDetBlockCount_le_log {Z : ℕ} {T : ℝ} (hZ : 2 ≤ Z) (hZT : (Z : ℝ) ≤ T) :
    (gDetBlockCount Z : ℝ) ≤ 2 * (1 + Real.log T) := by
  have hZ0 : Z ≠ 0 := by omega
  have hpow : ((2 : ℝ) ^ Nat.log 2 Z) ≤ Z := by exact_mod_cast Nat.pow_log_le_self 2 hZ0
  have hlog2 : (Nat.log 2 Z : ℝ) * Real.log 2 ≤ Real.log Z := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have hlogZ : Real.log Z ≤ Real.log T :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hZ0) hZT
  have hl2 : (0.69 : ℝ) < Real.log 2 := Real.log_two_gt_d9.trans' (by norm_num)
  have hlogT : 0 ≤ Real.log T := le_trans (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Z)))
    hlogZ
  have hN : (Nat.log 2 Z : ℝ) ≤ 2 * Real.log T := by
    have h2 : (Nat.log 2 Z : ℝ) * 0.69 ≤ (Nat.log 2 Z : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
    nlinarith
  unfold gDetBlockCount
  push_cast
  linarith

/-- **The power window.**  If `T^{ε/32} ≤ K ≤ T^y (log T)²` with `y = 1/2 + ε/8`, `0 < ε ≤ 1` and
`log T ≥ 1`, then some power `K^ℓ`, `1 ≤ ℓ ≤ ⌈32/ε⌉`, lies in `[T^{4y/3}, T^{2y}(log T)⁴]`. -/
theorem exists_pow_mem_dh_window {ε T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 1 < T)
    (hlog1 : 1 ≤ Real.log T) {K : ℕ} (hK1 : T ^ (ε / 32) ≤ K)
    (hK2 : (K : ℝ) ≤ T ^ dhSmoothExp ε * Real.log T ^ 2) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ dhPowerBound ε ∧ T ^ (4 * dhSmoothExp ε / 3) ≤ (K : ℝ) ^ ℓ ∧
      (K : ℝ) ^ ℓ ≤ T ^ (2 * dhSmoothExp ε) * Real.log T ^ 4 := by
  classical
  set y := dhSmoothExp ε with hy
  have hT0 : 0 < T := by linarith
  have hK0 : 0 < (K : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 _) hK1
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT.le
  have hM : (32 / ε : ℝ) ≤ dhPowerBound ε := Nat.le_ceil _
  have hM2 : 2 ≤ dhPowerBound ε := by
    have h32 : (32 : ℝ) ≤ 32 / ε := by rw [le_div_iff₀ hε]; linarith
    have : (2 : ℝ) ≤ dhPowerBound ε := by linarith
    exact_mod_cast this
  by_cases hbig : T ^ (2 * y / 3) ≤ K
  · refine ⟨2, by norm_num, hM2, ?_, ?_⟩
    · calc T ^ (4 * y / 3) = (T ^ (2 * y / 3)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
        _ ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hbig 2
    · calc (K : ℝ) ^ 2 ≤ (T ^ y * Real.log T ^ 2) ^ 2 := pow_le_pow_left₀ hK0.le hK2 2
        _ = T ^ (2 * y) * Real.log T ^ 4 := by
            rw [mul_pow, ← Real.rpow_natCast (T ^ y), ← Real.rpow_mul hT0.le, ← pow_mul]
            ring_nf
  · push Not at hbig
    have hy1 : 4 * y / 3 ≤ 1 := by rw [hy, dhSmoothExp]; linarith
    have hMpow : T ^ (4 * y / 3) ≤ (K : ℝ) ^ dhPowerBound ε := by
      calc T ^ (4 * y / 3) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT.le hy1
        _ ≤ T ^ (ε / 32 * dhPowerBound ε) := by
            apply Real.rpow_le_rpow_of_exponent_le hT.le
            have := mul_le_mul_of_nonneg_left hM (show (0 : ℝ) ≤ ε / 32 by positivity)
            rw [show ε / 32 * (32 / ε) = 1 by field_simp] at this
            exact this
        _ = (T ^ (ε / 32)) ^ dhPowerBound ε := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        _ ≤ (K : ℝ) ^ dhPowerBound ε := pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hK1 _
    have hex : ∃ ℓ, T ^ (4 * y / 3) ≤ (K : ℝ) ^ ℓ := ⟨_, hMpow⟩
    set ℓ := Nat.find hex with hℓ
    have hspec : T ^ (4 * y / 3) ≤ (K : ℝ) ^ ℓ := Nat.find_spec hex
    have hle : ℓ ≤ dhPowerBound ε := Nat.find_min' hex hMpow
    have hy0 : 0 < 4 * y / 3 := by rw [hy, dhSmoothExp]; positivity
    have hone : 1 < T ^ (4 * y / 3) := Real.one_lt_rpow hT hy0
    have hℓ1 : 1 ≤ ℓ := by
      by_contra h
      have h0 : ℓ = 0 := by omega
      rw [h0, pow_zero] at hspec
      linarith
    refine ⟨ℓ, hℓ1, hle, hspec, ?_⟩
    have hmin : ¬ T ^ (4 * y / 3) ≤ (K : ℝ) ^ (ℓ - 1) := Nat.find_min hex (by omega)
    push Not at hmin
    have hsplit : (K : ℝ) ^ ℓ = (K : ℝ) ^ (ℓ - 1) * K := by
      rw [← pow_succ]
      congr 1
      omega
    calc (K : ℝ) ^ ℓ = (K : ℝ) ^ (ℓ - 1) * K := hsplit
      _ ≤ T ^ (4 * y / 3) * T ^ (2 * y / 3) :=
          mul_le_mul hmin.le hbig.le hK0.le (Real.rpow_nonneg hT0.le _)
      _ = T ^ (2 * y) := by rw [← Real.rpow_add hT0]; ring_nf
      _ ≤ T ^ (2 * y) * Real.log T ^ 4 :=
          le_mul_of_one_le_right (Real.rpow_nonneg hT0.le _) (one_le_pow₀ hlog1)

/-- The diagonal term: `X^{2-2σ} ≤ T^{(2+ε)(1-σ)}` for `X ≤ T^{2y}(log T)⁴`. -/
theorem dh_window_diagonal_le {T X σ ε : ℝ} (hT : 1 ≤ T) (hX0 : 0 ≤ X)
    (hX2 : X ≤ T ^ (2 * dhSmoothExp ε) * Real.log T ^ 4) (hσ : σ ≤ 1)
    (hlogε : Real.log T ^ 8 ≤ T ^ (ε / 2)) :
    X ^ (2 - 2 * σ) ≤ T ^ ((2 + ε) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  have hl0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have h1 : X ^ (2 - 2 * σ) ≤ (T ^ (2 * dhSmoothExp ε) * Real.log T ^ 4) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow hX0 hX2 (by linarith)
  have h2 : (T ^ (2 * dhSmoothExp ε) * Real.log T ^ 4) ^ (2 - 2 * σ) =
      T ^ ((2 + ε / 2) * (1 - σ)) * (Real.log T ^ 8) ^ (1 - σ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hT0.le _) (by positivity), ← Real.rpow_mul hT0.le]
    congr 1
    · unfold dhSmoothExp
      ring_nf
    · rw [← Real.rpow_natCast (Real.log T) 4, ← Real.rpow_natCast (Real.log T) 8,
        ← Real.rpow_mul hl0, ← Real.rpow_mul hl0]
      ring_nf
  have h3 : (Real.log T ^ 8) ^ (1 - σ) ≤ (T ^ (ε / 2)) ^ (1 - σ) :=
    Real.rpow_le_rpow (by positivity) hlogε (by linarith)
  have h4 : T ^ ((2 + ε / 2) * (1 - σ)) * (T ^ (ε / 2)) ^ (1 - σ) = T ^ ((2 + ε) * (1 - σ)) := by
    rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
    ring_nf
  calc X ^ (2 - 2 * σ) ≤ T ^ ((2 + ε / 2) * (1 - σ)) * (Real.log T ^ 8) ^ (1 - σ) := h2 ▸ h1
    _ ≤ T ^ ((2 + ε / 2) * (1 - σ)) * (T ^ (ε / 2)) ^ (1 - σ) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hT0.le _)
    _ = T ^ ((2 + ε) * (1 - σ)) := h4

/-- The Huxley term: `T X^{4-6σ} ≤ T^{(2+ε)(1-σ)}` for `X ≥ T^{4y/3}`, `5/6 ≤ σ ≤ 1`. -/
theorem dh_huxley_term_le {T X σ ε : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (4 * dhSmoothExp ε / 3) ≤ X)
    (hσ : 5 / 6 ≤ σ) (hε : 0 ≤ ε) :
    T * X ^ (4 - 6 * σ) ≤ T ^ ((2 + ε) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  calc T * X ^ (4 - 6 * σ) ≤ T * (T ^ (4 * dhSmoothExp ε / 3)) ^ (4 - 6 * σ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hX1 (by linarith)) hT0.le
    _ = T ^ (1 + (4 * dhSmoothExp ε / 3) * (4 - 6 * σ)) := by
        rw [← Real.rpow_mul hT0.le, Real.rpow_add hT0, Real.rpow_one]
    _ ≤ T ^ ((2 + ε) * (1 - σ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hT
        unfold dhSmoothExp
        nlinarith

/-- Huxley's threshold: `X^{3/2-2σ} ≤ T^{-1/9}` for `X ≥ T^{4y/3}`, `σ ≥ 5/6`. -/
theorem dh_huxley_decay_le {T X σ ε : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (4 * dhSmoothExp ε / 3) ≤ X)
    (hXge : 1 ≤ X) (hε : 0 ≤ ε) (hσ : 5 / 6 ≤ σ) :
    X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ T ^ (-(1 / 9 : ℝ)) := by
  have hT0 : 0 < T := by linarith
  calc X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ X ^ (-(1 / 6 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hXge (by linarith)
    _ ≤ (T ^ (4 * dhSmoothExp ε / 3)) ^ (-(1 / 6 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hX1 (by norm_num)
    _ = T ^ (-(4 * dhSmoothExp ε / 18)) := by rw [← Real.rpow_mul hT0.le]; ring_nf
    _ ≤ T ^ (-(1 / 9 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hT
        unfold dhSmoothExp
        nlinarith

/-- `T^{ε/32} ≤ 2^j` whenever `⌊T^{ε/16}⌋ < 2·2^j` and `T^{ε/32} ≥ 2`. -/
theorem rpow_dh_le_of_moll_lt {ε T : ℝ} (hT1 : 1 ≤ T) (h2 : 2 ≤ T ^ (ε / 32))
    {j : ℕ} (hj : pDetMoll (dhMollExp ε) T < 2 * 2 ^ j) : T ^ (ε / 32) ≤ ((2 ^ j : ℕ) : ℝ) := by
  have hT0 : 0 < T := by linarith
  have h1 : (pDetMoll (dhMollExp ε) T : ℝ) + 1 ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (show pDetMoll (dhMollExp ε) T + 1 ≤ 2 * 2 ^ j by omega)
  have h2' : T ^ (ε / 16) < (pDetMoll (dhMollExp ε) T : ℝ) + 1 := by
    unfold pDetMoll dhMollExp
    exact Nat.lt_floor_add_one _
  have h4 : T ^ (ε / 16) = T ^ (ε / 32) * T ^ (ε / 32) := by
    rw [← Real.rpow_add hT0]
    ring_nf
  have h5 : 2 * T ^ (ε / 32) ≤ T ^ (ε / 16) := by
    rw [h4]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT0.le _)
  linarith

/-- The facts on `Q = (M + 100)(1 + log T)` used by the class count. -/
structure DhBigFacts (M : ℕ) (Q T : ℝ) : Prop where
  threshold : 3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M) * (Q ^ (2 * M) * Q ^ (2 ^ (4 * M)))
    ≤ T ^ (1 / 9 : ℝ)

theorem exists_dhBigFacts (M : ℕ) :
    ∃ TH : ℝ, ∀ T : ℝ, TH ≤ T →
      DhBigFacts M (((M : ℝ) + 100) * (1 + Real.log T)) T := by
  obtain ⟨TH, hTH⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow (2 * M + 2 ^ (4 * M)) (c := 1 / 9) (by norm_num)
      (3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M) * ((M : ℝ) + 100) ^ (2 * M + 2 ^ (4 * M))))
  refine ⟨TH, fun T hT => ⟨?_⟩⟩
  have h := hTH T hT
  rw [← pow_add, mul_pow]
  calc 3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M)
        * (((M : ℝ) + 100) ^ (2 * M + 2 ^ (4 * M)) * (1 + Real.log T) ^ (2 * M + 2 ^ (4 * M)))
      = 3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M) * ((M : ℝ) + 100) ^ (2 * M + 2 ^ (4 * M))
          * (1 + Real.log T) ^ (2 * M + 2 ^ (4 * M)) := by ring
    _ ≤ T ^ (1 / 9 : ℝ) := h

/-- **The detector class count on `σ ≥ 5/6`, exponent `2 + ε`.** -/
theorem exists_dh_class_card_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 5 / 6 ≤ σ → σ ≤ 1 →
      ∀ (j i : ℕ) (σ' : ℝ), σ ≤ σ' → ∀ W : Finset ℝ,
        (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) →
        (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
        (∀ t ∈ W, 1 / (48 * (gDetBlockCount (pDetCut (dhSmoothExp ε) T) : ℝ)) ≤
          ‖abscissaTaylorPoly (gDetBlock (pDetCut (dhSmoothExp ε) T) j)
            (fun k => ((gDetCoeff (pDetMoll (dhMollExp ε) T) (pDetSmooth (dhSmoothExp ε) T) k :
              ℝ) : ℂ))
            (gDetLog (pDetCut (dhSmoothExp ε) T)) i σ' t‖) →
        (W.card : ℝ) ≤ dhCountConstant ε * (1 + Real.log T) ^ dhLogExponent ε
          * T ^ ((2 + ε) * (1 - σ)) := by
  set M := dhPowerBound ε with hMdef
  set y := dhSmoothExp ε with hydef
  have hy0 : 0 < y := by rw [hydef, dhSmoothExp]; positivity
  have hy1 : y ≤ 5 / 8 := by rw [hydef, dhSmoothExp]; linarith
  obtain ⟨TH, hTH⟩ := exists_dhBigFacts M
  obtain ⟨TA, hTA⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 2 (c := 3 / 8) (by norm_num) 1)
  obtain ⟨TB, hTB⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 4 (c := 3 / 4) (by norm_num) 1)
  obtain ⟨TC, hTC⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 8 (c := ε / 2) (by positivity) 1)
  obtain ⟨TD, hTD⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0 : ℝ) < ε / 32 by positivity)).eventually_ge_atTop 2)
  refine ⟨max (max (max (Real.exp 1) 4) TH) (max TA (max TB (max TC TD))), ?_⟩
  intro T hT σ hσ1 hσ2 j i σ' hσσ' W hW hsep hbig
  have hTe : Real.exp 1 ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hT
  have hTTH : TH ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTTA : TA ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTTB : TB ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hT
  have hTTC : TC ≤ T := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hT
  have hTTD : TD ≤ T := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hT
  have hT1 : (1 : ℝ) ≤ T := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hTe
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    exact hTe
  have hT2 : (2 : ℝ) ≤ T := by linarith [Real.add_one_le_exp (1 : ℝ)]
  -- polylogarithmic comparisons
  have hA := hTA T hTTA
  have hB := hTB T hTTB
  have hC := hTC T hTTC
  simp only [one_mul] at hA hB hC
  have hlogsq : Real.log T ^ 2 ≤ T ^ (3 / 8 : ℝ) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 2) hA
  have hlog4 : Real.log T ^ 4 ≤ T ^ (3 / 4 : ℝ) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 4) hB
  have hlog8 : Real.log T ^ 8 ≤ T ^ (ε / 2) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 8) hC
  have hZT : T ^ y * Real.log T ^ 2 ≤ T := by
    calc T ^ y * Real.log T ^ 2 ≤ T ^ (5 / 8 : ℝ) * T ^ (3 / 8 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 hy1) hlogsq (by positivity)
            (Real.rpow_nonneg hT0.le _)
      _ = T := by rw [← Real.rpow_add hT0]; norm_num
  have hwin2 : T ^ (2 * y) * Real.log T ^ 4 ≤ T ^ (2 : ℝ) := by
    calc T ^ (2 * y) * Real.log T ^ 4 ≤ T ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hlog4 (by positivity)
            (Real.rpow_nonneg hT0.le _)
      _ = T ^ (2 : ℝ) := by rw [← Real.rpow_add hT0]; norm_num
  set Zc := pDetCut y T with hZc
  have hZle : (Zc : ℝ) ≤ T ^ y * Real.log T ^ 2 :=
    Nat.floor_le (by positivity)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = ((M : ℝ) + 100) * (1 + Real.log T) := ⟨_, rfl⟩
  have hBig := hTH T hTTH
  rw [← hQdef] at hBig
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hl1 : 1 ≤ 1 + Real.log T := by linarith only [hlog0]
  have hQM3 : ((M : ℝ) + 3) * (1 + Real.log T) ≤ Q := by
    rw [hQdef]; exact mul_le_mul_of_nonneg_right (by linarith only) (by linarith only [hl1])
  have hQlow : 36 * (1 + Real.log T) ≤ Q := by
    rw [hQdef]; exact mul_le_mul_of_nonneg_right (by linarith only [hM0]) (by linarith only [hl1])
  have hQ1 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ 36 * (1 + Real.log T) := by linarith only [hl1]
    linarith only [this, hQlow]
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ1
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Q ^ (2 ^ (4 * M)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPdef]; exact pow_nonneg hQ0.le _
  set R : ℝ := Q ^ (4 * M + 3 * 2 ^ (4 * M)) with hRdef
  have hcube : Q ^ (4 * M) * P ^ 3 ≤ R := by
    rw [hPdef, ← pow_mul, ← pow_add, hRdef, mul_comm (2 ^ (4 * M)) 3]
  have hsingle : P ≤ R := by
    rw [hPdef, hRdef]
    exact pow_le_pow_right₀ hQ1 (by omega)
  rcases W.eq_empty_or_nonempty with hWe | ⟨t₀, ht₀⟩
  · rw [hWe, card_empty, Nat.cast_zero]
    have := dhCountConstant_nonneg ε
    have hl : 0 ≤ 1 + Real.log T := by linarith
    positivity
  set J := gDetBlockCount Zc with hJdef
  set V : ℝ := 1 / (48 * (J : ℝ)) with hVdef
  have hJpos : (0 : ℝ) < J := by
    rw [hJdef, gDetBlockCount]
    positivity
  have hV0 : 0 < V := by positivity
  obtain ⟨hjX, hjZ⟩ := gDetBlock_bounds_of_large hV0 (hbig t₀ ht₀)
  have hZ2 : 2 ≤ Zc := by
    have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_right (Real.exp 1) 4)
      (le_trans (le_max_left _ TH) (le_trans (le_max_left _ _) hT))
    have hTy : (2 : ℝ) ≤ T ^ y := by
      calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hT4 (by norm_num)
        _ ≤ T ^ y := Real.rpow_le_rpow_of_exponent_le hT1 (by rw [hydef, dhSmoothExp]; linarith)
    have h2 : (2 : ℝ) ≤ T ^ y * Real.log T ^ 2 :=
      le_trans hTy (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog1))
    rw [hZc, pDetCut]
    exact Nat.le_floor (by exact_mod_cast h2)
  have hJQ : 48 * (J : ℝ) ≤ Q := by
    have hZTR : (Zc : ℝ) ≤ T := le_trans hZle hZT
    have hJ2 := gDetBlockCount_le_log hZ2 hZTR
    rw [hQdef]
    calc 48 * (J : ℝ) ≤ 48 * (2 * (1 + Real.log T)) := by linarith only [hJ2]
      _ = 96 * (1 + Real.log T) := by ring
      _ ≤ ((M : ℝ) + 100) * (1 + Real.log T) :=
          mul_le_mul_of_nonneg_right (by linarith only [hM0]) (by linarith only [hlog0])
  have hVQ : 1 / Q ≤ V := by
    rw [hVdef]
    exact one_div_le_one_div_of_le (by positivity) hJQ
  set Λ := gDetLog Zc with hΛ
  set B := gDetBlock Zc j with hBdef
  set Xm := pDetMoll (dhMollExp ε) T with hXm
  set Ys := pDetSmooth y T with hYs
  have hXm1 : 1 ≤ Xm := one_le_pDetMoll (by unfold dhMollExp; positivity) hT1
  have hYs0 : 0 < Ys := lt_of_lt_of_le one_pos (one_le_pDetSmooth hy0.le hT1)
  have hB1 : ∀ k ∈ B, 1 ≤ k := fun k hk => (mem_gDetBlock_bounds hk).1
  have hBb : ∀ k ∈ B, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1 := fun k hk =>
    ⟨(mem_gDetBlock_bounds hk).2.2.1, (mem_gDetBlock_bounds hk).2.2.2⟩
  have hBΛ : ∀ k ∈ B, Real.log k ≤ Λ := by
    intro k hk
    have hk := mem_gDetBlock_bounds hk
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk.2.1)
  have hcoef : ∀ k ∈ B, |gDetCoeff Xm Ys k| ≤ k.divisors.card :=
    fun k _ => abs_gDetCoeff_le hXm1 hYs0 k
  have hbig' : ∀ t ∈ W, V ≤ ‖dpoly (genClassCoeff (gDetCoeff Xm Ys) Λ i σ') B t‖ := by
    intro t ht
    rw [← abscissaTaylorPoly_ofReal_eq_dpoly hB1]
    exact hbig t ht
  have hK1 := rpow_dh_le_of_moll_lt hT1 (hTD T hTTD) hjX
  have hK2 : ((2 ^ j : ℕ) : ℝ) ≤ T ^ y * Real.log T ^ 2 :=
    le_trans (by exact_mod_cast hjZ) hZle
  obtain ⟨ℓ, hℓ1, hℓM, hX1, hX2⟩ := exists_pow_mem_dh_window hε hε1
    (lt_of_lt_of_le one_lt_two hT2) hlog1 hK1 hK2
  have hX2' : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ T ^ (2 : ℝ) := le_trans hX2 hwin2
  set X : ℝ := (((2 ^ j : ℕ) : ℝ)) ^ ℓ with hXdef
  have hXge1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast Nat.one_le_two_pow)
  have hσ0 : (0 : ℝ) ≤ σ := le_trans (by norm_num) hσ1
  have hmass₀ := classPowerMass_le_of_le (σ := σ) hT1 hℓM hX2'
  rw [← hXdef] at hmass₀
  have hPP : (((M : ℝ) + 3) * (1 + Real.log T)) ^ (2 ^ (4 * M)) ≤ P := by
    rw [hPdef]
    exact pow_le_pow_left₀ (by positivity) hQM3 _
  have hmass : classPowerMass j ℓ σ ≤ 2 ^ M * X ^ (1 - 2 * σ) * P :=
    le_trans hmass₀ (mul_le_mul_of_nonneg_left hPP (by positivity))
  have hLcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * X := by
    rw [hXdef]
    push_cast
    ring
  have hLM : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ 2 ^ M * X := by
    rw [hLcast]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hℓM) (by linarith)
  have hL1 : (1 : ℝ) ≤ (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by positivity)
  have hVl : 1 / Q ^ M ≤ V ^ ℓ := by
    calc 1 / Q ^ M ≤ 1 / Q ^ ℓ := one_div_le_one_div_of_le (pow_pos hQ0 _)
          (pow_le_pow_right₀ hQ1 hℓM)
      _ = (1 / Q) ^ ℓ := by rw [one_div_pow]
      _ ≤ V ^ ℓ := pow_le_pow_left₀ (by positivity) hVQ ℓ
  have hG0 : 0 ≤ classPowerMass j ℓ σ := by unfold classPowerMass; positivity
  have hdiag := dh_window_diagonal_le hT1 (by linarith) hX2 hσ2 hlog8
  have hVlpos : 0 < V ^ ℓ := pow_pos hV0 ℓ
  have hℓRM : (ℓ : ℝ) ≤ M := by exact_mod_cast hℓM
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = ℓ / V ^ ℓ := ⟨_, rfl⟩
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hU0 : 0 < U := by rw [hUdef]; positivity
  have hU : U ≤ M * Q ^ M := by
    rw [hUdef, div_le_iff₀ hVlpos]
    have h1 : 1 ≤ Q ^ M * V ^ ℓ := by
      have := mul_le_mul_of_nonneg_left hVl (pow_nonneg hQ0.le M)
      rwa [mul_one_div_cancel (pow_pos hQ0 _).ne'] at this
    calc (ℓ : ℝ) ≤ M * 1 := by linarith only [hℓRM]
      _ ≤ M * (Q ^ M * V ^ ℓ) := mul_le_mul_of_nonneg_left h1 hM0
      _ = M * Q ^ M * V ^ ℓ := by ring
  have hVU : V ^ ℓ / ℓ = 1 / U := by rw [hUdef, one_div_div]
  have hthr' := class_huxley_threshold_arith_of_le hT1 hXge1
    (dh_huxley_decay_le hT1 hX1 hXge1 hε.le hσ1) hQ1 hP0 hL1 hLM hmass hU0 hU
    (by rw [hPdef]; exact hBig.threshold)
  rw [← hVU] at hthr'
  have hhux := card_mul_pow_le_genClass_huxley (B := B) (c := gDetCoeff Xm Ys) (Λ := Λ)
    (i := i) hℓ1 hBb hBΛ hcoef hσ0 hσσ' hT0.le hV0 hW hsep hbig' hthr'
  rw [hVU] at hhux
  have hc := class_count_huxley_arith_of_le hT1 hXge1
    (dh_huxley_term_le hT1 hX1 hσ1 hε.le) hdiag hQ1 hQlow hP0 hcube
    hsingle hL1 hLM hG0 hmass hU0 hU hℓRM hhux
  refine le_trans hc (le_of_eq ?_)
  have hQB : Q ^ (2 * M) * R * Q = Q ^ dhLogExponent ε := by
    rw [hRdef, ← pow_add, ← pow_succ, dhLogExponent, ← hMdef]
    congr 1
    ring
  rw [hQB, hQdef, mul_pow, dhCountConstant, ← hMdef]
  ring

end RHTower

end
