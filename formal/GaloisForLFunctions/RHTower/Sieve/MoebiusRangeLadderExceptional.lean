import GaloisForLFunctions.RHTower.Sieve.MoebiusRangeLadderWindow
import GaloisForLFunctions.RHTower.Sieve.ShortExceptionalMeasure

/-!
# The exceptional set of the ladder

A frequency outside every first-small set has, in the last range `K`, a block exceeding its
threshold `S^{1-α_K}`.  The moment method at order `k = ⌈log W/log S⌉ + 1` bounds each such set by
`4·W^{2α_K}·S²·(1 + k log 2S)·(4k)^k`.  Choosing `K` least with `ν_K ≥ T` puts `ν_K ∈ [T, T²]` and
`2^K ≤ (log T)/2`; since `1/2 + 2α_K = 1 − 1/(4·2^K)`, the saving `M^{-1/(4·2^K)}` is
`exp(−log M/(2 log T))`, and when `log M ≍ T⁴⁰` it beats every other factor:
`√W·|U| ≤ M·exp(−T⁴⁰/(8 log T))`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The moment order `k = ⌈log W/log S⌉ + 1` brackets `W` between `S^{k-1}` and `S^k/S`. -/
theorem momentOrder_spec {S W : ℝ} (hS : 1 < S) (hW : 1 ≤ W) :
    W ≤ S ^ (⌈Real.log W / Real.log S⌉₊ + 1 - 1)
      ∧ S ^ (⌈Real.log W / Real.log S⌉₊ + 1) ≤ W * S ^ 2 := by
  have hS0 : 0 < S := by linarith
  have hW0 : 0 < W := by linarith
  have hlS : 0 < Real.log S := Real.log_pos hS
  have hlW : 0 ≤ Real.log W := Real.log_nonneg hW
  set x := Real.log W / Real.log S with hx
  have hx0 : 0 ≤ x := div_nonneg hlW hlS.le
  have hxS : x * Real.log S = Real.log W := by rw [hx]; field_simp
  constructor
  · rw [Nat.add_sub_cancel, ← Real.log_le_log_iff hW0 (by positivity), Real.log_pow]
    calc Real.log W = x * Real.log S := hxS.symm
      _ ≤ (⌈x⌉₊ : ℝ) * Real.log S := by gcongr; exact Nat.le_ceil x
  · rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
      Real.log_mul hW0.ne' (by positivity), Real.log_pow]
    have hc := Nat.ceil_lt_add_one hx0
    push_cast
    nlinarith

/-- **The exceptional set of one block at a power threshold.**  For a block of primes up to
`S(1+η) ≤ 2S` thresholded at `S^{1-α}`, the moment method at order `k = ⌈log W/log S⌉ + 1` gives
`|{|w| ≤ W : |Q(w)| ≥ S^{1-α}}| ≤ 4·W^{2α}·S²·(1 + k log 2S)·(4k)^k`. -/
theorem measureReal_shortExceptional_power_le {B : Finset ℕ} (hBprime : ∀ p ∈ B, p.Prime)
    {S η W α : ℝ} (hS : 1 < S) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hB : B ⊆ Finset.Icc 1 ⌊S * (1 + η)⌋₊) (hW : 1 ≤ W) (hα : α < 1 / 2) :
    volume.real (shortExceptional B W (S ^ (1 - α)))
      ≤ 4 * W ^ (2 * α) * S ^ 2
          * (1 + (⌈Real.log W / Real.log S⌉₊ + 1 : ℕ) * Real.log (2 * S))
          * (4 * ((⌈Real.log W / Real.log S⌉₊ + 1 : ℕ) : ℝ)) ^ (⌈Real.log W / Real.log S⌉₊ + 1) := by
  set k := ⌈Real.log W / Real.log S⌉₊ + 1 with hkdef
  have hk : 1 ≤ k := Nat.le_add_left 1 _
  have hS0 : 0 < S := by linarith
  have hW0 : 0 < W := by linarith
  obtain ⟨hlow, hhigh⟩ := momentOrder_spec hS hW
  rw [← hkdef] at hlow hhigh
  set NA := ⌊S * (1 + η)⌋₊ with hNAdef
  have hNA : (NA : ℝ) ≤ 2 * S := by
    have := Nat.floor_le (show 0 ≤ S * (1 + η) by positivity)
    nlinarith
  have hNA1 : 1 ≤ NA := Nat.le_floor (by push_cast; nlinarith)
  have hcard : (B.card : ℝ) ≤ 2 * S := by
    have := Finset.card_le_card hB
    rw [Nat.card_Icc, add_tsub_cancel_right] at this
    exact (by exact_mod_cast this : (B.card : ℝ) ≤ NA).trans hNA
  have hV : 0 < S ^ (1 - α) := Real.rpow_pos_of_pos hS0 _
  have hbase := measureReal_shortExceptional_le hBprime hB hk hW0.le hV
  refine hbase.trans ?_
  -- the pieces
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hNAk : ((NA ^ k : ℕ) : ℝ) ≤ 2 ^ k * S ^ 2 * W := by
    push_cast
    calc (NA : ℝ) ^ k ≤ (2 * S) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hNA k
      _ = 2 ^ k * S ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (W * S ^ 2) := by gcongr
      _ = 2 ^ k * S ^ 2 * W := by ring
  have hNAk1 : (1 : ℝ) ≤ ((NA ^ k : ℕ) : ℝ) := by
    have : 1 ≤ NA ^ k := Nat.one_le_pow _ _ hNA1
    exact_mod_cast this
  have hlogNA : Real.log ((NA ^ k : ℕ) : ℝ) ≤ k * Real.log (2 * S) := by
    push_cast
    rw [Real.log_pow]
    have hNA0 : (0 : ℝ) < NA := by exact_mod_cast hNA1
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hNA0 hNA) hk0.le
  have hlog0 : 0 ≤ Real.log ((NA ^ k : ℕ) : ℝ) := Real.log_nonneg hNAk1
  have hmoment : ((k : ℝ) ^ k * (B.card : ℝ) ^ k) / (S ^ (1 - α)) ^ (2 * k)
      ≤ (2 * k : ℝ) ^ k * W ^ (-(1 - 2 * α)) := by
    have h1 : (k : ℝ) ^ k * (B.card : ℝ) ^ k ≤ (2 * k : ℝ) ^ k * S ^ k := by
      have : (B.card : ℝ) ^ k ≤ (2 * S) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard k
      calc (k : ℝ) ^ k * (B.card : ℝ) ^ k ≤ (k : ℝ) ^ k * (2 * S) ^ k :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = (2 * k : ℝ) ^ k * S ^ k := by rw [mul_pow, mul_pow]; ring
    have hVk : (S ^ (1 - α)) ^ (2 * k) = S ^ k * S ^ ((k : ℝ) * (1 - 2 * α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le, ← Real.rpow_natCast S k,
        ← Real.rpow_add hS0]
      congr 1; push_cast; ring
    have hSk : W ^ (1 - 2 * α) ≤ S ^ ((k : ℝ) * (1 - 2 * α)) := by
      have hW' : W ≤ S ^ ((k : ℝ) - 1) := by
        rw [show ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub hk]; ring,
          Real.rpow_natCast]
        exact hlow
      have hmono : S ^ ((k : ℝ) - 1) ≤ S ^ (k : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hS.le (by linarith)
      calc W ^ (1 - 2 * α) ≤ (S ^ (k : ℝ)) ^ (1 - 2 * α) :=
            Real.rpow_le_rpow hW0.le (hW'.trans hmono) (by linarith)
        _ = S ^ ((k : ℝ) * (1 - 2 * α)) := by rw [← Real.rpow_mul hS0.le]
    have hWp : 0 < W ^ (1 - 2 * α) := Real.rpow_pos_of_pos hW0 _
    rw [hVk, Real.rpow_neg hW0.le, div_le_iff₀ (by positivity)]
    calc (k : ℝ) ^ k * (B.card : ℝ) ^ k ≤ (2 * k : ℝ) ^ k * S ^ k := h1
      _ = (2 * k : ℝ) ^ k * (W ^ (1 - 2 * α))⁻¹ * (S ^ k * W ^ (1 - 2 * α)) := by
          field_simp
      _ ≤ (2 * k : ℝ) ^ k * (W ^ (1 - 2 * α))⁻¹ * (S ^ k * S ^ ((k : ℝ) * (1 - 2 * α))) := by
          gcongr
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hlog2S : 0 < Real.log (2 * S) := Real.log_pos (by linarith)
  set Λ := 1 + (k : ℝ) * Real.log (2 * S) with hΛ
  have hΛ1 : 1 ≤ Λ := by have := mul_pos hk0 hlog2S; rw [hΛ]; linarith
  have hfirst : 2 * Real.pi * W + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ))
      ≤ 2 * Real.pi * W + 4 * (2 ^ k * S ^ 2 * W) * Λ := by
    have : 1 + Real.log ((NA ^ k : ℕ) : ℝ) ≤ Λ := by rw [hΛ]; linarith
    gcongr
  have h2k : (1 : ℝ) ≤ 2 ^ k * S ^ 2 * Λ := by
    have a : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have b : (1 : ℝ) ≤ S ^ 2 := one_le_pow₀ hS.le
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ 2 ^ k * S ^ 2 * Λ := by gcongr
  have hcoef : (2 * Real.pi)⁻¹ * 2 * (2 * Real.pi * W + 4 * (2 ^ k * S ^ 2 * W) * Λ)
      ≤ 4 * (2 ^ k * S ^ 2 * Λ) * W := by
    have hid : (2 * Real.pi)⁻¹ * 2 * (2 * Real.pi * W + 4 * (2 ^ k * S ^ 2 * W) * Λ)
        = 2 * W + (4 / Real.pi) * (2 ^ k * S ^ 2 * Λ) * W := by
      field_simp
    rw [hid]
    have h4pi : 4 / Real.pi ≤ 2 := by rw [div_le_iff₀ hpi0]; linarith
    have hX : 0 ≤ 2 ^ k * S ^ 2 * Λ * W := by positivity
    nlinarith
  have hWpow : W * W ^ (-(1 - 2 * α)) = W ^ (2 * α) := by
    have h := Real.rpow_add hW0 1 (-(1 - 2 * α))
    rw [Real.rpow_one, show (1 : ℝ) + -(1 - 2 * α) = 2 * α by ring] at h
    exact h.symm
  have hm0 : 0 ≤ ((k : ℝ) ^ k * (B.card : ℝ) ^ k) / (S ^ (1 - α)) ^ (2 * k) := by positivity
  calc (2 * Real.pi)⁻¹ * (2 * ((2 * Real.pi * W
          + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * ((k : ℝ) ^ k * (B.card : ℝ) ^ k)) / (S ^ (1 - α)) ^ (2 * k))
      = (2 * Real.pi)⁻¹ * 2 * (2 * Real.pi * W
          + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * (((k : ℝ) ^ k * (B.card : ℝ) ^ k) / (S ^ (1 - α)) ^ (2 * k)) := by ring
    _ ≤ (2 * Real.pi)⁻¹ * 2 * (2 * Real.pi * W + 4 * (2 ^ k * S ^ 2 * W) * Λ)
          * ((2 * k : ℝ) ^ k * W ^ (-(1 - 2 * α))) := by
        gcongr
    _ ≤ 4 * (2 ^ k * S ^ 2 * Λ) * W * ((2 * k : ℝ) ^ k * W ^ (-(1 - 2 * α))) := by
        gcongr
    _ = 4 * (W * W ^ (-(1 - 2 * α))) * S ^ 2 * Λ * (2 ^ k * (2 * k : ℝ) ^ k) := by ring
    _ = 4 * W ^ (2 * α) * S ^ 2 * Λ * (4 * (k : ℝ)) ^ k := by
        rw [hWpow, ← mul_pow]; ring

/-- **The exceptional set of the last range.**  Every frequency outside the union of the
all-small sets has a large block in the last range; each block is paid by the moment method with
`S ≤ Q_K` and `k ≤ k* = ⌈log W/log R_K⌉ + 1`. -/
theorem measureReal_rangeLadder_exceptional_le {ν : ℝ} (hν : 2 ≤ ν) (K : ℕ) {W w₀ : ℝ}
    (hW : 1 ≤ W) :
    volume.real (annulusLarge (rangeUnionSmall (rangeLadderP ν) (rangeLadderR ν) (rangeLadderEta ν)
        (rangeLadderSteps ν) (powerThreshold (rangeLadderR ν) (rangeLadderEta ν) rangeLadderAlpha) W
        (K + 1)) W w₀)
      ≤ rangeLadderSteps ν K * (4 * W ^ (2 * rangeLadderAlpha K) * rangeLadderTopReal ν K ^ 2
          * (1 + (⌈Real.log W / Real.log (rangeLadderR ν K)⌉₊ + 1 : ℕ)
              * Real.log (2 * rangeLadderTopReal ν K))
          * (4 * ((⌈Real.log W / Real.log (rangeLadderR ν K)⌉₊ + 1 : ℕ) : ℝ))
              ^ (⌈Real.log W / Real.log (rangeLadderR ν K)⌉₊ + 1)) := by
  have hν0 : 0 < ν := by linarith
  set V := powerThreshold (rangeLadderR ν) (rangeLadderEta ν) rangeLadderAlpha with hVdef
  have hsub := annulusLarge_rangeUnionSmall_subset (rangeLadderP ν) (rangeLadderR ν)
    (rangeLadderEta ν) (rangeLadderSteps ν) V W w₀ (Nat.lt_succ_self K)
  have hfin : volume (annulusLarge (rangeAllSmall (rangeLadderP ν) (rangeLadderR ν)
      (rangeLadderEta ν) (rangeLadderSteps ν) V W K) W w₀) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (annulusLarge_subset _ W w₀)) ?_)
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  refine (measureReal_mono hsub hfin).trans ?_
  refine (measureReal_annulusLarge_le (rangeLadderP ν K) (rangeLadderR ν K) (rangeLadderEta ν K)
    (rangeLadderSteps ν K) (V K) W w₀).trans ?_
  set k := ⌈Real.log W / Real.log (rangeLadderR ν K)⌉₊ + 1 with hkdef
  set Q := rangeLadderTopReal ν K with hQdef
  have hR1 := one_lt_rangeLadderR hν0 K
  have hη := rangeLadderEta_pos ν K
  have hη1 := rangeLadderEta_le_one hν0.le K
  have hα : rangeLadderAlpha K < 1 / 2 := by
    rw [rangeLadderAlpha]; have : (0 : ℝ) ≤ 1 / (8 * 2 ^ K) := by positivity
    linarith
  have hbound : ∀ r ∈ Finset.range (rangeLadderSteps ν K),
      volume.real (shortExceptional (geomBlock (rangeLadderP ν K) (rangeLadderR ν K)
          (1 + rangeLadderEta ν K) r) W (V K r))
        ≤ 4 * W ^ (2 * rangeLadderAlpha K) * Q ^ 2 * (1 + (k : ℝ) * Real.log (2 * Q))
            * (4 * (k : ℝ)) ^ k := by
    intro r hr
    set S := rangeLadderR ν K * (1 + rangeLadderEta ν K) ^ r with hSdef
    have hS1 : 1 < S := by
      have : rangeLadderR ν K ≤ S := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by linarith))
      linarith
    have hSQ : S ≤ Q := by
      rw [hQdef, rangeLadderTopReal]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hr).le) (by linarith)
    have hBsub : geomBlock (rangeLadderP ν K) (rangeLadderR ν K) (1 + rangeLadderEta ν K) r
        ⊆ Finset.Icc 1 ⌊S * (1 + rangeLadderEta ν K)⌋₊ := by
      have h := geomBlock_subset_Icc_one (P := rangeLadderP ν K) (by linarith : 0 < rangeLadderR ν K)
        hη.le r
      rwa [pow_succ, ← mul_assoc] at h
    have hVr : V K r = S ^ (1 - rangeLadderAlpha K) := rfl
    rw [hVr]
    refine (measureReal_shortExceptional_power_le (fun p hp => rangeLadderP_prime ν K p
      (geomBlock_subset _ _ _ _ hp)) hS1 hη.le hη1 hBsub hW hα).trans ?_
    set kr := ⌈Real.log W / Real.log S⌉₊ + 1 with hkrdef
    have hkr : kr ≤ k := by
      refine Nat.add_le_add_right (Nat.ceil_mono ?_) 1
      have hlogR : 0 < Real.log (rangeLadderR ν K) := Real.log_pos hR1
      have hlogRS : Real.log (rangeLadderR ν K) ≤ Real.log S :=
        Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith)
          (one_le_pow₀ (by linarith)))
      exact div_le_div_of_nonneg_left (Real.log_nonneg hW) hlogR hlogRS
    have hkrR : (kr : ℝ) ≤ k := by exact_mod_cast hkr
    have hkr1 : (1 : ℝ) ≤ kr := by exact_mod_cast Nat.le_add_left 1 _
    have hlog2S : 0 ≤ Real.log (2 * S) := Real.log_nonneg (by linarith)
    have hlog2SQ : Real.log (2 * S) ≤ Real.log (2 * Q) := Real.log_le_log (by linarith) (by linarith)
    have hWa : 0 ≤ W ^ (2 * rangeLadderAlpha K) := Real.rpow_nonneg (by linarith) _
    have h1 : 1 + (kr : ℝ) * Real.log (2 * S) ≤ 1 + (k : ℝ) * Real.log (2 * Q) := by
      have := mul_le_mul hkrR hlog2SQ hlog2S (by linarith)
      linarith
    have h2 : (4 * (kr : ℝ)) ^ kr ≤ (4 * (k : ℝ)) ^ k :=
      (pow_le_pow_left₀ (by positivity) (by linarith) kr).trans
        (pow_le_pow_right₀ (by linarith) hkr)
    have h3 : S ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by linarith) hSQ 2
    have h0 : 0 ≤ 1 + (kr : ℝ) * Real.log (2 * S) := by positivity
    have hQ1 : 0 ≤ 1 + (k : ℝ) * Real.log (2 * Q) :=
      add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (hlog2S.trans hlog2SQ))
    have hA0 : 0 ≤ 4 * W ^ (2 * rangeLadderAlpha K) * Q ^ 2 := by positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h3 (by positivity)) h1 h0 hA0) h2
      (by positivity) (mul_nonneg hA0 hQ1)
  refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

open Classical in
/-- The last range of the ladder: the least `k` with `ν_k ≥ T`. -/
def rangeLadderLast (ν T : ℝ) : ℕ :=
  if h : ∃ k, T ≤ rangeLadderNu ν k then Nat.find h else 0

theorem exists_le_rangeLadderNu {ν : ℝ} (hν : 2 ≤ ν) (T : ℝ) : ∃ k, T ≤ rangeLadderNu ν k := by
  refine ⟨⌈T⌉₊, ?_⟩
  set k := ⌈T⌉₊
  have h1 : T ≤ (k : ℝ) := Nat.le_ceil T
  have h2 : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self
  have h3 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 ^ k) :=
    pow_le_pow_right₀ (by norm_num) (Nat.lt_two_pow_self).le
  have h4 : (2 : ℝ) ^ (2 ^ k) ≤ ν ^ (2 ^ k) := pow_le_pow_left₀ (by norm_num) hν _
  rw [rangeLadderNu]
  linarith

/-- The last range reaches `T` and stays below `T²`. -/
theorem rangeLadderLast_spec {ν T : ℝ} (hν : 2 ≤ ν) (hνT : ν ≤ T) :
    T ≤ rangeLadderNu ν (rangeLadderLast ν T) ∧ rangeLadderNu ν (rangeLadderLast ν T) ≤ T ^ 2 := by
  classical
  have hex := exists_le_rangeLadderNu hν T
  have hK : rangeLadderLast ν T = Nat.find hex := by
    rw [rangeLadderLast, dif_pos hex]
  rw [hK]
  refine ⟨Nat.find_spec hex, ?_⟩
  have hT1 : 1 ≤ T := by linarith
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, rangeLadderNu, pow_zero, pow_one]
    nlinarith
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [not_le] at hmin
    rw [hk, rangeLadderNu_succ]
    have h0 : 0 ≤ rangeLadderNu ν k := (rangeLadderNu_pos (by linarith) k).le
    nlinarith

/-- The number of ranges is logarithmic in `log T`: `2^K ≤ (log T)/2`. -/
theorem two_pow_rangeLadderLast_le {ν T : ℝ} (hν : 3000 ≤ ν) (hνT : ν ≤ T) :
    (2 : ℝ) ^ rangeLadderLast ν T ≤ Real.log T / 2 := by
  have hν0 : 0 < ν := by linarith
  obtain ⟨-, hup⟩ := rangeLadderLast_spec (by linarith) hνT
  have hlog := Real.log_le_log (rangeLadderNu_pos hν0 _) hup
  rw [log_rangeLadderNu, Real.log_pow] at hlog
  have h4 := log_ge_four_of_ge hν
  have hg : (0 : ℝ) ≤ 2 ^ rangeLadderLast ν T := by positivity
  push_cast at hlog
  nlinarith

/-- **The numerical core of the exceptional-set bound.** -/
theorem rangeLadder_exceptional_exponent_le {T lam : ℝ} (hT : 3000 ≤ T) (hlo : T ^ 40 / 2 ≤ lam) :
    -(lam / (2 * Real.log T)) + 70 * T ^ 10
        + (lam / T ^ 4 + 2) * (3 + 36 * Real.log T)
      ≤ -(T ^ 40 / (8 * Real.log T)) := by
  set u := Real.log T with hu
  have hT1 : 1 ≤ T := by linarith
  have hu4 : 4 ≤ u := log_ge_four_of_ge hT
  have hu0 : 0 < u := by linarith
  have huT : u ≤ T := by have := Real.log_le_sub_one_of_pos (by linarith : 0 < T); linarith
  have hu2 : u ^ 2 ≤ 4 * T := log_sq_le_four_mul hT1
  have hT4 : 0 < T ^ 4 := by positivity
  have hlam0 : 0 ≤ lam := le_trans (by positivity) hlo
  -- claim A
  have hA : lam / T ^ 4 * (3 + 36 * u) ≤ lam / (8 * u) := by
    have hkey : 8 * u * (3 + 36 * u) ≤ T ^ 4 := by
      have h3 : 1176 ≤ T ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3000) hT 3
        have h3' : (1176 : ℝ) ≤ 3000 ^ 3 := by norm_num
        linarith
      have : T ^ 4 = T * T ^ 3 := by ring
      nlinarith
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hT4 (by positivity)]
    have := mul_le_mul_of_nonneg_left hkey hlam0
    nlinarith
  -- claim B
  have hB : 70 * T ^ 10 + 2 * (3 + 36 * u) ≤ lam / (8 * u) := by
    rw [le_div_iff₀ (by positivity)]
    have h10 : 1 ≤ T ^ 10 := one_le_pow₀ hT1
    have hT10 : T ≤ T ^ 10 := by
      calc T = T ^ 1 := (pow_one T).symm
        _ ≤ T ^ 10 := pow_le_pow_right₀ hT1 (by norm_num)
    have hstep : (70 * T ^ 10 + 2 * (3 + 36 * u)) * (8 * u) ≤ 1248 * T ^ 11 := by
      have : 70 * T ^ 10 + 2 * (3 + 36 * u) ≤ 78 * T ^ 10 := by nlinarith
      have h11 : T ^ 11 = T ^ 10 * T := by ring
      nlinarith
    have hbig : 1248 * T ^ 11 ≤ T ^ 40 / 2 := by
      have h29 : 2496 ≤ T ^ 29 := by
        have : (3000 : ℝ) ^ 29 ≤ T ^ 29 := pow_le_pow_left₀ (by norm_num) hT 29
        have h3 : (2496 : ℝ) ≤ 3000 ^ 29 := by norm_num
        linarith
      have : T ^ 40 = T ^ 11 * T ^ 29 := by ring
      have h11 : 0 ≤ T ^ 11 := by positivity
      nlinarith
    linarith
  have hsplit : lam / (2 * u) = lam / (8 * u) + lam / (8 * u) + lam / (4 * u) := by
    field_simp; ring
  have hfin : T ^ 40 / (8 * u) ≤ lam / (4 * u) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hexp : (lam / T ^ 4 + 2) * (3 + 36 * u) = lam / T ^ 4 * (3 + 36 * u) + 2 * (3 + 36 * u) := by
    ring
  rw [hexp, hsplit]
  linarith

/-- **The exceptional set of the ladder is small.**  With the last range at scale `ν_K ∈ [T, T²]`
and `log M ≍ T⁴⁰`, `√W·|U| ≤ M·exp(−T⁴⁰/(8 log T))`. -/
theorem sqrt_mul_measureReal_rangeLadder_exceptional_le {ν T : ℝ} (hν : 3000 ≤ ν) (hνT : ν ≤ T)
    {M : ℕ} (hMlo : T ^ 40 / 2 ≤ Real.log M) (hMhi : Real.log M ≤ T ^ 40) {W w₀ : ℝ}
    (hW : 1 ≤ W) (hWM : W ≤ M) :
    Real.sqrt W * volume.real (annulusLarge (rangeUnionSmall (rangeLadderP ν) (rangeLadderR ν)
        (rangeLadderEta ν) (rangeLadderSteps ν)
        (powerThreshold (rangeLadderR ν) (rangeLadderEta ν) rangeLadderAlpha) W
        (rangeLadderLast ν T + 1)) W w₀)
      ≤ M * Real.exp (-(T ^ 40 / (8 * Real.log T))) := by
  set K := rangeLadderLast ν T with hKdef
  have hν0 : 0 < ν := by linarith
  have hT : 3000 ≤ T := le_trans hν hνT
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  set u := Real.log T with hudef
  have hu4 : 4 ≤ u := log_ge_four_of_ge hT
  have huT : u ≤ T := by have := Real.log_le_sub_one_of_pos hT0; linarith
  set lam := Real.log (M : ℝ) with hlam
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hMlo
  have hM1 : (1 : ℝ) < M := by
    by_contra hcon
    rw [not_lt] at hcon
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have : Real.log (M : ℝ) ≤ 0 := Real.log_nonpos hM0 hcon
    linarith
  have hM0 : (0 : ℝ) < M := by linarith
  obtain ⟨htlo, hthi⟩ := rangeLadderLast_spec (by linarith) hνT
  rw [← hKdef] at htlo hthi
  set t := rangeLadderNu ν K with htdef
  have ht0 : 0 < t := by linarith
  have hg := two_pow_rangeLadderLast_le hν hνT
  rw [← hKdef, ← hudef] at hg
  set g : ℝ := 2 ^ K with hgdef
  have hg1 : 1 ≤ g := one_le_pow₀ (by norm_num)
  have hbase := measureReal_rangeLadder_exceptional_le (by linarith : (2 : ℝ) ≤ ν) K
    (w₀ := w₀) hW
  set k := ⌈Real.log W / Real.log (rangeLadderR ν K)⌉₊ + 1 with hkdef
  set Q := rangeLadderTopReal ν K with hQdef
  set L := (rangeLadderSteps ν K : ℝ) with hLdef
  -- the steps
  have hL : L ≤ 3 * T ^ 10 * u * Real.exp T := by
    have h := rangeLadderSteps_le_exp (by linarith : (1 : ℝ) ≤ ν) K
    rw [← htdef, ← hgdef] at h
    have h5 : t ^ 5 ≤ T ^ 10 := by
      calc t ^ 5 ≤ (T ^ 2) ^ 5 := pow_le_pow_left₀ ht0.le hthi 5
        _ = T ^ 10 := by ring
    have hgu : g ≤ u := by linarith
    have hν' : Real.exp ν ≤ Real.exp T := Real.exp_le_exp.mpr hνT
    calc L ≤ 3 * t ^ 5 * g * Real.exp ν := h
      _ ≤ 3 * T ^ 10 * u * Real.exp T := by gcongr
  -- the top
  have hQlog : Real.log Q ≤ 3 * T ^ 10 := by
    have h := log_rangeLadderTopReal_le (by linarith : (2 : ℝ) ≤ ν) K
    rw [← htdef] at h
    have h5 : t ^ 5 ≤ T ^ 10 := by
      calc t ^ 5 ≤ (T ^ 2) ^ 5 := pow_le_pow_left₀ ht0.le hthi 5
        _ = T ^ 10 := by ring
    linarith
  have hQ0 : 0 < Q := rangeLadderTopReal_pos hν0 K
  have hQ2 : Q ^ 2 ≤ Real.exp (6 * T ^ 10) := by
    have : Q ≤ Real.exp (3 * T ^ 10) := by
      rw [← Real.exp_log hQ0]; exact Real.exp_le_exp.mpr hQlog
    calc Q ^ 2 ≤ Real.exp (3 * T ^ 10) ^ 2 := pow_le_pow_left₀ hQ0.le this 2
      _ = Real.exp (6 * T ^ 10) := by rw [← Real.exp_nat_mul]; ring_nf
  have hQ1 : 1 ≤ Q := by
    have h := log_rangeLadderTopReal_ge hν0.le hν0 K
    have : 0 ≤ Real.log Q := le_trans (by positivity) h
    rwa [Real.log_nonneg_iff hQ0] at this
  have hlog2Q : Real.log (2 * Q) ≤ 1 + 3 * T ^ 10 := by
    rw [Real.log_mul (by norm_num) hQ0.ne']
    have := Real.log_two_lt_d9
    linarith
  have hlog2Q0 : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
  -- the moment order
  set X := lam / T ^ 4 + 2 with hXdef
  have hk : (k : ℝ) ≤ X := by
    have hR := log_rangeLadderR_ge ν K
    rw [← htdef] at hR
    have ht4 : T ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hT0.le htlo 4
    have hlogR : 0 < Real.log (rangeLadderR ν K) := by
      have : 0 < T ^ 4 := by positivity
      linarith
    have hlogW : Real.log W ≤ lam := Real.log_le_log (by linarith) hWM
    have hlogW0 : 0 ≤ Real.log W := Real.log_nonneg hW
    have hratio : Real.log W / Real.log (rangeLadderR ν K) ≤ lam / T ^ 4 :=
      div_le_div₀ hlam0.le hlogW (by positivity) (by linarith)
    have hc := Nat.ceil_lt_add_one (div_nonneg hlogW0 hlogR.le)
    rw [hkdef]
    push_cast
    linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.le_add_left 1 _
  have hX1 : 1 ≤ X := by linarith
  have hXup : X ≤ 3 * T ^ 36 := by
    have : lam / T ^ 4 ≤ T ^ 36 := by
      rw [div_le_iff₀ (by positivity)]
      calc lam ≤ T ^ 40 := hMhi
        _ = T ^ 36 * T ^ 4 := by ring
    have : 1 ≤ T ^ 36 := one_le_pow₀ hT1
    linarith
  have hpowk : (4 * (k : ℝ)) ^ k ≤ Real.exp (X * (3 + 36 * u)) := by
    rw [pow_eq_exp_nat_mul_log (by positivity)]
    refine Real.exp_le_exp.mpr ?_
    have hlog4k : Real.log (4 * (k : ℝ)) ≤ 3 + 36 * u := by
      have h4X : 4 * (k : ℝ) ≤ Real.exp 3 * T ^ 36 := by
        have he3 : (12 : ℝ) ≤ Real.exp 3 := by
          have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
          have h : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
          rw [h]
          calc (12 : ℝ) ≤ 2.7 ^ 3 := by norm_num
            _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he 3
        have : 0 ≤ T ^ 36 := by positivity
        nlinarith
      have := Real.log_le_log (by positivity) h4X
      rwa [Real.log_mul (Real.exp_pos 3).ne' (by positivity), Real.log_exp, Real.log_pow] at this
    have hlog4k0 : 0 ≤ Real.log (4 * (k : ℝ)) := Real.log_nonneg (by linarith)
    exact mul_le_mul hk hlog4k hlog4k0 (by linarith)
  -- the polynomial factors
  have hpoly : 4 * L * Q ^ 2 * (1 + (k : ℝ) * Real.log (2 * Q)) ≤ Real.exp (70 * T ^ 10) := by
    have h1 : 1 + (k : ℝ) * Real.log (2 * Q) ≤ 13 * T ^ 46 := by
      have : (k : ℝ) * Real.log (2 * Q) ≤ (3 * T ^ 36) * (1 + 3 * T ^ 10) :=
        mul_le_mul (hk.trans hXup) hlog2Q hlog2Q0 (by positivity)
      have h36 : 1 ≤ T ^ 36 := one_le_pow₀ hT1
      have h46 : T ^ 46 = T ^ 36 * T ^ 10 := by ring
      have h10 : 1 ≤ T ^ 10 := one_le_pow₀ hT1
      nlinarith
    have hL0 : 0 ≤ L := Nat.cast_nonneg _
    have h2 : 4 * L * Q ^ 2 * (1 + (k : ℝ) * Real.log (2 * Q))
        ≤ 4 * (3 * T ^ 10 * u * Real.exp T) * Real.exp (6 * T ^ 10) * (13 * T ^ 46) := by
      have : 0 ≤ 1 + (k : ℝ) * Real.log (2 * Q) := by positivity
      gcongr
    refine h2.trans ?_
    have hT57 : T ^ 56 * u ≤ Real.exp (57 * T) := by
      have hTe : T ≤ Real.exp T := by have := Real.add_one_le_exp T; linarith
      have : T ^ 57 ≤ Real.exp T ^ 57 := pow_le_pow_left₀ hT0.le hTe 57
      rw [← Real.exp_nat_mul] at this
      have h56 : T ^ 56 * u ≤ T ^ 56 * T := mul_le_mul_of_nonneg_left huT (by positivity)
      have : T ^ 56 * T = T ^ 57 := by ring
      push_cast at *
      linarith
    have h156 : (156 : ℝ) ≤ Real.exp 6 := by
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have h : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      calc (156 : ℝ) ≤ 2.7 ^ 6 := by norm_num
        _ ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) he 6
    calc 4 * (3 * T ^ 10 * u * Real.exp T) * Real.exp (6 * T ^ 10) * (13 * T ^ 46)
        = 156 * (T ^ 56 * u) * Real.exp T * Real.exp (6 * T ^ 10) := by ring
      _ ≤ Real.exp 6 * Real.exp (57 * T) * Real.exp T * Real.exp (6 * T ^ 10) := by gcongr
      _ = Real.exp (6 + 58 * T + 6 * T ^ 10) := by
          simp only [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (70 * T ^ 10) := by
          refine Real.exp_le_exp.mpr ?_
          have h10 : T ≤ T ^ 10 := by
            calc T = T ^ 1 := (pow_one T).symm
              _ ≤ T ^ 10 := pow_le_pow_right₀ hT1 (by norm_num)
          have : 1 ≤ T ^ 10 := one_le_pow₀ hT1
          linarith
  -- the frequency factor
  have hWfac : Real.sqrt W * W ^ (2 * rangeLadderAlpha K) ≤ M * Real.exp (-(lam / (2 * u))) := by
    have hα : 1 / 2 + 2 * rangeLadderAlpha K = 1 - 1 / (4 * g) := by
      rw [rangeLadderAlpha, hgdef]; field_simp; ring
    have hW0 : 0 < W := by linarith
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hW0, hα]
    have hexp0 : 0 ≤ 1 - 1 / (4 * g) := by
      have : 1 / (4 * g) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith
    calc W ^ (1 - 1 / (4 * g)) ≤ (M : ℝ) ^ (1 - 1 / (4 * g)) :=
          Real.rpow_le_rpow hW0.le hWM hexp0
      _ = M * Real.exp (-(lam / (4 * g))) := by
          rw [Real.rpow_sub hM0, Real.rpow_one, Real.rpow_def_of_pos hM0, div_eq_mul_inv,
            Real.exp_neg]
          congr 2
          rw [hlam]; field_simp
      _ ≤ M * Real.exp (-(lam / (2 * u))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) hM0.le
          exact div_le_div_of_nonneg_left hlam0.le (by positivity) (by linarith)
  have hcore := rangeLadder_exceptional_exponent_le hT hMlo
  have hsq0 : 0 ≤ Real.sqrt W := Real.sqrt_nonneg W
  have hWa0 : 0 ≤ W ^ (2 * rangeLadderAlpha K) := Real.rpow_nonneg (by linarith) _
  calc Real.sqrt W * volume.real (annulusLarge (rangeUnionSmall (rangeLadderP ν) (rangeLadderR ν)
        (rangeLadderEta ν) (rangeLadderSteps ν)
        (powerThreshold (rangeLadderR ν) (rangeLadderEta ν) rangeLadderAlpha) W (K + 1)) W w₀)
      ≤ Real.sqrt W * (L * (4 * W ^ (2 * rangeLadderAlpha K) * Q ^ 2
          * (1 + (k : ℝ) * Real.log (2 * Q)) * (4 * (k : ℝ)) ^ k)) :=
        mul_le_mul_of_nonneg_left hbase hsq0
    _ = (Real.sqrt W * W ^ (2 * rangeLadderAlpha K))
          * ((4 * L * Q ^ 2 * (1 + (k : ℝ) * Real.log (2 * Q))) * (4 * (k : ℝ)) ^ k) := by ring
    _ ≤ (M * Real.exp (-(lam / (2 * u))))
          * (Real.exp (70 * T ^ 10) * Real.exp (X * (3 + 36 * u))) := by
        gcongr
    _ = M * Real.exp (-(lam / (2 * u)) + 70 * T ^ 10 + X * (3 + 36 * u)) := by
        rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ M * Real.exp (-(T ^ 40 / (8 * u))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcore) hM0.le

end

end RHTower.Sieve
