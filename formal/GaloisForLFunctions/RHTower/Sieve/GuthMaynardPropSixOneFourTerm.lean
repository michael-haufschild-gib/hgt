import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSixOne

/-!
# Guth–Maynard (6.4) with the fourth Heath-Brown term

The corpus Heath-Brown bound valid at **every** block length (`hbPairSum_Ioc_le_anyBlock`) carries,
besides Heath-Brown's three terms, a fourth term `|W|^{3/2} M²`.  This module runs the assembly of
`prop61_abstract` with that extra term present:

`Y ≤ C' (W² M^k + W M^{2k} + W^{5/4} T^{1/2} M^k + W^{3/2} M^{2k})`

costs exactly one extra summand in (6.4),

`S₂ ≤ C C'^{1/k} (N²W² + TN W^{2−1/k} + N² W^{2−3/(4k)} T^{1/(2k)} + TN W^{2−1/(2k)})`,

because `(W²)^{1−1/k}(W^{3/2}M^{2k})^{1/k} = W^{2−1/(2k)} M²` and `N²M ≤ TN`.  Since
`W^{2−1/k} ≤ W^{2−1/(2k)}` for `W ≥ 1`, the fourth summand absorbs the second: the four-term input
gives Proposition 6.1 with the second exponent `2 − 1/k` replaced by `2 − 1/(2k)`
(`prop61_abstract4_absorbed`).
-/

set_option autoImplicit false

namespace RHTower.GuthMaynard

noncomputable section

/-- `(a+b+c+d)^{1/k} ≤ a^{1/k}+b^{1/k}+c^{1/k}+d^{1/k}` for nonnegative reals and `k ≥ 1`. -/
theorem rpow_inv_add_four_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    {k : ℕ} (hk : 1 ≤ k) :
    (a + b + c + d) ^ (1 / (k : ℝ)) ≤
      a ^ (1 / (k : ℝ)) + b ^ (1 / (k : ℝ)) + c ^ (1 / (k : ℝ)) + d ^ (1 / (k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hp1 : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hkpos]; exact_mod_cast hk
  calc (a + b + c + d) ^ (1 / (k : ℝ))
      ≤ (a + b + c) ^ (1 / (k : ℝ)) + d ^ (1 / (k : ℝ)) :=
        Real.rpow_add_le_add_rpow (by positivity) hd hp0 hp1
    _ ≤ _ := by
        gcongr
        exact rpow_inv_add_three_le ha hb hc hk

/-- **Guth–Maynard (6.4) with the fourth Heath-Brown term.**  From (6.1) `S₂ ≤ C (N²/M) X`,
(6.2) `X ≤ (W²)^{1−1/k} Y^{1/k}`, the four-term (6.3) and `M ≤ T/N`:
`S₂ ≤ C C'^{1/k} (N²W² + TN W^{2−1/k} + N² W^{2−3/(4k)} T^{1/(2k)} + TN W^{2−1/(2k)})`. -/
theorem prop61_abstract4 {W N M T S₂ X Y C C' : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hW : 0 < W) (hN : 0 < N) (hM : 0 < M) (hT : 0 < T) (hMT : M ≤ T / N)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hY0 : 0 ≤ Y)
    (h61 : S₂ ≤ C * (N ^ 2 / M) * X)
    (h62 : X ≤ (W ^ 2) ^ (1 - 1 / (k : ℝ)) * Y ^ (1 / (k : ℝ)))
    (h63 : Y ≤ C' * (W ^ 2 * M ^ k + W * M ^ (2 * k)
      + W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k + W ^ ((3 : ℝ) / 2) * M ^ (2 * k))) :
    S₂ ≤ C * C' ^ (1 / (k : ℝ)) *
      (N ^ 2 * W ^ 2 + T * N * W ^ (2 - 1 / (k : ℝ))
        + N ^ 2 * W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))
        + T * N * W ^ (2 - 1 / (2 * (k : ℝ)))) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk0 : k ≠ 0 := by omega
  set κ : ℝ := (k : ℝ) with hκ
  have hκpos : 0 < κ := hkpos
  -- the `k`-th roots of the four factors
  have hMk : (M ^ k) ^ (1 / κ) = M := by
    rw [one_div, Real.pow_rpow_inv_natCast hM.le hk0]
  have hM2k : (M ^ (2 * k)) ^ (1 / κ) = M ^ 2 := by
    rw [pow_mul, one_div, Real.pow_rpow_inv_natCast (by positivity) hk0]
  have hW2κ : (W ^ 2) ^ (1 / κ) = W ^ (2 / κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    congr 1; push_cast; ring
  have hW54 : (W ^ ((5 : ℝ) / 4)) ^ (1 / κ) = W ^ (5 / (4 * κ)) := by
    rw [← Real.rpow_mul hW.le]
    congr 1; field_simp
  have hW32 : (W ^ ((3 : ℝ) / 2)) ^ (1 / κ) = W ^ (3 / (2 * κ)) := by
    rw [← Real.rpow_mul hW.le]
    congr 1; field_simp
  have hT12 : (T ^ ((1 : ℝ) / 2)) ^ (1 / κ) = T ^ (1 / (2 * κ)) := by
    rw [← Real.rpow_mul hT.le]
    congr 1; field_simp
  have hp1 : (W ^ 2 * M ^ k) ^ (1 / κ) = W ^ (2 / κ) * M := by
    rw [Real.mul_rpow (by positivity) (by positivity), hW2κ, hMk]
  have hp2 : (W * M ^ (2 * k)) ^ (1 / κ) = W ^ (1 / κ) * M ^ 2 := by
    rw [Real.mul_rpow hW.le (by positivity), hM2k]
  have hp3 : (W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k) ^ (1 / κ)
      = W ^ (5 / (4 * κ)) * T ^ (1 / (2 * κ)) * M := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      hW54, hT12, hMk]
  have hp4 : (W ^ ((3 : ℝ) / 2) * M ^ (2 * k)) ^ (1 / κ) = W ^ (3 / (2 * κ)) * M ^ 2 := by
    rw [Real.mul_rpow (by positivity) (by positivity), hW32, hM2k]
  -- `Y^{1/κ}`
  have hY' : Y ^ (1 / κ) ≤ C' ^ (1 / κ) *
      (W ^ (2 / κ) * M + W ^ (1 / κ) * M ^ 2 + W ^ (5 / (4 * κ)) * T ^ (1 / (2 * κ)) * M
        + W ^ (3 / (2 * κ)) * M ^ 2) := by
    calc Y ^ (1 / κ)
        ≤ (C' * (W ^ 2 * M ^ k + W * M ^ (2 * k)
            + W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k
            + W ^ ((3 : ℝ) / 2) * M ^ (2 * k))) ^ (1 / κ) :=
          Real.rpow_le_rpow hY0 h63 (by positivity)
      _ = C' ^ (1 / κ) * (W ^ 2 * M ^ k + W * M ^ (2 * k)
            + W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k
            + W ^ ((3 : ℝ) / 2) * M ^ (2 * k)) ^ (1 / κ) :=
          Real.mul_rpow hC' (by positivity)
      _ ≤ C' ^ (1 / κ) * ((W ^ 2 * M ^ k) ^ (1 / κ) + (W * M ^ (2 * k)) ^ (1 / κ)
            + (W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k) ^ (1 / κ)
            + (W ^ ((3 : ℝ) / 2) * M ^ (2 * k)) ^ (1 / κ)) := by
          gcongr
          exact rpow_inv_add_four_le (by positivity) (by positivity) (by positivity)
            (by positivity) hk
      _ = _ := by rw [hp1, hp2, hp3, hp4]
  -- Hölder with the powers of `W` combined
  have hW2 : (W ^ 2) ^ (1 - 1 / κ) = W ^ (2 - 2 / κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]; congr 1; push_cast; ring
  have hX' : X ≤ C' ^ (1 / κ) *
      (W ^ 2 * M + W ^ (2 - 1 / κ) * M ^ 2 + W ^ (2 - 3 / (4 * κ)) * T ^ (1 / (2 * κ)) * M
        + W ^ (2 - 1 / (2 * κ)) * M ^ 2) := by
    have hWa : W ^ (2 - 2 / κ) * W ^ (2 / κ) = W ^ 2 := by
      rw [← Real.rpow_add hW]; norm_num
    have hWb : W ^ (2 - 2 / κ) * W ^ (1 / κ) = W ^ (2 - 1 / κ) := by
      rw [← Real.rpow_add hW]; congr 1; ring
    have hWc : W ^ (2 - 2 / κ) * W ^ (5 / (4 * κ)) = W ^ (2 - 3 / (4 * κ)) := by
      rw [← Real.rpow_add hW]; congr 1; field_simp; ring
    have hWd : W ^ (2 - 2 / κ) * W ^ (3 / (2 * κ)) = W ^ (2 - 1 / (2 * κ)) := by
      rw [← Real.rpow_add hW]; congr 1; field_simp; ring
    calc X ≤ (W ^ 2) ^ (1 - 1 / κ) * Y ^ (1 / κ) := h62
      _ ≤ (W ^ 2) ^ (1 - 1 / κ) * (C' ^ (1 / κ) *
          (W ^ (2 / κ) * M + W ^ (1 / κ) * M ^ 2 + W ^ (5 / (4 * κ)) * T ^ (1 / (2 * κ)) * M
            + W ^ (3 / (2 * κ)) * M ^ 2)) :=
          mul_le_mul_of_nonneg_left hY' (by positivity)
      _ = C' ^ (1 / κ) * (W ^ (2 - 2 / κ) * W ^ (2 / κ) * M + W ^ (2 - 2 / κ) * W ^ (1 / κ) * M ^ 2
          + W ^ (2 - 2 / κ) * W ^ (5 / (4 * κ)) * T ^ (1 / (2 * κ)) * M
          + W ^ (2 - 2 / κ) * W ^ (3 / (2 * κ)) * M ^ 2) := by
          rw [hW2]; ring
      _ = _ := by rw [hWa, hWb, hWc, hWd]
  -- assemble with (6.1) and `M ≤ T/N`
  have hMT' : N ^ 2 * M ≤ T * N := by
    have := mul_le_mul_of_nonneg_left hMT (by positivity : (0 : ℝ) ≤ N ^ 2)
    calc N ^ 2 * M ≤ N ^ 2 * (T / N) := this
      _ = T * N := by field_simp
  have hcoef : 0 ≤ C * (N ^ 2 / M) := by positivity
  calc S₂ ≤ C * (N ^ 2 / M) * X := h61
    _ ≤ C * (N ^ 2 / M) * (C' ^ (1 / κ) *
        (W ^ 2 * M + W ^ (2 - 1 / κ) * M ^ 2 + W ^ (2 - 3 / (4 * κ)) * T ^ (1 / (2 * κ)) * M
          + W ^ (2 - 1 / (2 * κ)) * M ^ 2)) :=
        mul_le_mul_of_nonneg_left hX' hcoef
    _ = C * C' ^ (1 / κ) * (N ^ 2 * W ^ 2 + N ^ 2 * M * W ^ (2 - 1 / κ)
        + N ^ 2 * W ^ (2 - 3 / (4 * κ)) * T ^ (1 / (2 * κ))
        + N ^ 2 * M * W ^ (2 - 1 / (2 * κ))) := by
        field_simp
    _ ≤ C * C' ^ (1 / κ) * (N ^ 2 * W ^ 2 + T * N * W ^ (2 - 1 / κ)
        + N ^ 2 * W ^ (2 - 3 / (4 * κ)) * T ^ (1 / (2 * κ))
        + T * N * W ^ (2 - 1 / (2 * κ))) := by
        gcongr

/-- The second summand of (6.4) is absorbed by the fourth: for `W ≥ 1` and `k ≥ 1`,
`W^{2−1/k} ≤ W^{2−1/(2k)}`. -/
theorem rpow_two_sub_inv_le {W : ℝ} (hW : 1 ≤ W) {k : ℕ} (hk : 1 ≤ k) :
    W ^ (2 - 1 / (k : ℝ)) ≤ W ^ (2 - 1 / (2 * (k : ℝ))) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine Real.rpow_le_rpow_of_exponent_le hW ?_
  have h : 1 / (2 * (k : ℝ)) ≤ 1 / (k : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hkpos]; linarith
  linarith

/-- **Proposition 6.1 from the four-term Heath-Brown input.**  With the second exponent weakened
to `2 − 1/(2k)`:
`S₂ ≤ 2 C C'^{1/k} (N²W² + TN W^{2−1/(2k)} + N² W^{2−3/(4k)} T^{1/(2k)})`. -/
theorem prop61_abstract4_absorbed {W N M T S₂ X Y C C' : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hW : 1 ≤ W) (hN : 0 < N) (hM : 0 < M) (hT : 0 < T) (hMT : M ≤ T / N)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hY0 : 0 ≤ Y)
    (h61 : S₂ ≤ C * (N ^ 2 / M) * X)
    (h62 : X ≤ (W ^ 2) ^ (1 - 1 / (k : ℝ)) * Y ^ (1 / (k : ℝ)))
    (h63 : Y ≤ C' * (W ^ 2 * M ^ k + W * M ^ (2 * k)
      + W ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ^ k + W ^ ((3 : ℝ) / 2) * M ^ (2 * k))) :
    S₂ ≤ 2 * (C * C' ^ (1 / (k : ℝ))) *
      (N ^ 2 * W ^ 2 + T * N * W ^ (2 - 1 / (2 * (k : ℝ)))
        + N ^ 2 * W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))) := by
  have hW0 : 0 < W := by linarith
  have h := prop61_abstract4 hk hW0 hN hM hT hMT hC hC' hY0 h61 h62 h63
  have habs := rpow_two_sub_inv_le hW hk
  have hCC : 0 ≤ C * C' ^ (1 / (k : ℝ)) := by positivity
  have hA : (0 : ℝ) ≤ N ^ 2 * W ^ 2 := by positivity
  have hB : (0 : ℝ) ≤ N ^ 2 * W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) := by
    positivity
  have hTN : (0 : ℝ) ≤ T * N := by positivity
  have hxy := mul_le_mul_of_nonneg_left habs hTN
  have hstep : N ^ 2 * W ^ 2 + T * N * W ^ (2 - 1 / (k : ℝ))
        + N ^ 2 * W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))
        + T * N * W ^ (2 - 1 / (2 * (k : ℝ))) ≤
      2 * (N ^ 2 * W ^ 2 + T * N * W ^ (2 - 1 / (2 * (k : ℝ)))
        + N ^ 2 * W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))) := by
    linarith
  calc S₂ ≤ C * C' ^ (1 / (k : ℝ)) *
        (N ^ 2 * W ^ 2 + T * N * W ^ (2 - 1 / (k : ℝ))
          + N ^ 2 * W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))
          + T * N * W ^ (2 - 1 / (2 * (k : ℝ)))) := h
    _ ≤ C * C' ^ (1 / (k : ℝ)) *
        (2 * (N ^ 2 * W ^ 2 + T * N * W ^ (2 - 1 / (2 * (k : ℝ)))
          + N ^ 2 * W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))))) :=
        mul_le_mul_of_nonneg_left hstep hCC
    _ = _ := by ring

end

end RHTower.GuthMaynard
