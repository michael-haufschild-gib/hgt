import GaloisForLFunctions.RHTower.CCM.CCMFirstRowStationaryPhase
import GaloisForLFunctions.RHTower.VanDerCorputWeighted
import GaloisForLFunctions.RHTower.VanDerCorputWeightedAnti
import GaloisForLFunctions.RHTower.VanDerCorputWeightedSecondGeneral

/-!
# The van der Corput blocks of the exact first row

The leading Bessel term of the exceptional first-row Gram entry is estimated block by block.  The ray
`(1, ∞)` splits at the two edges of the stationary window `k^{-2}/4 ≤ x² - 1 ≤ 2 k^{-2}`, and on each
piece a different mechanism controls the oscillatory integral:

* on the window the difference phase has a stationary point, its second derivative is of size exactly
  `k³`, and the weighted second-derivative van der Corput bound gives `O(c^{-1/2} k^{-2})`;
* below the window the derivative is at least `k/5`, above it at most `-k/8`, and one integration by
  parts gives `O(w(a)/(c k))` on each side.

The amplitude of the leading term is the elementary fourth root `ampFourthRoot`: the endpoint phases of
the two Liouville–Green amplitudes cancel the two Bessel symbol prefactors identically, so no integral
survives in the weight.  It is positive and decreasing with a continuous derivative, which is exactly
the weight hypothesis of the weighted tests — and their right-hand sides involve only the amplitude at
the left endpoint, so no amplitude budget integral is ever needed.

Main statements: **`norm_integral_window_block_le`**, **`norm_integral_inner_block_le`**,
**`norm_integral_outer_block_le`**, with the structural inputs `abs_xiDiffSecond_window_bounds`,
`xiDiffSpeed_ge_of_inner`, `xiDiffSpeed_le_of_outer`, `xiDiffSecond_neg` and `xiAmplitude_mul_eq`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set

/-! ## The second derivative on the stationary window -/

private theorem le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ)) : a ≤ b := by
  have hs := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at hs

private theorem cube_le_of_le {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ (3 : ℕ) ≤ b ^ (3 : ℕ) := by
  gcongr

/-- The speed derivative in root coordinates: `t(s-1) / [(t²-1)^{3/2}(t²-s)^{1/2}]`.  Written this way
its size is controlled by two square roots whose squares are polynomial, which is what makes the
window estimates rational. -/
theorem xiSpeedDeriv_eq {s t : ℝ} (hs1 : s ≤ 1) (ht : 1 < t) :
    xiSpeedDeriv s t
      = t * (s - 1) / (Real.sqrt (t ^ (2 : ℕ) - 1) ^ (3 : ℕ) * Real.sqrt (t ^ (2 : ℕ) - s)) := by
  have h1 : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  have h2 : (0 : ℝ) < t ^ (2 : ℕ) - s := by nlinarith
  have hxi : xiSpeed s t = Real.sqrt (t ^ (2 : ℕ) - s) / Real.sqrt (t ^ (2 : ℕ) - 1) := by
    rw [xiSpeed, Real.sqrt_div h2.le]
  obtain ⟨P, hP0, hPsq, hPeq⟩ : ∃ P : ℝ, 0 < P ∧ P ^ (2 : ℕ) = t ^ (2 : ℕ) - 1
      ∧ Real.sqrt (t ^ (2 : ℕ) - 1) = P :=
    ⟨Real.sqrt (t ^ (2 : ℕ) - 1), Real.sqrt_pos.mpr h1, Real.sq_sqrt h1.le, rfl⟩
  obtain ⟨Q, hQ0, hQsq, hQeq⟩ : ∃ Q : ℝ, 0 < Q ∧ Q ^ (2 : ℕ) = t ^ (2 : ℕ) - s
      ∧ Real.sqrt (t ^ (2 : ℕ) - s) = Q :=
    ⟨Real.sqrt (t ^ (2 : ℕ) - s), Real.sqrt_pos.mpr h2, Real.sq_sqrt h2.le, rfl⟩
  rw [xiSpeedDeriv, hxi, hPeq, hQeq, ← hPsq]
  field_simp

/-- The polynomial content of the window estimate: the near block is of size `k^(6 : ℕ)` and the far block
of size `k^(8 : ℕ)`, so after squaring the far one is smaller by `k^{-2}`. -/
private theorem window_polynomial_bounds {s k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hdpos : 0 < x ^ (2 : ℕ) - 1) (hd1 : 1 / 4 ≤ k ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1)) (hd2 : k ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) ≤ 2)
    (hxsq : x ^ (2 : ℕ) ≤ 3 / 2) :
    k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s) ≤ 12
      ∧ 1 / 128 ≤ k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s)
      ∧ 48 ≤ ((k * x) ^ (2 : ℕ) - 1) ^ (3 : ℕ) * ((k * x) ^ (2 : ℕ) - s) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hksq : (4 : ℝ) ≤ k ^ (2 : ℕ) := by nlinarith
  have hk8 : (256 : ℝ) ≤ k ^ (8 : ℕ) := by
    have h : (4 : ℝ) ^ (4 : ℕ) ≤ (k ^ (2 : ℕ)) ^ (4 : ℕ) := by gcongr
    calc (256 : ℝ) = (4 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (k ^ (2 : ℕ)) ^ (4 : ℕ) := h
      _ = k ^ (8 : ℕ) := by ring
  have hnn : (0 : ℝ) ≤ k ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) := mul_nonneg (by positivity) hdpos.le
  have hcube : k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) ≤ 8 := by
    have h := cube_le_of_le hnn hd2
    calc k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) = (k ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1)) ^ (3 : ℕ) := by ring
      _ ≤ 2 ^ (3 : ℕ) := h
      _ = 8 := by norm_num
  have hcube' : (1 : ℝ) / 64 ≤ k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) := by
    have h := cube_le_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4) hd1
    calc (1 : ℝ) / 64 = (1 / 4 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ (k ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1)) ^ (3 : ℕ) := h
      _ = k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) := by ring
  have hxs : (1 : ℝ) / 2 ≤ x ^ (2 : ℕ) - s := by linarith
  have hxs2 : x ^ (2 : ℕ) - s ≤ 3 / 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · calc k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s) ≤ 8 * (3 / 2) :=
          mul_le_mul hcube hxs2 (by linarith) (by norm_num)
      _ = 12 := by norm_num
  · calc (1 : ℝ) / 128 = 1 / 64 * (1 / 2) := by norm_num
      _ ≤ k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s) :=
          mul_le_mul hcube' hxs (by norm_num) (by positivity)
  · have hfar1 : (3 : ℝ) / 4 * k ^ (2 : ℕ) ≤ (k * x) ^ (2 : ℕ) - 1 := by nlinarith [hksq, hdpos]
    have hfar2 : (7 : ℝ) / 8 * k ^ (2 : ℕ) ≤ (k * x) ^ (2 : ℕ) - s := by nlinarith [hksq, hdpos]
    have hfarcube : (27 : ℝ) / 64 * k ^ (6 : ℕ) ≤ ((k * x) ^ (2 : ℕ) - 1) ^ (3 : ℕ) := by
      have h := cube_le_of_le (by positivity : (0 : ℝ) ≤ 3 / 4 * k ^ (2 : ℕ)) hfar1
      calc (27 : ℝ) / 64 * k ^ (6 : ℕ) = (3 / 4 * k ^ (2 : ℕ)) ^ (3 : ℕ) := by ring
        _ ≤ ((k * x) ^ (2 : ℕ) - 1) ^ (3 : ℕ) := h
    have hcubenn : (0 : ℝ) ≤ ((k * x) ^ (2 : ℕ) - 1) ^ (3 : ℕ) :=
      pow_nonneg (by nlinarith [hfar1, hksq]) 3
    have hprod : (27 : ℝ) / 64 * k ^ (6 : ℕ) * (7 / 8 * k ^ (2 : ℕ))
        ≤ ((k * x) ^ (2 : ℕ) - 1) ^ (3 : ℕ) * ((k * x) ^ (2 : ℕ) - s) :=
      mul_le_mul hfarcube hfar2 (by positivity) hcubenn
    have hval : (48 : ℝ) ≤ 27 / 64 * k ^ (6 : ℕ) * (7 / 8 * k ^ (2 : ℕ)) := by nlinarith [hk8]
    linarith

/-- The final assembly of the window estimate, isolated so that the arithmetic runs in a small
context. -/
private theorem window_assembly {s k x U V : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk0 : 0 < k)
    (hx1 : 1 ≤ x) (hxu : x ≤ 5 / 4) (hUlow : k ^ (3 : ℕ) / 4 ≤ U) (hUup : U ≤ 12 * k ^ (3 : ℕ))
    (hVU : V ≤ U / 2) (hV0 : 0 < V) :
    k ^ (3 : ℕ) / 16 ≤ x * (1 - s) * (U - V) ∧ x * (1 - s) * (U - V) ≤ 15 * k ^ (3 : ℕ) := by
  have hk3 : (0 : ℝ) < k ^ (3 : ℕ) := by positivity
  have hs : (1 : ℝ) / 2 ≤ 1 - s := by linarith
  have hs' : (1 : ℝ) - s ≤ 1 := by linarith
  have hlow : k ^ (3 : ℕ) / 8 ≤ U - V := by linarith
  have hup : U - V ≤ 12 * k ^ (3 : ℕ) := by linarith
  refine ⟨?_, ?_⟩
  · calc k ^ (3 : ℕ) / 16 = 1 * (1 / 2) * (k ^ (3 : ℕ) / 8) := by ring
      _ ≤ x * (1 - s) * (U - V) := by
          refine mul_le_mul (mul_le_mul hx1 hs (by norm_num) (by linarith)) hlow (by positivity)
            (by nlinarith)
  · calc x * (1 - s) * (U - V) ≤ 5 / 4 * 1 * (12 * k ^ (3 : ℕ)) := by
          refine mul_le_mul (mul_le_mul hxu hs' (by linarith) (by norm_num)) hup (by linarith)
            (by norm_num)
      _ = 15 * k ^ (3 : ℕ) := by ring

/-- **The second derivative on the stationary window.**  On the window `k^{-2}/4 ≤ x²-1 ≤ 2k^{-2}`,
which contains the stationary point, the second derivative of the difference phase has size exactly of
order `k³`, with absolute constants.  Equation `(11)` is the value at the stationary point itself; this
is the uniform statement that a stationary-phase estimate needs.

The mechanism is that the far block is smaller than the near one by a factor `k^{-4}`: after squaring,
both blocks are rational in `x²`, `s` and `k`, and the comparison is a polynomial inequality. -/
theorem abs_xiDiffSecond_window_bounds {s k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hx : 1 < x) (hlow : 1 / (4 * k ^ (2 : ℕ)) ≤ x ^ (2 : ℕ) - 1) (hhigh : x ^ (2 : ℕ) - 1 ≤ 2 / k ^ (2 : ℕ)) :
    k ^ (3 : ℕ) / 16 ≤ |xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)|
      ∧ |xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)| ≤ 15 * k ^ (3 : ℕ) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hksq : (4 : ℝ) ≤ k ^ (2 : ℕ) := by nlinarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd2 : k ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) ≤ 2 := by
    rw [le_div_iff₀ (by positivity)] at hhigh
    nlinarith [hhigh]
  have hd1 : (1 : ℝ) / 4 ≤ k ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) := by
    rw [div_le_iff₀ (by positivity)] at hlow
    nlinarith [hlow]
  have hdpos : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hxsq : x ^ (2 : ℕ) ≤ 3 / 2 := by nlinarith [hd2, hksq]
  have hxu : x ≤ 5 / 4 := by nlinarith [hxsq, hx0]
  have hkx : (1 : ℝ) < k * x := by nlinarith
  have hkxsq : (0 : ℝ) < (k * x) ^ (2 : ℕ) - 1 := by nlinarith
  obtain ⟨hpoly1, hpoly2, hpoly3⟩ :=
    window_polynomial_bounds hs0 hs1 hk hdpos hd1 hd2 hxsq
  set P : ℝ := Real.sqrt (x ^ (2 : ℕ) - 1) with hPdef
  set Q : ℝ := Real.sqrt (x ^ (2 : ℕ) - s) with hQdef
  set R : ℝ := Real.sqrt ((k * x) ^ (2 : ℕ) - 1) with hRdef
  set S : ℝ := Real.sqrt ((k * x) ^ (2 : ℕ) - s) with hSdef
  have hP0 : 0 < P := Real.sqrt_pos.mpr hdpos
  have hQ0 : 0 < Q := Real.sqrt_pos.mpr (by linarith)
  have hR0 : 0 < R := Real.sqrt_pos.mpr hkxsq
  have hS0 : 0 < S := Real.sqrt_pos.mpr (by nlinarith)
  have hPsq : P ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 := Real.sq_sqrt hdpos.le
  have hQsq : Q ^ (2 : ℕ) = x ^ (2 : ℕ) - s := Real.sq_sqrt (by linarith)
  have hRsq : R ^ (2 : ℕ) = (k * x) ^ (2 : ℕ) - 1 := Real.sq_sqrt hkxsq.le
  have hSsq : S ^ (2 : ℕ) = (k * x) ^ (2 : ℕ) - s := Real.sq_sqrt (by nlinarith)
  set U : ℝ := 1 / (P ^ (3 : ℕ) * Q) with hUdef
  set V : ℝ := k ^ (3 : ℕ) / (R ^ (3 : ℕ) * S) with hVdef
  have hU0 : 0 < U := by rw [hUdef]; positivity
  have hV0 : 0 < V := by rw [hVdef]; positivity
  have hUsq : U ^ (2 : ℕ) = 1 / ((x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s)) := by
    have h : (P ^ (3 : ℕ) * Q) ^ (2 : ℕ) = (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s) := by
      rw [mul_pow, ← hPsq, ← hQsq]
      ring
    rw [hUdef, div_pow, one_pow, h]
  have hVsq : V ^ (2 : ℕ) = k ^ (6 : ℕ) / (((k * x) ^ (2 : ℕ) - 1) ^ (3 : ℕ) * ((k * x) ^ (2 : ℕ) - s)) := by
    have h : (R ^ (3 : ℕ) * S) ^ (2 : ℕ) = ((k * x) ^ (2 : ℕ) - 1) ^ (3 : ℕ) * ((k * x) ^ (2 : ℕ) - s) := by
      rw [mul_pow, ← hRsq, ← hSsq]
      ring
    rw [hVdef, div_pow, h, show (k ^ (3 : ℕ)) ^ (2 : ℕ) = k ^ (6 : ℕ) from by ring]
  have hApos : (0 : ℝ) < (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s) :=
    mul_pos (pow_pos hdpos 3) (by linarith)
  have hBpos : (0 : ℝ) < ((k * x) ^ (2 : ℕ) - 1) ^ (3 : ℕ) * ((k * x) ^ (2 : ℕ) - s) :=
    mul_pos (pow_pos hkxsq 3) (by nlinarith)
  have hVU : V ≤ U / 2 := by
    refine le_of_sq_le_sq hV0.le (by positivity) ?_
    have hgoal : V ^ (2 : ℕ) ≤ U ^ (2 : ℕ) / 4 := by
      rw [hUsq, hVsq, div_div,
        div_le_div_iff₀ hBpos (by linarith : (0 : ℝ) < (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s) * 4),
        one_mul]
      calc k ^ (6 : ℕ) * ((x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s) * 4)
          = 4 * (k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s)) := by ring
        _ ≤ 4 * 12 := by linarith
        _ = 48 := by norm_num
        _ ≤ ((k * x) ^ (2 : ℕ) - 1) ^ (3 : ℕ) * ((k * x) ^ (2 : ℕ) - s) := hpoly3
    calc V ^ (2 : ℕ) ≤ U ^ (2 : ℕ) / 4 := hgoal
      _ = (U / 2) ^ (2 : ℕ) := by ring
  have hUlow : k ^ (3 : ℕ) / 4 ≤ U := by
    refine le_of_sq_le_sq (by positivity) hU0.le ?_
    rw [div_pow, hUsq, div_le_div_iff₀ (by norm_num : (0 : ℝ) < (4 : ℝ) ^ (2 : ℕ)) hApos, one_mul]
    calc (k ^ (3 : ℕ)) ^ (2 : ℕ) * ((x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s))
        = k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s) := by ring
      _ ≤ 12 := hpoly1
      _ ≤ (4 : ℝ) ^ (2 : ℕ) := by norm_num
  have hUup : U ≤ 12 * k ^ (3 : ℕ) := by
    refine le_of_sq_le_sq hU0.le (by positivity) ?_
    rw [hUsq, mul_pow, div_le_iff₀ hApos]
    calc (1 : ℝ) = 128 * (1 / 128) := by norm_num
      _ ≤ 128 * (k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s)) := by linarith
      _ ≤ 12 ^ (2 : ℕ) * (k ^ (3 : ℕ)) ^ (2 : ℕ) * ((x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s)) := by
          have hW : (0 : ℝ) ≤ k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s) := by linarith
          calc 128 * (k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s))
              ≤ 144 * (k ^ (6 : ℕ) * (x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s)) := by linarith
            _ = 12 ^ (2 : ℕ) * (k ^ (3 : ℕ)) ^ (2 : ℕ) * ((x ^ (2 : ℕ) - 1) ^ (3 : ℕ) * (x ^ (2 : ℕ) - s)) := by ring
  have hE : xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x) = x * (s - 1) * (U - V) := by
    rw [xiSpeedDeriv_eq (by linarith) hx, xiSpeedDeriv_eq (by linarith) hkx, hUdef, hVdef,
      ← hPdef, ← hQdef, ← hRdef, ← hSdef]
    field_simp
  have hUV0 : 0 < U - V := by linarith
  have habs : |xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)| = x * (1 - s) * (U - V) := by
    rw [hE, abs_mul, abs_of_pos hUV0, abs_mul, abs_of_pos hx0,
      abs_of_nonpos (by linarith : s - 1 ≤ 0)]
    ring
  rw [habs]
  exact window_assembly hs0 hs1 hk0 hx.le hxu hUlow hUup hVU hV0

/-! ## The first derivative off the window -/

private theorem sqrt_le_of_le_sq {A B : ℝ} (hB : 0 ≤ B) (h : A ≤ B ^ (2 : ℕ)) : Real.sqrt A ≤ B := by
  rw [show B = Real.sqrt (B ^ (2 : ℕ)) from (Real.sqrt_sq hB).symm]
  exact Real.sqrt_le_sqrt h

private theorem le_sqrt_of_sq_le {A B : ℝ} (hA : 0 ≤ A) (h : A ^ (2 : ℕ) ≤ B) : A ≤ Real.sqrt B := by
  rw [show A = Real.sqrt (A ^ (2 : ℕ)) from (Real.sqrt_sq hA).symm]
  exact Real.sqrt_le_sqrt h

/-- The far speed is never below `1`: the dilated Liouville ratio exceeds one for every admissible
parameter. -/
theorem one_le_xiSpeed {s t : ℝ} (hs1 : s ≤ 1) (ht : 1 < t) : 1 ≤ xiSpeed s t := by
  have h1 : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  rw [xiSpeed]
  refine le_sqrt_of_sq_le (by norm_num) ?_
  rw [one_pow, le_div_iff₀ h1]
  linarith

/-- **Below the window the difference phase has derivative of size `k`.**  The near speed is at least
`sqrt 2 k` there while the far speed contributes at most `1.2 k`, so no cancellation is possible. -/
theorem xiDiffSpeed_ge_of_inner {s k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hx : 1 < x) (hin : x ^ (2 : ℕ) - 1 ≤ 1 / (4 * k ^ (2 : ℕ))) :
    k / 5 ≤ xiDiffSpeed s k x ∧ k / 5 ≤ |xiDiffSpeed s k x| := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hksq : (4 : ℝ) ≤ k ^ (2 : ℕ) := by nlinarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hdpos : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hd : k ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hin
    nlinarith [hin]
  have hkx : (1 : ℝ) < k * x := by nlinarith
  have hkxsq : (0 : ℝ) < (k * x) ^ (2 : ℕ) - 1 := by nlinarith
  -- the near speed is large
  have hnear : 141 / 100 * k ≤ xiSpeed s x := by
    rw [xiSpeed]
    refine le_sqrt_of_sq_le (by positivity) ?_
    rw [le_div_iff₀ hdpos]
    have hxs : (1 : ℝ) / 2 ≤ x ^ (2 : ℕ) - s := by nlinarith
    nlinarith [hd, hdpos, hksq, hxs]
  -- the far speed is small
  have hfar : xiSpeed s (k * x) ≤ 6 / 5 := by
    rw [xiSpeed]
    refine sqrt_le_of_le_sq (by norm_num) ?_
    rw [div_le_iff₀ hkxsq]
    have hkx4 : (4 : ℝ) ≤ (k * x) ^ (2 : ℕ) := by nlinarith
    nlinarith [hkx4, hs0]
  have hsign : k / 5 ≤ xiDiffSpeed s k x := by
    rw [xiDiffSpeed]
    have hmul : k * xiSpeed s (k * x) ≤ k * (6 / 5) := mul_le_mul_of_nonneg_left hfar hk0.le
    nlinarith [hnear, hmul]
  exact ⟨hsign, le_trans hsign (le_abs_self _)⟩

/-- **Above the window the difference phase has derivative of size `k` as well.**  The far speed
contributes at least `k` while the near speed is at most `(7/8) k`. -/
theorem xiDiffSpeed_le_of_outer {s k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hx : 1 < x) (hout : 2 / k ^ (2 : ℕ) ≤ x ^ (2 : ℕ) - 1) :
    k / 8 ≤ -xiDiffSpeed s k x ∧ k / 8 ≤ |xiDiffSpeed s k x| := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hksq : (4 : ℝ) ≤ k ^ (2 : ℕ) := by nlinarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hdpos : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by
    have hpos : (0 : ℝ) < 2 / k ^ (2 : ℕ) := by positivity
    linarith
  have hd : (2 : ℝ) ≤ k ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) := by
    rw [div_le_iff₀ (by positivity)] at hout
    nlinarith [hout]
  have hkx : (1 : ℝ) < k * x := by nlinarith
  -- the near speed is bounded above
  have hnear : xiSpeed s x ≤ 7 / 8 * k := by
    rw [xiSpeed]
    refine sqrt_le_of_le_sq (by positivity) ?_
    rw [div_le_iff₀ hdpos]
    have hone : (1 : ℝ) - s ≤ 1 := by linarith
    nlinarith [hd, hdpos, hksq, hone]
  -- the far speed is bounded below
  have hfar : (1 : ℝ) ≤ xiSpeed s (k * x) := one_le_xiSpeed (by linarith) hkx
  have hsign : k / 8 ≤ -xiDiffSpeed s k x := by
    rw [xiDiffSpeed]
    have hmul : k * 1 ≤ k * xiSpeed s (k * x) := mul_le_mul_of_nonneg_left hfar hk0.le
    nlinarith [hnear, hmul]
  exact ⟨hsign, le_trans hsign (neg_le_abs _)⟩

/-! ## The exact amplitude of the leading Bessel term -/

/-- The product of the four Liouville factors. -/
def ampPoly (s k x : ℝ) : ℝ := (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s)

/-- Its derivative. -/
def ampPolyDeriv (s k x : ℝ) : ℝ :=
  2 * x * (x ^ (2 : ℕ) - s) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s)
    + (x ^ (2 : ℕ) - 1) * (2 * x) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s)
    + (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) * (2 * k ^ (2 : ℕ) * x) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s)
    + (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (2 * k ^ (2 : ℕ) * x)

/-- The exact amplitude of the leading Bessel term: the two Liouville–Green amplitudes against the two
Bessel symbols.  The endpoint phases cancel identically, leaving an elementary algebraic fourth root
with no integral in it at all. -/
def ampFourthRoot (s k x : ℝ) : ℝ := 1 / Real.sqrt (Real.sqrt (ampPoly s k x))

theorem ampPoly_pos_of_one_lt {s k x : ℝ} (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hx : 1 < x) :
    0 < ampPoly s k x := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have hksq : (1 : ℝ) < k ^ (2 : ℕ) := by nlinarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hx1 : (1 : ℝ) < x ^ (2 : ℕ) := by nlinarith
  have h1 : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by linarith
  have h2 : (0 : ℝ) < x ^ (2 : ℕ) - s := by linarith
  have h3 : (0 : ℝ) < k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by nlinarith
  have h4 : (0 : ℝ) < k ^ (2 : ℕ) * x ^ (2 : ℕ) - s := by nlinarith
  rw [ampPoly]
  positivity

/-- Compatibility wrapper for the uniform integer-dilation regime. -/
theorem ampPoly_pos {s k x : ℝ} (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    0 < ampPoly s k x :=
  ampPoly_pos_of_one_lt hs1 (by linarith) hx

theorem ampPolyDeriv_pos_of_one_lt {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hx : 1 < x) :
    0 < ampPolyDeriv s k x := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have hksq : (1 : ℝ) < k ^ (2 : ℕ) := by nlinarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hx1 : (1 : ℝ) < x ^ (2 : ℕ) := by nlinarith
  have h1 : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by linarith
  have h2 : (0 : ℝ) < x ^ (2 : ℕ) - s := by linarith
  have h3 : (0 : ℝ) < k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by nlinarith
  have h4 : (0 : ℝ) < k ^ (2 : ℕ) * x ^ (2 : ℕ) - s := by nlinarith
  rw [ampPolyDeriv]
  positivity

/-- Compatibility wrapper for the uniform integer-dilation regime. -/
theorem ampPolyDeriv_pos {s k x : ℝ} (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    0 < ampPolyDeriv s k x :=
  ampPolyDeriv_pos_of_one_lt hs1 (by linarith) hx

theorem hasDerivAt_ampPoly (s k x : ℝ) : HasDerivAt (ampPoly s k) (ampPolyDeriv s k x) x := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ)) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h1 : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) - 1) (2 * x) x := by
    simpa using hsq.sub_const 1
  have h2 : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) - s) (2 * x) x := by
    simpa using hsq.sub_const s
  have h3 : HasDerivAt (fun t : ℝ => k ^ (2 : ℕ) * t ^ (2 : ℕ) - 1) (2 * k ^ (2 : ℕ) * x) x := by
    have h := (hsq.const_mul (k ^ (2 : ℕ))).sub_const 1
    rw [show k ^ (2 : ℕ) * (2 * x) = 2 * k ^ (2 : ℕ) * x from by ring] at h
    exact h
  have h4 : HasDerivAt (fun t : ℝ => k ^ (2 : ℕ) * t ^ (2 : ℕ) - s) (2 * k ^ (2 : ℕ) * x) x := by
    have h := (hsq.const_mul (k ^ (2 : ℕ))).sub_const s
    rw [show k ^ (2 : ℕ) * (2 * x) = 2 * k ^ (2 : ℕ) * x from by ring] at h
    exact h
  have h := ((h1.fun_mul h2).fun_mul h3).fun_mul h4
  have hval : (((2 * x) * (x ^ (2 : ℕ) - s) + (x ^ (2 : ℕ) - 1) * (2 * x)) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)
        + (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) * (2 * k ^ (2 : ℕ) * x)) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s)
      + (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (2 * k ^ (2 : ℕ) * x)
      = ampPolyDeriv s k x := by
    rw [ampPolyDeriv]
    ring
  rw [hval] at h
  exact h

/-- **The phase factors cancel.**  The product of the two Liouville–Green amplitudes against the two
Bessel symbol prefactors is the elementary fourth root: the two `xi^{1/2}` numerators of the
amplitudes cancel the two `xi^{-1/2}` symbol factors exactly. -/
theorem xiAmplitude_mul_eq_of_one_lt {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hx : 1 < x) :
    xiAmplitude s x * xiAmplitude s (k * x)
      = ampFourthRoot s k x
        * (Real.sqrt (xiEndpointPhase s x) * Real.sqrt (xiEndpointPhase s (k * x))) := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have hksq : (1 : ℝ) < k ^ (2 : ℕ) := by nlinarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hx1 : (1 : ℝ) < x ^ (2 : ℕ) := by nlinarith
  have h1 : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by linarith
  have h2 : (0 : ℝ) < x ^ (2 : ℕ) - s := by linarith
  have h3 : (0 : ℝ) < k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by nlinarith
  have h4 : (0 : ℝ) < k ^ (2 : ℕ) * x ^ (2 : ℕ) - s := by nlinarith
  have hkxsq : (k * x) ^ (2 : ℕ) = k ^ (2 : ℕ) * x ^ (2 : ℕ) := by ring
  have hden : Real.sqrt (Real.sqrt (ampPoly s k x))
      = Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))
        * Real.sqrt (Real.sqrt (((k * x) ^ (2 : ℕ) - 1) * ((k * x) ^ (2 : ℕ) - s))) := by
    rw [hkxsq, ampPoly, show (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s)
        = ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) * ((k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s)) from by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (Real.sqrt_nonneg _)]
  have hd1 : (0 : ℝ) < Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hd2 : (0 : ℝ) < Real.sqrt (Real.sqrt (((k * x) ^ (2 : ℕ) - 1) * ((k * x) ^ (2 : ℕ) - s))) := by
    refine Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ?_)
    rw [hkxsq]
    positivity
  rw [xiAmplitude, xiAmplitude, ampFourthRoot, hden]
  field_simp

/-- Compatibility wrapper for the uniform integer-dilation regime. -/
theorem xiAmplitude_mul_eq {s k x : ℝ} (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    xiAmplitude s x * xiAmplitude s (k * x)
      = ampFourthRoot s k x
        * (Real.sqrt (xiEndpointPhase s x) * Real.sqrt (xiEndpointPhase s (k * x))) :=
  xiAmplitude_mul_eq_of_one_lt hs1 (by linarith) hx

/-- The amplitude is bounded by `2 k^{-1/2}` from the window on: the two far factors contribute `k²`
and the near ones a constant. -/
theorem ampFourthRoot_le {s k x : ℝ} (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x)
    (hlow : 1 / (4 * k ^ (2 : ℕ)) ≤ x ^ (2 : ℕ) - 1) : ampFourthRoot s k x ≤ 2 / Real.sqrt k := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hksq : (4 : ℝ) ≤ k ^ (2 : ℕ) := by nlinarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hx1 : (1 : ℝ) < x ^ (2 : ℕ) := by nlinarith
  have h1 : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by linarith
  have h2 : (1 : ℝ) / 2 ≤ x ^ (2 : ℕ) - s := by linarith
  have h3 : (3 : ℝ) / 4 * k ^ (2 : ℕ) ≤ k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by nlinarith
  have h4 : (7 : ℝ) / 8 * k ^ (2 : ℕ) ≤ k ^ (2 : ℕ) * x ^ (2 : ℕ) - s := by nlinarith
  -- the polynomial is at least k²/16
  have hW : k ^ (2 : ℕ) / 16 ≤ ampPoly s k x := by
    rw [ampPoly]
    have hstep1 : 1 / (4 * k ^ (2 : ℕ)) * (1 / 2) ≤ (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) :=
      mul_le_mul hlow h2 (by norm_num) (by linarith)
    have hstep2 : (3 : ℝ) / 4 * k ^ (2 : ℕ) * (7 / 8 * k ^ (2 : ℕ))
        ≤ (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s) :=
      mul_le_mul h3 h4 (by positivity) (by linarith)
    have hprod : (1 / (4 * k ^ (2 : ℕ)) * (1 / 2)) * (3 / 4 * k ^ (2 : ℕ) * (7 / 8 * k ^ (2 : ℕ)))
        ≤ ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) * ((k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s)) :=
      mul_le_mul hstep1 hstep2 (by positivity) (by nlinarith [hstep1])
    have hval : k ^ (2 : ℕ) / 16 ≤ (1 / (4 * k ^ (2 : ℕ)) * (1 / 2)) * (3 / 4 * k ^ (2 : ℕ) * (7 / 8 * k ^ (2 : ℕ))) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16)] at *
      field_simp
      nlinarith [hk0, sq_nonneg k]
    calc k ^ (2 : ℕ) / 16 ≤ (1 / (4 * k ^ (2 : ℕ)) * (1 / 2)) * (3 / 4 * k ^ (2 : ℕ) * (7 / 8 * k ^ (2 : ℕ))) := hval
      _ ≤ ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) * ((k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s)) := hprod
      _ = (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) * x ^ (2 : ℕ) - s) := by ring
  -- pass to the fourth root
  have hWpos : (0 : ℝ) < ampPoly s k x := ampPoly_pos hs1 hk hx
  have hsqW : k / 4 ≤ Real.sqrt (ampPoly s k x) := by
    refine le_sqrt_of_sq_le (by positivity) ?_
    calc (k / 4) ^ (2 : ℕ) = k ^ (2 : ℕ) / 16 := by ring
      _ ≤ ampPoly s k x := hW
  have hsqsqW : Real.sqrt k / 2 ≤ Real.sqrt (Real.sqrt (ampPoly s k x)) := by
    refine le_sqrt_of_sq_le (by positivity) ?_
    have hks : Real.sqrt k ^ (2 : ℕ) = k := Real.sq_sqrt hk0.le
    calc (Real.sqrt k / 2) ^ (2 : ℕ) = k / 4 := by rw [div_pow, hks]; norm_num
      _ ≤ Real.sqrt (ampPoly s k x) := hsqW
  have hpos : (0 : ℝ) < Real.sqrt k / 2 := by positivity
  rw [ampFourthRoot]
  calc 1 / Real.sqrt (Real.sqrt (ampPoly s k x)) ≤ 1 / (Real.sqrt k / 2) :=
        one_div_le_one_div_of_le hpos hsqsqW
    _ = 2 / Real.sqrt k := by
        rw [one_div_div]

/-- The derivative of the amplitude. -/
def ampFourthRootDeriv (s k x : ℝ) : ℝ :=
  -(ampPolyDeriv s k x) / (4 * ampPoly s k x * Real.sqrt (Real.sqrt (ampPoly s k x)))

theorem hasDerivAt_ampFourthRoot_of_one_lt {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hx : 1 < x) :
    HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x := by
  have hW : 0 < ampPoly s k x := ampPoly_pos_of_one_lt hs1 hk hx
  have hGpos : 0 < Real.sqrt (ampPoly s k x) := Real.sqrt_pos.mpr hW
  have hFpos : 0 < Real.sqrt (Real.sqrt (ampPoly s k x)) := Real.sqrt_pos.mpr hGpos
  have hfun : ampFourthRoot s k = fun t => (Real.sqrt (Real.sqrt (ampPoly s k t)))⁻¹ := by
    funext t
    rw [ampFourthRoot, one_div]
  have h1 : HasDerivAt (fun t : ℝ => Real.sqrt (ampPoly s k t))
      (ampPolyDeriv s k x / (2 * Real.sqrt (ampPoly s k x))) x :=
    (hasDerivAt_ampPoly s k x).sqrt hW.ne'
  have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (Real.sqrt (ampPoly s k t)))
      (ampPolyDeriv s k x / (2 * Real.sqrt (ampPoly s k x))
        / (2 * Real.sqrt (Real.sqrt (ampPoly s k x)))) x :=
    h1.sqrt hGpos.ne'
  have h3 := h2.fun_inv hFpos.ne'
  have hval : -(ampPolyDeriv s k x / (2 * Real.sqrt (ampPoly s k x))
        / (2 * Real.sqrt (Real.sqrt (ampPoly s k x))))
        / Real.sqrt (Real.sqrt (ampPoly s k x)) ^ (2 : ℕ)
      = ampFourthRootDeriv s k x := by
    rw [ampFourthRootDeriv]
    obtain ⟨G, hG0, hGsq, hGeq⟩ : ∃ G : ℝ, 0 < G ∧ G ^ (2 : ℕ) = ampPoly s k x
        ∧ Real.sqrt (ampPoly s k x) = G :=
      ⟨Real.sqrt (ampPoly s k x), hGpos, Real.sq_sqrt hW.le, rfl⟩
    obtain ⟨F, hF0, hFsq, hFeq⟩ : ∃ F : ℝ, 0 < F ∧ F ^ (2 : ℕ) = G ∧ Real.sqrt G = F :=
      ⟨Real.sqrt G, Real.sqrt_pos.mpr hG0, Real.sq_sqrt hG0.le, rfl⟩
    rw [hGeq, hFeq, ← hGsq, ← hFsq]
    field_simp
    ring
  rw [hfun, ← hval]
  exact h3

/-- Compatibility wrapper for the uniform integer-dilation regime. -/
theorem hasDerivAt_ampFourthRoot {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
  hasDerivAt_ampFourthRoot_of_one_lt hs1 (by linarith) hx

theorem ampFourthRootDeriv_nonpos_of_one_lt {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hx : 1 < x) :
    ampFourthRootDeriv s k x ≤ 0 := by
  have hW : 0 < ampPoly s k x := ampPoly_pos_of_one_lt hs1 hk hx
  have hD : 0 < ampPolyDeriv s k x := ampPolyDeriv_pos_of_one_lt hs1 hk hx
  have hFpos : 0 < Real.sqrt (Real.sqrt (ampPoly s k x)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hW)
  rw [ampFourthRootDeriv, div_nonpos_iff]
  right
  exact ⟨by linarith, mul_nonneg (by linarith) hFpos.le⟩

/-- Compatibility wrapper for the uniform integer-dilation regime. -/
theorem ampFourthRootDeriv_nonpos {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    ampFourthRootDeriv s k x ≤ 0 :=
  ampFourthRootDeriv_nonpos_of_one_lt hs1 (by linarith) hx

theorem continuousOn_ampPoly (s k : ℝ) : ContinuousOn (ampPoly s k) (Set.Ioi 1) := by
  unfold ampPoly
  fun_prop

theorem continuousOn_ampFourthRootDeriv_of_one_lt {s k : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 1 < k) :
    ContinuousOn (ampFourthRootDeriv s k) (Set.Ioi 1) := by
  intro x hx
  have hx1 : (1 : ℝ) < x := hx
  have hW : 0 < ampPoly s k x := ampPoly_pos_of_one_lt hs1 hk hx1
  have hnum : ContinuousWithinAt (fun t : ℝ => -(ampPolyDeriv s k t)) (Set.Ioi 1) x := by
    refine ContinuousWithinAt.neg ?_
    refine ContinuousAt.continuousWithinAt ?_
    unfold ampPolyDeriv
    fun_prop
  have hpolyc : ContinuousWithinAt (ampPoly s k) (Set.Ioi 1) x :=
    (continuousOn_ampPoly s k) x hx
  have hden : ContinuousWithinAt
      (fun t : ℝ => 4 * ampPoly s k t * Real.sqrt (Real.sqrt (ampPoly s k t))) (Set.Ioi 1) x :=
    (continuousWithinAt_const.mul hpolyc).mul (hpolyc.sqrt.sqrt)
  have hne : 4 * ampPoly s k x * Real.sqrt (Real.sqrt (ampPoly s k x)) ≠ 0 := by
    have hFpos : 0 < Real.sqrt (Real.sqrt (ampPoly s k x)) :=
      Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hW)
    positivity
  exact hnum.div hden hne

/-- Compatibility wrapper for the uniform integer-dilation regime. -/
theorem continuousOn_ampFourthRootDeriv {s k : ℝ} (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) :
    ContinuousOn (ampFourthRootDeriv s k) (Set.Ioi 1) :=
  continuousOn_ampFourthRootDeriv_of_one_lt hs1 (by linarith)

/-- The amplitude of the leading term is positive. -/
theorem ampFourthRoot_pos_of_one_lt {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hx : 1 < x) :
    0 < ampFourthRoot s k x := by
  have hW : 0 < ampPoly s k x := ampPoly_pos_of_one_lt hs1 hk hx
  have hFpos : 0 < Real.sqrt (Real.sqrt (ampPoly s k x)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hW)
  rw [ampFourthRoot]
  positivity

/-- Compatibility wrapper for the uniform integer-dilation regime. -/
theorem ampFourthRoot_pos {s k x : ℝ} (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    0 < ampFourthRoot s k x :=
  ampFourthRoot_pos_of_one_lt hs1 (by linarith) hx

/-! ## Strict concavity of the difference phase -/

/-- **The difference phase is strictly concave on the whole ray.**  The far block of the second
derivative is strictly smaller than the near one for a structural reason: `sqrt(k²x²-1) > k sqrt(x²-1)`
and `sqrt(k²x²-s) > sqrt(x²-s)`, so the far denominator beats the factor `k³` outright.  No window is
needed. -/
theorem xiDiffSecond_neg {s k x : ℝ} (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hx : 1 < x) :
    xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x) < 0 := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have hksq : (1 : ℝ) < k ^ (2 : ℕ) := by nlinarith
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hx1 : (1 : ℝ) < x ^ (2 : ℕ) := by nlinarith
  have hkx : (1 : ℝ) < k * x := by nlinarith
  have hdpos : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by linarith
  have hkxsq : (0 : ℝ) < (k * x) ^ (2 : ℕ) - 1 := by nlinarith
  set P : ℝ := Real.sqrt (x ^ (2 : ℕ) - 1) with hPdef
  set Q : ℝ := Real.sqrt (x ^ (2 : ℕ) - s) with hQdef
  set R : ℝ := Real.sqrt ((k * x) ^ (2 : ℕ) - 1) with hRdef
  set S : ℝ := Real.sqrt ((k * x) ^ (2 : ℕ) - s) with hSdef
  have hP0 : 0 < P := Real.sqrt_pos.mpr hdpos
  have hQ0 : 0 < Q := Real.sqrt_pos.mpr (by linarith)
  have hR0 : 0 < R := Real.sqrt_pos.mpr hkxsq
  have hS0 : 0 < S := Real.sqrt_pos.mpr (by nlinarith)
  have hPsq : P ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 := Real.sq_sqrt hdpos.le
  have hQsq : Q ^ (2 : ℕ) = x ^ (2 : ℕ) - s := Real.sq_sqrt (by linarith)
  have hRsq : R ^ (2 : ℕ) = (k * x) ^ (2 : ℕ) - 1 := Real.sq_sqrt hkxsq.le
  have hSsq : S ^ (2 : ℕ) = (k * x) ^ (2 : ℕ) - s := Real.sq_sqrt (by nlinarith)
  have hRP : k * P < R := by
    refine lt_of_pow_lt_pow_left₀ 2 hR0.le ?_
    rw [mul_pow, hPsq, hRsq]
    nlinarith [hksq, hx1]
  have hQS : Q < S := by
    refine lt_of_pow_lt_pow_left₀ 2 hS0.le ?_
    rw [hQsq, hSsq]
    nlinarith [hksq, hx1, hx0]
  have hprod : k ^ (3 : ℕ) * (P ^ (3 : ℕ) * Q) < R ^ (3 : ℕ) * S := by
    have h1 : (k * P) ^ (3 : ℕ) < R ^ (3 : ℕ) := by
      exact pow_lt_pow_left₀ hRP (by positivity) (by norm_num)
    have h2 : (k * P) ^ (3 : ℕ) = k ^ (3 : ℕ) * P ^ (3 : ℕ) := by ring
    calc k ^ (3 : ℕ) * (P ^ (3 : ℕ) * Q) = (k * P) ^ (3 : ℕ) * Q := by rw [h2]; ring
      _ < R ^ (3 : ℕ) * Q := by
          exact mul_lt_mul_of_pos_right h1 hQ0
      _ < R ^ (3 : ℕ) * S := by
          exact mul_lt_mul_of_pos_left hQS (by positivity)
  have hUV : k ^ (3 : ℕ) / (R ^ (3 : ℕ) * S) < 1 / (P ^ (3 : ℕ) * Q) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
    exact hprod
  have hE : xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)
      = x * (s - 1) * (1 / (P ^ (3 : ℕ) * Q) - k ^ (3 : ℕ) / (R ^ (3 : ℕ) * S)) := by
    rw [xiSpeedDeriv_eq (by linarith) hx, xiSpeedDeriv_eq (by linarith) hkx,
      ← hPdef, ← hQdef, ← hRdef, ← hSdef]
    field_simp
  rw [hE]
  have hpos : 0 < 1 / (P ^ (3 : ℕ) * Q) - k ^ (3 : ℕ) / (R ^ (3 : ℕ) * S) := by linarith
  have hneg : x * (s - 1) < 0 := by nlinarith
  exact mul_neg_of_neg_of_pos hneg hpos

/-! ## The window block of the stationary-phase estimate -/

theorem continuousOn_xiSpeedDeriv {s : ℝ} (hs1 : s ≤ 1) :
    ContinuousOn (xiSpeedDeriv s) (Set.Ioi 1) := by
  intro t ht
  have ht1 : (1 : ℝ) < t := ht
  have h1 : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  have h2 : (0 : ℝ) < t ^ (2 : ℕ) - s := by nlinarith
  have hxi : 0 < xiSpeed s t := by
    rw [xiSpeed]
    exact Real.sqrt_pos.mpr (div_pos h2 h1)
  have hnum : ContinuousWithinAt (fun u : ℝ => u * (s - 1)) (Set.Ioi 1) t := by
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop
  have hden : ContinuousWithinAt
      (fun u : ℝ => (u ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s u) (Set.Ioi 1) t := by
    refine ContinuousWithinAt.mul ?_ ((continuousAt_xiSpeed ht1).continuousWithinAt)
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop
  have hne : ((t ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s t) ≠ 0 := by positivity
  exact hnum.div hden hne

/-! ## Fixed-ratio first-derivative blocks -/

/-- On every fixed compact exterior block, strict concavity has a positive curvature floor uniform
over `0 ≤ s ≤ 1/2`. -/
theorem exists_fixedRatioCurvatureFloor {k p q : ℝ}
    (hk : 1 < k) (hp : 1 < p) (hpq : p ≤ q) :
    ∃ η : ℝ, 0 < η ∧ ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ x ∈ Set.Icc p q,
      η ≤ -(xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)) := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc p q
  let F : ℝ × ℝ → ℝ := fun z =>
    -(xiSpeedDeriv z.1 z.2 - k ^ (2 : ℕ) * xiSpeedDeriv z.1 (k * z.2))
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := by
    exact (Set.nonempty_Icc.mpr (by norm_num)).prod (Set.nonempty_Icc.mpr hpq)
  have hFcont : ContinuousOn F K := by
    intro z hz
    have hx : 1 < z.2 := hp.trans_le hz.2.1
    have hk0 : 0 < k := lt_trans zero_lt_one hk
    have hkx : 1 < k * z.2 := by nlinarith
    have hs1 : z.1 ≤ 1 / 2 := hz.1.2
    have hnearRad : 0 < (z.2 ^ (2 : ℕ) - z.1) / (z.2 ^ (2 : ℕ) - 1) := by
      apply div_pos <;> nlinarith
    have hfarRad : 0 < ((k * z.2) ^ (2 : ℕ) - z.1) / ((k * z.2) ^ (2 : ℕ) - 1) := by
      apply div_pos <;> nlinarith
    have hnearSqrt : Real.sqrt ((z.2 ^ (2 : ℕ) - z.1) / (z.2 ^ (2 : ℕ) - 1)) ≠ 0 :=
      (Real.sqrt_pos.mpr hnearRad).ne'
    have hfarSqrt : Real.sqrt (((k * z.2) ^ (2 : ℕ) - z.1) / ((k * z.2) ^ (2 : ℕ) - 1)) ≠ 0 :=
      (Real.sqrt_pos.mpr hfarRad).ne'
    have hnearBase : z.2 ^ (2 : ℕ) - 1 ≠ 0 := by nlinarith
    have hfarBase : (k * z.2) ^ (2 : ℕ) - 1 ≠ 0 := by nlinarith
    have hnearDen :
        (z.2 ^ (2 : ℕ) - 1) ^ (2 : ℕ) * Real.sqrt ((z.2 ^ (2 : ℕ) - z.1) / (z.2 ^ (2 : ℕ) - 1)) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ hnearBase) hnearSqrt
    have hfarDen :
        ((k * z.2) ^ (2 : ℕ) - 1) ^ (2 : ℕ) *
          Real.sqrt (((k * z.2) ^ (2 : ℕ) - z.1) / ((k * z.2) ^ (2 : ℕ) - 1)) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ hfarBase) hfarSqrt
    have hnearRadCont : ContinuousAt
        (fun w : ℝ × ℝ => (w.2 ^ (2 : ℕ) - w.1) / (w.2 ^ (2 : ℕ) - 1)) z := by
      have hnum : ContinuousAt (fun w : ℝ × ℝ => w.2 ^ (2 : ℕ) - w.1) z := by
        fun_prop
      have hden : ContinuousAt (fun w : ℝ × ℝ => w.2 ^ (2 : ℕ) - 1) z := by
        fun_prop
      exact hnum.div hden hnearBase
    have hfarRadCont : ContinuousAt
        (fun w : ℝ × ℝ => ((k * w.2) ^ (2 : ℕ) - w.1) / ((k * w.2) ^ (2 : ℕ) - 1)) z := by
      have hnum : ContinuousAt (fun w : ℝ × ℝ => (k * w.2) ^ (2 : ℕ) - w.1) z := by
        fun_prop
      have hden : ContinuousAt (fun w : ℝ × ℝ => (k * w.2) ^ (2 : ℕ) - 1) z := by
        fun_prop
      exact hnum.div hden hfarBase
    have hnearTerm : ContinuousAt (fun w : ℝ × ℝ =>
        w.2 * (w.1 - 1) /
          ((w.2 ^ (2 : ℕ) - 1) ^ (2 : ℕ) * Real.sqrt ((w.2 ^ (2 : ℕ) - w.1) / (w.2 ^ (2 : ℕ) - 1)))) z := by
      have hnum : ContinuousAt (fun w : ℝ × ℝ => w.2 * (w.1 - 1)) z := by
        fun_prop
      have hbase : ContinuousAt (fun w : ℝ × ℝ => (w.2 ^ (2 : ℕ) - 1) ^ (2 : ℕ)) z := by
        fun_prop
      exact hnum.div (hbase.mul hnearRadCont.sqrt) hnearDen
    have hfarTerm : ContinuousAt (fun w : ℝ × ℝ =>
        k * w.2 * (w.1 - 1) /
          (((k * w.2) ^ (2 : ℕ) - 1) ^ (2 : ℕ) *
            Real.sqrt (((k * w.2) ^ (2 : ℕ) - w.1) / ((k * w.2) ^ (2 : ℕ) - 1)))) z := by
      have hnum : ContinuousAt (fun w : ℝ × ℝ => k * w.2 * (w.1 - 1)) z := by
        fun_prop
      have hbase : ContinuousAt (fun w : ℝ × ℝ => ((k * w.2) ^ (2 : ℕ) - 1) ^ (2 : ℕ)) z := by
        fun_prop
      exact hnum.div (hbase.mul hfarRadCont.sqrt) hfarDen
    apply ContinuousAt.continuousWithinAt
    dsimp only [F]
    unfold xiSpeedDeriv xiSpeed
    exact (hnearTerm.sub (continuousAt_const.mul hfarTerm)).neg
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hFcont
  have hpos : ∀ z ∈ K, 0 < F z := by
    intro z hz
    exact neg_pos.mpr (xiDiffSecond_neg hz.1.2 hk (hp.trans_le hz.2.1))
  refine ⟨F z₀, hpos z₀ hz₀, ?_⟩
  intro s hs x hx
  exact (isMinOn_iff.mp hmin) (s, x) ⟨hs, hx⟩

/-- Weighted stationary-phase cancellation on a block with an arbitrary supplied lower curvature
bound.  This is the fixed-ratio counterpart of the explicit uniform window theorem below. -/
theorem norm_integral_neg_diffPhase_block_le_of_second_ge
    {s c k a b η : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k)
    (hc : 0 < c) (hη : 0 < η) (hab : a ≤ b) (ha : 1 < a)
    (hcurv : ∀ x ∈ Set.uIcc a b,
      η ≤ -(xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x))) :
    ‖∫ x in a..b, (ampFourthRoot s k x : ℂ)
        * Complex.exp (((-(c * xiDiffPhase s k x) : ℝ) : ℂ) * Complex.I)‖
      ≤ 10 * ampFourthRoot s k a / Real.sqrt (c * η) := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have hsub : Set.uIcc a b ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hx1 : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < x := fun x hx => hsub hx
  have hkx : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < k * x := by
    intro x hx
    have := hx1 x hx
    nlinarith
  set lam : ℝ := c * η with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hw : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
    fun x hx => hasDerivAt_ampFourthRoot_of_one_lt hs1 hk (hx1 x hx)
  have hw'c : ContinuousOn (ampFourthRootDeriv s k) (Set.uIcc a b) :=
    (continuousOn_ampFourthRootDeriv_of_one_lt hs1 hk).mono hsub
  have hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ ampFourthRoot s k x :=
    fun x hx => (ampFourthRoot_pos_of_one_lt hs1 hk (hx1 x hx)).le
  have hwanti : ∀ x ∈ Set.uIcc a b, ampFourthRootDeriv s k x ≤ 0 :=
    fun x hx => ampFourthRootDeriv_nonpos_of_one_lt hs1 hk (hx1 x hx)
  have hg : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(c * xiDiffPhase s k t)) (-(c * xiDiffSpeed s k x)) x :=
    fun x hx => ((hasDerivAt_xiDiffPhase hs0 (hx1 x hx) (hkx x hx)).const_mul c).neg
  have hg' : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(c * xiDiffSpeed s k t))
        (-(c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)))) x :=
    fun x hx => ((hasDerivAt_xiDiffSpeed (by linarith) (hx1 x hx) (hkx x hx)).const_mul c).neg
  have hg''c : ContinuousOn
      (fun t : ℝ => -(c * (xiSpeedDeriv s t - k ^ (2 : ℕ) * xiSpeedDeriv s (k * t))))
      (Set.uIcc a b) := by
    have h1 : ContinuousOn (xiSpeedDeriv s) (Set.uIcc a b) :=
      (continuousOn_xiSpeedDeriv (by linarith)).mono hsub
    have h2 : ContinuousOn (fun t : ℝ => xiSpeedDeriv s (k * t)) (Set.uIcc a b) := by
      refine (continuousOn_xiSpeedDeriv (s := s) (by linarith)).comp
        ((continuous_const.mul continuous_id).continuousOn) ?_
      intro x hx
      exact hkx x hx
    exact (continuousOn_const.mul (h1.sub (continuousOn_const.mul h2))).neg
  have hg''lb : ∀ x ∈ Set.uIcc a b,
      lam ≤ -(c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x))) := by
    intro x hx
    rw [hlamdef]
    have hmul := mul_le_mul_of_nonneg_left (hcurv x hx) hc.le
    nlinarith
  have hmain := _root_.RHTower.norm_integral_weight_cexp_secondDeriv hab hlam hw hw'c hwnn hwanti
    hg hg' hg''c hg''lb
  simpa [hlamdef] using hmain

/-- Weighted first-derivative cancellation before the stationary point, with an arbitrary supplied
speed floor.  Unlike the uniform integer-dilation estimate below, this theorem only needs `k > 1`. -/
theorem norm_integral_diffPhase_block_le_of_speed_ge
    {s c k a b η : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k)
    (hc : 0 < c) (hη : 0 < η) (hab : a ≤ b) (ha : 1 < a)
    (hfloor : ∀ x ∈ Set.uIcc a b, η ≤ xiDiffSpeed s k x) :
    ‖∫ x in a..b, (ampFourthRoot s k x : ℂ)
        * Complex.exp (((c * xiDiffPhase s k x : ℝ) : ℂ) * Complex.I)‖
      ≤ 4 * ampFourthRoot s k a / (c * η) := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have hsub : Set.uIcc a b ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hx1 : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < x := fun x hx => hsub hx
  have hkx : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < k * x := by
    intro x hx
    have := hx1 x hx
    nlinarith
  set lam : ℝ := c * η with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hw : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
    fun x hx => hasDerivAt_ampFourthRoot_of_one_lt hs1 hk (hx1 x hx)
  have hw'c : ContinuousOn (ampFourthRootDeriv s k) (Set.uIcc a b) :=
    (continuousOn_ampFourthRootDeriv_of_one_lt hs1 hk).mono hsub
  have hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ ampFourthRoot s k x :=
    fun x hx => (ampFourthRoot_pos_of_one_lt hs1 hk (hx1 x hx)).le
  have hwanti : ∀ x ∈ Set.uIcc a b, ampFourthRootDeriv s k x ≤ 0 :=
    fun x hx => ampFourthRootDeriv_nonpos_of_one_lt hs1 hk (hx1 x hx)
  have hg : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => c * xiDiffPhase s k t) (c * xiDiffSpeed s k x) x :=
    fun x hx => (hasDerivAt_xiDiffPhase hs0 (hx1 x hx) (hkx x hx)).const_mul c
  have hg' : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => c * xiDiffSpeed s k t)
        (c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x))) x :=
    fun x hx => (hasDerivAt_xiDiffSpeed (by linarith) (hx1 x hx) (hkx x hx)).const_mul c
  have hg''c : ContinuousOn
      (fun t : ℝ => c * (xiSpeedDeriv s t - k ^ (2 : ℕ) * xiSpeedDeriv s (k * t)))
      (Set.uIcc a b) := by
    have h1 : ContinuousOn (xiSpeedDeriv s) (Set.uIcc a b) :=
      (continuousOn_xiSpeedDeriv (by linarith)).mono hsub
    have h2 : ContinuousOn (fun t : ℝ => xiSpeedDeriv s (k * t)) (Set.uIcc a b) := by
      refine (continuousOn_xiSpeedDeriv (s := s) (by linarith)).comp
        ((continuous_const.mul continuous_id).continuousOn) ?_
      intro x hx
      exact hkx x hx
    exact continuousOn_const.mul (h1.sub (continuousOn_const.mul h2))
  have hg'lb : ∀ x ∈ Set.uIcc a b, lam ≤ c * xiDiffSpeed s k x := by
    intro x hx
    rw [hlamdef]
    exact mul_le_mul_of_nonneg_left (hfloor x hx) hc.le
  have hg''np : ∀ x ∈ Set.uIcc a b,
      c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)) ≤ 0 := by
    intro x hx
    have hneg := xiDiffSecond_neg (k := k) hs1 hk (hx1 x hx)
    nlinarith [hneg, hc.le]
  have hmain := _root_.RHTower.norm_integral_weight_cexp_le_anti hab hlam hw hw'c hwnn hwanti
    hg hg' hg''c hg'lb hg''np
  simpa [hlamdef] using hmain

/-- Weighted first-derivative cancellation after the stationary point, with an arbitrary supplied
negative speed floor. -/
theorem norm_integral_neg_diffPhase_block_le_of_speed_le
    {s c k a b η : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k)
    (hc : 0 < c) (hη : 0 < η) (hab : a ≤ b) (ha : 1 < a)
    (hfloor : ∀ x ∈ Set.uIcc a b, xiDiffSpeed s k x ≤ -η) :
    ‖∫ x in a..b, (ampFourthRoot s k x : ℂ)
        * Complex.exp (((-(c * xiDiffPhase s k x) : ℝ) : ℂ) * Complex.I)‖
      ≤ 4 * ampFourthRoot s k a / (c * η) := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have hsub : Set.uIcc a b ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hx1 : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < x := fun x hx => hsub hx
  have hkx : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < k * x := by
    intro x hx
    have := hx1 x hx
    nlinarith
  set lam : ℝ := c * η with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hw : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
    fun x hx => hasDerivAt_ampFourthRoot_of_one_lt hs1 hk (hx1 x hx)
  have hw'c : ContinuousOn (ampFourthRootDeriv s k) (Set.uIcc a b) :=
    (continuousOn_ampFourthRootDeriv_of_one_lt hs1 hk).mono hsub
  have hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ ampFourthRoot s k x :=
    fun x hx => (ampFourthRoot_pos_of_one_lt hs1 hk (hx1 x hx)).le
  have hwanti : ∀ x ∈ Set.uIcc a b, ampFourthRootDeriv s k x ≤ 0 :=
    fun x hx => ampFourthRootDeriv_nonpos_of_one_lt hs1 hk (hx1 x hx)
  have hg : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(c * xiDiffPhase s k t)) (-(c * xiDiffSpeed s k x)) x :=
    fun x hx => ((hasDerivAt_xiDiffPhase hs0 (hx1 x hx) (hkx x hx)).const_mul c).neg
  have hg' : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(c * xiDiffSpeed s k t))
        (-(c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)))) x :=
    fun x hx => ((hasDerivAt_xiDiffSpeed (by linarith) (hx1 x hx) (hkx x hx)).const_mul c).neg
  have hg''c : ContinuousOn
      (fun t : ℝ => -(c * (xiSpeedDeriv s t - k ^ (2 : ℕ) * xiSpeedDeriv s (k * t))))
      (Set.uIcc a b) := by
    have h1 : ContinuousOn (xiSpeedDeriv s) (Set.uIcc a b) :=
      (continuousOn_xiSpeedDeriv (by linarith)).mono hsub
    have h2 : ContinuousOn (fun t : ℝ => xiSpeedDeriv s (k * t)) (Set.uIcc a b) := by
      refine (continuousOn_xiSpeedDeriv (s := s) (by linarith)).comp
        ((continuous_const.mul continuous_id).continuousOn) ?_
      intro x hx
      exact hkx x hx
    exact (continuousOn_const.mul (h1.sub (continuousOn_const.mul h2))).neg
  have hg'lb : ∀ x ∈ Set.uIcc a b, lam ≤ -(c * xiDiffSpeed s k x) := by
    intro x hx
    rw [hlamdef]
    have hmul := mul_le_mul_of_nonneg_left (hfloor x hx) hc.le
    nlinarith
  have hg''nn : ∀ x ∈ Set.uIcc a b,
      0 ≤ -(c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x))) := by
    intro x hx
    have hneg := xiDiffSecond_neg (k := k) hs1 hk (hx1 x hx)
    nlinarith [hneg, hc.le]
  have hmain := _root_.RHTower.norm_integral_weight_cexp_le hab hlam hw hw'c hwnn hwanti
    hg hg' hg''c hg'lb hg''nn
  simpa [hlamdef] using hmain

/-- **The window block of `(13)`.**  On any subinterval of the stationary window the leading Bessel
term obeys the sharp bound `O(c^{-1/2} k^{-2})`, with the explicit constant `80`.

Every input is now unconditional: the amplitude is the elementary fourth root with the endpoint phases
cancelled, it is positive and decreasing with a continuous derivative, and the phase has second
derivative at least `c k³/16` in absolute value with a fixed sign.  The estimate itself is the corpus
weighted second-derivative van der Corput bound, whose right-hand side involves only the amplitude at
the left endpoint. -/
theorem norm_integral_window_block_le {s c k a b : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc : 0 < c) (hab : a ≤ b) (ha : 1 < a)
    (hwin : ∀ x ∈ Set.uIcc a b, 1 / (4 * k ^ (2 : ℕ)) ≤ x ^ (2 : ℕ) - 1 ∧ x ^ (2 : ℕ) - 1 ≤ 2 / k ^ (2 : ℕ)) :
    ‖∫ x in a..b, (ampFourthRoot s k x : ℂ)
        * Complex.exp (((-(c * xiDiffPhase s k x) : ℝ) : ℂ) * Complex.I)‖
      ≤ 80 / (Real.sqrt c * k ^ (2 : ℕ)) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hcs : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsub : Set.uIcc a b ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hx1 : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < x := fun x hx => hsub hx
  have hkx : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < k * x := by
    intro x hx
    have := hx1 x hx
    nlinarith
  set lam : ℝ := c * k ^ (3 : ℕ) / 16 with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  -- the weight
  have hw : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
    fun x hx => hasDerivAt_ampFourthRoot hs1 hk (hx1 x hx)
  have hw'c : ContinuousOn (ampFourthRootDeriv s k) (Set.uIcc a b) :=
    (continuousOn_ampFourthRootDeriv hs1 hk).mono hsub
  have hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ ampFourthRoot s k x :=
    fun x hx => (ampFourthRoot_pos hs1 hk (hx1 x hx)).le
  have hwanti : ∀ x ∈ Set.uIcc a b, ampFourthRootDeriv s k x ≤ 0 :=
    fun x hx => ampFourthRootDeriv_nonpos hs1 hk (hx1 x hx)
  -- the phase
  have hg : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(c * xiDiffPhase s k t)) (-(c * xiDiffSpeed s k x)) x := by
    intro x hx
    exact ((hasDerivAt_xiDiffPhase hs0 (hx1 x hx) (hkx x hx)).const_mul c).neg
  have hg' : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(c * xiDiffSpeed s k t))
        (-(c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)))) x := by
    intro x hx
    exact ((hasDerivAt_xiDiffSpeed (by linarith) (hx1 x hx) (hkx x hx)).const_mul c).neg
  have hg''c : ContinuousOn
      (fun t : ℝ => -(c * (xiSpeedDeriv s t - k ^ (2 : ℕ) * xiSpeedDeriv s (k * t))))
      (Set.uIcc a b) := by
    have h1 : ContinuousOn (xiSpeedDeriv s) (Set.uIcc a b) :=
      (continuousOn_xiSpeedDeriv (by linarith)).mono hsub
    have h2 : ContinuousOn (fun t : ℝ => xiSpeedDeriv s (k * t)) (Set.uIcc a b) := by
      refine (continuousOn_xiSpeedDeriv (s := s) (by linarith)).comp
        ((continuous_const.mul continuous_id).continuousOn) ?_
      intro x hx
      exact hkx x hx
    exact (continuousOn_const.mul (h1.sub (continuousOn_const.mul h2))).neg
  have hg''lb : ∀ x ∈ Set.uIcc a b,
      lam ≤ -(c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x))) := by
    intro x hx
    obtain ⟨hlo, hhi⟩ := hwin x hx
    have hxx := hx1 x hx
    have hbounds := abs_xiDiffSecond_window_bounds hs0 hs1 hk hxx hlo hhi
    have hneg := xiDiffSecond_neg (k := k) hs1 (by linarith : (1:ℝ) < k) hxx
    have habs : |xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)|
        = -(xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)) := abs_of_neg hneg
    rw [habs] at hbounds
    have hstep : k ^ (3 : ℕ) / 16 ≤ -(xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)) := hbounds.1
    rw [hlamdef]
    have hmul := mul_le_mul_of_nonneg_left hstep hc.le
    calc c * k ^ (3 : ℕ) / 16 = c * (k ^ (3 : ℕ) / 16) := by ring
      _ ≤ c * -(xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)) := hmul
      _ = -(c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x))) := by ring
  have hmain := _root_.RHTower.norm_integral_weight_cexp_secondDeriv hab hlam hw hw'c hwnn hwanti
    hg hg' hg''c hg''lb
  refine hmain.trans ?_
  -- the amplitude at the left endpoint
  have hA : ampFourthRoot s k a ≤ 2 / Real.sqrt k :=
    ampFourthRoot_le hs1 hk ha (hwin a Set.left_mem_uIcc).1
  have hks : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hlamsqrt : Real.sqrt lam = Real.sqrt c * Real.sqrt (k ^ (3 : ℕ)) / 4 := by
    rw [hlamdef, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_mul hc.le,
      show Real.sqrt (16 : ℝ) = 4 from by
        rw [show (16 : ℝ) = 4 ^ (2 : ℕ) from by norm_num, Real.sqrt_sq (by norm_num)]]
  have hk3 : Real.sqrt (k ^ (3 : ℕ)) * Real.sqrt k = k ^ (2 : ℕ) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show k ^ (3 : ℕ) * k = (k ^ (2 : ℕ)) ^ (2 : ℕ) from by ring, Real.sqrt_sq (by positivity)]
  rw [hlamsqrt]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hAk : ampFourthRoot s k a * Real.sqrt k ≤ 2 := by
    rw [← le_div_iff₀ hks]
    exact hA
  calc 10 * ampFourthRoot s k a * (Real.sqrt c * k ^ (2 : ℕ))
      = 10 * (Real.sqrt c * Real.sqrt (k ^ (3 : ℕ))) * (ampFourthRoot s k a * Real.sqrt k) := by
        rw [← hk3]
        ring
    _ ≤ 10 * (Real.sqrt c * Real.sqrt (k ^ (3 : ℕ))) * 2 :=
        mul_le_mul_of_nonneg_left hAk (by positivity)
    _ = 80 * (Real.sqrt c * Real.sqrt (k ^ (3 : ℕ)) / 4) := by ring

/-! ## The two off-window blocks -/

/-- **The outer block of `(13)`.**  Above the window the difference phase has no stationary point: its
derivative is at most `-k/8` and its second derivative keeps a fixed sign, so one integration by parts
gives `O(c^{-1} k^{-3/2})`, uniformly in the length of the block.  With `k <= c` this is smaller than the
window contribution. -/
theorem norm_integral_outer_block_le {s c k a b : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc : 0 < c) (hab : a ≤ b) (ha : 1 < a)
    (hout : ∀ x ∈ Set.uIcc a b, 2 / k ^ (2 : ℕ) ≤ x ^ (2 : ℕ) - 1) :
    ‖∫ x in a..b, (ampFourthRoot s k x : ℂ)
        * Complex.exp (((-(c * xiDiffPhase s k x) : ℝ) : ℂ) * Complex.I)‖
      ≤ 64 / (c * k * Real.sqrt k) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hks : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hsub : Set.uIcc a b ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hx1 : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < x := fun x hx => hsub hx
  have hkx : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < k * x := by
    intro x hx
    have := hx1 x hx
    nlinarith
  set lam : ℝ := c * k / 8 with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hw : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
    fun x hx => hasDerivAt_ampFourthRoot hs1 hk (hx1 x hx)
  have hw'c : ContinuousOn (ampFourthRootDeriv s k) (Set.uIcc a b) :=
    (continuousOn_ampFourthRootDeriv hs1 hk).mono hsub
  have hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ ampFourthRoot s k x :=
    fun x hx => (ampFourthRoot_pos hs1 hk (hx1 x hx)).le
  have hwanti : ∀ x ∈ Set.uIcc a b, ampFourthRootDeriv s k x ≤ 0 :=
    fun x hx => ampFourthRootDeriv_nonpos hs1 hk (hx1 x hx)
  have hg : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(c * xiDiffPhase s k t)) (-(c * xiDiffSpeed s k x)) x :=
    fun x hx => ((hasDerivAt_xiDiffPhase hs0 (hx1 x hx) (hkx x hx)).const_mul c).neg
  have hg' : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(c * xiDiffSpeed s k t))
        (-(c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)))) x :=
    fun x hx => ((hasDerivAt_xiDiffSpeed (by linarith) (hx1 x hx) (hkx x hx)).const_mul c).neg
  have hg''c : ContinuousOn
      (fun t : ℝ => -(c * (xiSpeedDeriv s t - k ^ (2 : ℕ) * xiSpeedDeriv s (k * t))))
      (Set.uIcc a b) := by
    have h1 : ContinuousOn (xiSpeedDeriv s) (Set.uIcc a b) :=
      (continuousOn_xiSpeedDeriv (by linarith)).mono hsub
    have h2 : ContinuousOn (fun t : ℝ => xiSpeedDeriv s (k * t)) (Set.uIcc a b) := by
      refine (continuousOn_xiSpeedDeriv (s := s) (by linarith)).comp
        ((continuous_const.mul continuous_id).continuousOn) ?_
      intro x hx
      exact hkx x hx
    exact (continuousOn_const.mul (h1.sub (continuousOn_const.mul h2))).neg
  have hg'lb : ∀ x ∈ Set.uIcc a b, lam ≤ -(c * xiDiffSpeed s k x) := by
    intro x hx
    have hsign := (xiDiffSpeed_le_of_outer hs0 hs1 hk (hx1 x hx) (hout x hx)).1
    rw [hlamdef]
    have hmul := mul_le_mul_of_nonneg_left hsign hc.le
    calc c * k / 8 = c * (k / 8) := by ring
      _ ≤ c * -xiDiffSpeed s k x := hmul
      _ = -(c * xiDiffSpeed s k x) := by ring
  have hg''nn : ∀ x ∈ Set.uIcc a b,
      0 ≤ -(c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x))) := by
    intro x hx
    have hneg := xiDiffSecond_neg (k := k) hs1 (by linarith : (1 : ℝ) < k) (hx1 x hx)
    nlinarith [hneg, hc.le]
  have hmain := _root_.RHTower.norm_integral_weight_cexp_le hab hlam hw hw'c hwnn hwanti
    hg hg' hg''c hg'lb hg''nn
  refine hmain.trans ?_
  have hA : ampFourthRoot s k a ≤ 2 / Real.sqrt k := by
    refine ampFourthRoot_le hs1 hk ha ?_
    have h := hout a Set.left_mem_uIcc
    have hstep : 1 / (4 * k ^ (2 : ℕ)) ≤ 2 / k ^ (2 : ℕ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hk0]
    linarith
  have hAk : ampFourthRoot s k a * Real.sqrt k ≤ 2 := by
    rw [← le_div_iff₀ hks]
    exact hA
  rw [hlamdef, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 4 * ampFourthRoot s k a * 8 * (c * k * Real.sqrt k)
      = 32 * (c * k) * (ampFourthRoot s k a * Real.sqrt k) := by ring
    _ ≤ 32 * (c * k) * 2 := by
        refine mul_le_mul_of_nonneg_left hAk (by positivity)
    _ = 64 * (c * k) := by ring

/-- **The inner block of `(13)`.**  Below the window the derivative of the difference phase is at least
`k/5`, so the same integration by parts gives `O(w(a)/(c k))` with `w(a)` the amplitude at the left end
of the block.  The amplitude is unbounded as the block reaches the endpoint, which is exactly why the
endpoint layer `(12)` is split off first. -/
theorem norm_integral_inner_block_le {s c k a b : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc : 0 < c) (hab : a ≤ b) (ha : 1 < a)
    (hin : ∀ x ∈ Set.uIcc a b, x ^ (2 : ℕ) - 1 ≤ 1 / (4 * k ^ (2 : ℕ))) :
    ‖∫ x in a..b, (ampFourthRoot s k x : ℂ)
        * Complex.exp (((c * xiDiffPhase s k x : ℝ) : ℂ) * Complex.I)‖
      ≤ 20 * ampFourthRoot s k a / (c * k) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hsub : Set.uIcc a b ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hx1 : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < x := fun x hx => hsub hx
  have hkx : ∀ x ∈ Set.uIcc a b, (1 : ℝ) < k * x := by
    intro x hx
    have := hx1 x hx
    nlinarith
  set lam : ℝ := c * k / 5 with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hw : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
    fun x hx => hasDerivAt_ampFourthRoot hs1 hk (hx1 x hx)
  have hw'c : ContinuousOn (ampFourthRootDeriv s k) (Set.uIcc a b) :=
    (continuousOn_ampFourthRootDeriv hs1 hk).mono hsub
  have hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ ampFourthRoot s k x :=
    fun x hx => (ampFourthRoot_pos hs1 hk (hx1 x hx)).le
  have hwanti : ∀ x ∈ Set.uIcc a b, ampFourthRootDeriv s k x ≤ 0 :=
    fun x hx => ampFourthRootDeriv_nonpos hs1 hk (hx1 x hx)
  have hg : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => c * xiDiffPhase s k t) (c * xiDiffSpeed s k x) x :=
    fun x hx => (hasDerivAt_xiDiffPhase hs0 (hx1 x hx) (hkx x hx)).const_mul c
  have hg' : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => c * xiDiffSpeed s k t)
        (c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x))) x :=
    fun x hx => (hasDerivAt_xiDiffSpeed (by linarith) (hx1 x hx) (hkx x hx)).const_mul c
  have hg''c : ContinuousOn
      (fun t : ℝ => c * (xiSpeedDeriv s t - k ^ (2 : ℕ) * xiSpeedDeriv s (k * t))) (Set.uIcc a b) := by
    have h1 : ContinuousOn (xiSpeedDeriv s) (Set.uIcc a b) :=
      (continuousOn_xiSpeedDeriv (by linarith)).mono hsub
    have h2 : ContinuousOn (fun t : ℝ => xiSpeedDeriv s (k * t)) (Set.uIcc a b) := by
      refine (continuousOn_xiSpeedDeriv (s := s) (by linarith)).comp
        ((continuous_const.mul continuous_id).continuousOn) ?_
      intro x hx
      exact hkx x hx
    exact continuousOn_const.mul (h1.sub (continuousOn_const.mul h2))
  have hg'lb : ∀ x ∈ Set.uIcc a b, lam ≤ c * xiDiffSpeed s k x := by
    intro x hx
    have hsign := (xiDiffSpeed_ge_of_inner hs0 hs1 hk (hx1 x hx) (hin x hx)).1
    rw [hlamdef]
    have hmul := mul_le_mul_of_nonneg_left hsign hc.le
    calc c * k / 5 = c * (k / 5) := by ring
      _ ≤ c * xiDiffSpeed s k x := hmul
  have hg''np : ∀ x ∈ Set.uIcc a b,
      c * (xiSpeedDeriv s x - k ^ (2 : ℕ) * xiSpeedDeriv s (k * x)) ≤ 0 := by
    intro x hx
    have hneg := xiDiffSecond_neg (k := k) hs1 (by linarith : (1 : ℝ) < k) (hx1 x hx)
    nlinarith [hneg, hc.le]
  have hmain := _root_.RHTower.norm_integral_weight_cexp_le_anti hab hlam hw hw'c hwnn hwanti
    hg hg' hg''c hg'lb hg''np
  refine hmain.trans ?_
  rw [hlamdef]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hAnn : 0 ≤ ampFourthRoot s k a := (ampFourthRoot_pos hs1 hk ha).le
  nlinarith [hAnn, hc.le, hk0.le]

end GaloisForLFunctions.RHTower

end
