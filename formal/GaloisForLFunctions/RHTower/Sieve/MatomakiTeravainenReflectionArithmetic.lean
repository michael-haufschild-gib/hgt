import GaloisForLFunctions.RHTower.Sieve.UnitBlockReflectionFourthMoment

/-!
# Bookkeeping for the reflection branch of Matomäki–Teräväinen Lemma 3.5

Elementary inequalities that turn the outputs of the reflection argument into the shape of the
Deshouillers–Iwaniec and Watt bounds.

* `one_add_log_pow_four_le_mul_rpow`: `(1 + log T)⁴ ≤ (1 + 1/ε)⁴ T^{4ε}`.
* `ub_error_le`: the reflection error `X⁴`, `X = (1 + log T)/N + T^{-1/2}`, against the mean value
  `(5πe/A + (5π/2)T/A²)S` costs at most `K(1 + log T)⁴ (T + A²√T)/(N²A) · S/A` when `N < T`.
* `ub_overHeight_le`: the over-height bound has the shape `K (T + A)/(T⁴A) · S/A`.
* `ub_numDI_scale`, `ub_numW_scale`, `ub_tail_scale`: moving the window from `T` to `T' ∈ [T/2, 5T/4]`
  changes the numerators by at most `5/4` and the tail term by at most `20`.
* `ub_dualBase_ge`, `ub_Y_sq_le`: `M ≥ Y/9` and `Y² ≤ T/32` in the reflection range.
* `exists_norm_mtWattUnitBlock_le_short_dual`: if the dual length `Y = T/(2πN)` is at most `11`, the
  reflected block is `O((1 + log T)/N + T^{-1/2})` pointwise.
-/

open Complex Set MeasureTheory Filter
open scoped Real

namespace RHTower.Sieve

noncomputable section

/-- `(1 + log T)⁴ ≤ (1 + 1/ε)⁴ T^{4ε}` for `T ≥ 1`. -/
theorem one_add_log_pow_four_le_mul_rpow {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 1 ≤ T) :
    (1 + Real.log T) ^ 4 ≤ (1 + 1 / ε) ^ 4 * T ^ (4 * ε) := by
  have h1 : Real.log T ≤ T ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  have h2 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have h3 : 1 + Real.log T ≤ (1 + 1 / ε) * T ^ ε := by
    have : T ^ ε / ε = (1 / ε) * T ^ ε := by ring
    nlinarith
  have h4 : (T ^ ε) ^ 4 = T ^ (4 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; ring_nf
  calc (1 + Real.log T) ^ 4 ≤ ((1 + 1 / ε) * T ^ ε) ^ 4 :=
        pow_le_pow_left₀ (by linarith) h3 4
    _ = (1 + 1 / ε) ^ 4 * T ^ (4 * ε) := by rw [mul_pow, h4]

private theorem ub_err_combine {c d L4 x y r p1 p2 : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hL4 : 1 ≤ L4) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (h1 : x ≤ L4 * p2) (h2 : x * r ≤ L4 * p1)
    (h3 : y ≤ p2) (h4 : y * r ≤ p1) :
    (x + y) * (c + d * r) ≤ 2 * (c + d) * L4 * (p1 + p2) := by
  have e : (x + y) * (c + d * r) = c * x + c * y + d * (x * r) + d * (y * r) := by ring
  rw [e]
  have a1 := mul_le_mul_of_nonneg_left h1 hc
  have a2 := mul_le_mul_of_nonneg_left h3 hc
  have a3 := mul_le_mul_of_nonneg_left h2 hd
  have a4 := mul_le_mul_of_nonneg_left h4 hd
  have b1 : c * p2 ≤ c * L4 * p2 := by
    have := mul_le_mul_of_nonneg_left hL4 (mul_nonneg hc hp2); nlinarith
  have b2 : d * p1 ≤ d * L4 * p1 := by
    have := mul_le_mul_of_nonneg_left hL4 (mul_nonneg hd hp1); nlinarith
  have b3 : 0 ≤ c * L4 * p1 := by positivity
  have b4 : 0 ≤ d * L4 * p2 := by positivity
  nlinarith

private theorem ub_err_terms {T N A L4 : ℝ} (hT : 1 ≤ T) (hN : 1 ≤ N) (hNT : N ≤ T) (hA : 1 ≤ A)
    (hL4 : 0 ≤ L4) :
    L4 / N ^ 4 ≤ L4 * (A ^ 2 * Real.sqrt T / (N ^ 2 * A)) ∧
    L4 / N ^ 4 * (T / A) ≤ L4 * (T / (N ^ 2 * A)) ∧
    1 / T ^ 2 ≤ A ^ 2 * Real.sqrt T / (N ^ 2 * A) ∧
    1 / T ^ 2 * (T / A) ≤ T / (N ^ 2 * A) := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hA0 : 0 < A := by linarith
  have hsT1 : 1 ≤ Real.sqrt T := by rw [Real.one_le_sqrt]; exact hT
  have hAs : 1 ≤ A * Real.sqrt T := by nlinarith
  have e : A ^ 2 * Real.sqrt T / (N ^ 2 * A) = A * Real.sqrt T / N ^ 2 := by field_simp
  have hN24 : N ^ 2 ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
  have hNT2 : N ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hN0.le hNT 2
  have k1 : 1 / N ^ 4 ≤ 1 / N ^ 2 := one_div_le_one_div_of_le (by positivity) hN24
  have k2 : 1 / N ^ 2 ≤ A * Real.sqrt T / N ^ 2 := div_le_div_of_nonneg_right hAs (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, div_eq_mul_one_div L4]
    exact mul_le_mul_of_nonneg_left (k1.trans k2) hL4
  · rw [show L4 / N ^ 4 * (T / A) = L4 * (T / (N ^ 4 * A)) by ring]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hT0.le (by positivity)
      (mul_le_mul_of_nonneg_right hN24 hA0.le)) hL4
  · rw [e]
    exact (one_div_le_one_div_of_le (by positivity) hNT2).trans k2
  · rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have : N ^ 2 * A ≤ T ^ 2 * A := mul_le_mul_of_nonneg_right hNT2 hA0.le
    nlinarith

/-- **The reflection error against the mean value.** -/
theorem ub_error_le {T N A S : ℝ} (hT : 1 ≤ T) (hN : 1 ≤ N) (hNT : N < T) (hA : 1 ≤ A)
    (hS : 0 ≤ S) :
    ((1 + Real.log T) / N + 1 / Real.sqrt T) ^ 4 *
        ((5 * π * Real.exp 1 * (1 / A) + (5 * π / 2) * (1 / A ^ 2) * T) * S) ≤
      16 * (5 * π * Real.exp 1 + 5 * π / 2) * (1 + Real.log T) ^ 4 *
        ((T + A ^ 2 * Real.sqrt T) / (N ^ 2 * A) * (1 / A * S)) := by
  have hT0 : 0 < T := by linarith
  have hA0 : 0 < A := by linarith
  have hL : 1 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  obtain ⟨L, hLdef⟩ : ∃ L, L = 1 + Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hL ⊢
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hs4 : (1 / Real.sqrt T) ^ 4 = 1 / T ^ 2 := by
    rw [div_pow, one_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hT0.le]
  have hX : (L / N + 1 / Real.sqrt T) ^ 4 ≤ 8 * (L ^ 4 / N ^ 4 + 1 / T ^ 2) := by
    have := add_pow_four_le (L / N) (1 / Real.sqrt T)
    rwa [hs4, div_pow] at this
  have hπe : 0 < 5 * π * Real.exp 1 := by positivity
  have hMV : (5 * π * Real.exp 1 * (1 / A) + (5 * π / 2) * (1 / A ^ 2) * T) * S =
      (5 * π * Real.exp 1 + (5 * π / 2) * (T / A)) * (1 / A * S) := by
    field_simp
  rw [hMV]
  have hE0 : 0 ≤ 1 / A * S := by positivity
  obtain ⟨t1, t2, t3, t4⟩ := ub_err_terms hT hN hNT.le hA (by positivity : (0 : ℝ) ≤ L ^ 4)
  have hK := ub_err_combine hπe.le (by positivity : (0 : ℝ) ≤ 5 * π / 2)
    (one_le_pow₀ hL : 1 ≤ L ^ 4) (by positivity : (0 : ℝ) ≤ T / (N ^ 2 * A))
    (by positivity : (0 : ℝ) ≤ A ^ 2 * Real.sqrt T / (N ^ 2 * A)) t1 t2 t3 t4
  have hK' : (L ^ 4 / N ^ 4 + 1 / T ^ 2) * (5 * π * Real.exp 1 + 5 * π / 2 * (T / A)) ≤
      2 * (5 * π * Real.exp 1 + 5 * π / 2) * L ^ 4 * ((T + A ^ 2 * Real.sqrt T) / (N ^ 2 * A)) := by
    rw [add_div]; exact hK
  calc (L / N + 1 / Real.sqrt T) ^ 4 * ((5 * π * Real.exp 1 + (5 * π / 2) * (T / A)) *
        (1 / A * S))
      ≤ 8 * (L ^ 4 / N ^ 4 + 1 / T ^ 2) * ((5 * π * Real.exp 1 + (5 * π / 2) * (T / A)) *
          (1 / A * S)) :=
        mul_le_mul_of_nonneg_right hX (by positivity)
    _ = 8 * ((L ^ 4 / N ^ 4 + 1 / T ^ 2) * (5 * π * Real.exp 1 + 5 * π / 2 * (T / A))) *
          (1 / A * S) := by ring
    _ ≤ 8 * (2 * (5 * π * Real.exp 1 + 5 * π / 2) * L ^ 4 *
          ((T + A ^ 2 * Real.sqrt T) / (N ^ 2 * A))) * (1 / A * S) := by
        gcongr
    _ = 16 * (5 * π * Real.exp 1 + 5 * π / 2) * L ^ 4 *
          ((T + A ^ 2 * Real.sqrt T) / (N ^ 2 * A) * (1 / A * S)) := by ring

/-- **The over-height bound in the tail shape.** -/
theorem ub_overHeight_le {T A S : ℝ} (hT : 0 < T) (hA : 0 < A) (hS : 0 ≤ S) :
    (2 * (6 * π + 1) / T) ^ 4 * (5 * π * Real.exp 1 * (1 / A) + (5 * π / 2) * (1 / A ^ 2) * T) * S ≤
      (2 * (6 * π + 1)) ^ 4 * (5 * π * Real.exp 1) * ((T + A) / (T ^ 4 * A) * (1 / A * S)) := by
  have hπ2 : 5 * π / 2 ≤ 5 * π * Real.exp 1 := by
    have := Real.add_one_le_exp 1
    have := Real.pi_pos
    nlinarith
  have e1 : (2 * (6 * π + 1) / T) ^ 4 * (5 * π * Real.exp 1 * (1 / A) +
      (5 * π / 2) * (1 / A ^ 2) * T) * S = (2 * (6 * π + 1)) ^ 4 *
      ((5 * π * Real.exp 1 * A + (5 * π / 2) * T) / (T ^ 4 * A ^ 2)) * S := by
    field_simp
  have e2 : (2 * (6 * π + 1)) ^ 4 * (5 * π * Real.exp 1) * ((T + A) / (T ^ 4 * A) * (1 / A * S)) =
      (2 * (6 * π + 1)) ^ 4 * ((5 * π * Real.exp 1 * (T + A)) / (T ^ 4 * A ^ 2)) * S := by
    field_simp
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right ?_ (by positivity)) (by positivity)) hS
  nlinarith [mul_le_mul_of_nonneg_right hπ2 hT.le]

/-- The Deshouillers–Iwaniec numerator grows by at most `5/4` from `T` to `T' ≤ 5T/4`. -/
theorem ub_numDI_scale {T T' A : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T') (hTT' : T' ≤ 5 * T / 4)
    (hA : 0 ≤ A) :
    T' + A ^ 2 * Real.sqrt T' + A ^ (5 / 4 : ℝ) * T' ^ (3 / 4 : ℝ) ≤
      5 / 4 * (T + A ^ 2 * Real.sqrt T + A ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
  have hs : Real.sqrt T' ≤ 5 / 4 * Real.sqrt T := by
    calc Real.sqrt T' ≤ Real.sqrt (5 / 4 * T) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt (5 / 4) * Real.sqrt T := Real.sqrt_mul (by norm_num) T
      _ ≤ 5 / 4 * Real.sqrt T := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hr : T' ^ (3 / 4 : ℝ) ≤ 5 / 4 * T ^ (3 / 4 : ℝ) := by
    calc T' ^ (3 / 4 : ℝ) ≤ (5 / 4 * T) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow hT' (by linarith) (by norm_num)
      _ = (5 / 4) ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := Real.mul_rpow (by norm_num) hT
      _ ≤ 5 / 4 * T ^ (3 / 4 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (5 / 4 : ℝ) ^ (3 / 4 : ℝ) ≤ (5 / 4) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 5 / 4 := Real.rpow_one _
  have h1 := mul_le_mul_of_nonneg_left hs (sq_nonneg A)
  have h2 := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ A ^ (5 / 4 : ℝ))
  nlinarith

/-- The Watt numerator grows by at most `5/4` from `T` to `T' ≤ 5T/4`. -/
theorem ub_numW_scale {T T' A : ℝ} (hT' : 0 ≤ T') (hTT' : T' ≤ 5 * T / 4) :
    T' + A ^ 2 * Real.sqrt T' ≤ 5 / 4 * (T + A ^ 2 * Real.sqrt T) := by
  have hT : 0 ≤ T := by linarith
  have hs : Real.sqrt T' ≤ 5 / 4 * Real.sqrt T := by
    calc Real.sqrt T' ≤ Real.sqrt (5 / 4 * T) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt (5 / 4) * Real.sqrt T := Real.sqrt_mul (by norm_num) T
      _ ≤ 5 / 4 * Real.sqrt T := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h1 := mul_le_mul_of_nonneg_left hs (sq_nonneg A)
  nlinarith

/-- The tail term grows by at most `20` on `[T/2, 5T/4]`. -/
theorem ub_tail_scale {T T' A : ℝ} (hT : 0 < T) (hA : 0 < A) (h1 : T / 2 ≤ T')
    (h2 : T' ≤ 5 * T / 4) :
    (T' + A) / (T' ^ 4 * A) ≤ 20 * ((T + A) / (T ^ 4 * A)) := by
  have hT' : 0 < T' := by linarith
  have h4 : T ^ 4 / 16 ≤ T' ^ 4 := by
    have := pow_le_pow_left₀ (by linarith) h1 4
    have e : (T / 2) ^ 4 = T ^ 4 / 16 := by ring
    linarith
  rw [div_le_iff₀ (by positivity), mul_assoc, mul_comm ((T + A) / (T ^ 4 * A)), ← mul_assoc,
    show 20 * (T' ^ 4 * A) * ((T + A) / (T ^ 4 * A)) = 20 * T' ^ 4 * (T + A) / T ^ 4 by
      field_simp]
  rw [le_div_iff₀ (by positivity)]
  have hTA : T' + A ≤ 5 / 4 * (T + A) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 20 * (T + A)),
    mul_le_mul_of_nonneg_left hTA (by positivity : (0 : ℝ) ≤ T ^ 4)]

/-- `Y² ≤ T/32` for `Y = T/(2πN)` and `T < N²`. -/
theorem ub_Y_sq_le {T N : ℝ} (hN : 1 ≤ N) (hT : 0 < T) (hTN : T < N ^ 2) :
    (T / (2 * π * N)) ^ 2 ≤ T / 32 := by
  have hπ : 3 < π := Real.pi_gt_three
  rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : T * T < T * N ^ 2 := mul_lt_mul_of_pos_left hTN hT
  have e : T * (2 * π * N) ^ 2 = T * N ^ 2 * (4 * π ^ 2) := by ring
  rw [e]
  have h2 : 32 ≤ 4 * π ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ T * N ^ 2)]

/-- `M ≥ Y/9` for the dual base, once `Y = T/(2πN) ≥ 9`. -/
theorem ub_dualBase_ge {N N' : ℕ} (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N) {T : ℝ}
    (hT : 0 < T) (hY : 9 ≤ T / (2 * π * N)) :
    T / (2 * π * N) / 9 ≤ ubDualBase N' T := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN'r : (N : ℝ) + 1 ≤ N' := by exact_mod_cast hNN'
  have hN'2 : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'
  obtain ⟨hxlo, -⟩ := ubDualBase_bounds hT hN1 hNN'r hN'2
  have h := Nat.sub_one_lt_floor (T / (4 * π * ((N' : ℝ) + 1 / 4)))
  rw [ubDualBase]
  linarith

/-- **The short-dual pointwise bound.**  If the dual length `T/(2πN)` is at most `11`, the
reflected block is `O((1 + log T)/N + T^{-1/2})` on `[T/2, T]`. -/
theorem exists_norm_mtWattUnitBlock_le_short_dual :
    ∃ C : ℝ, 0 < C ∧ ∀ (N N' : ℕ), 1 ≤ N → N < N' → N' ≤ 2 * N → ∀ T : ℝ, 2 ≤ T →
      (N : ℝ) < T → T < (N : ℝ) ^ 2 → T / (2 * π * N) ≤ 11 → ∀ t ∈ Icc (T / 2) T,
      ‖mtWattUnitBlock N N' t‖ ≤ C * ((1 + Real.log T) / N + 1 / Real.sqrt T) := by
  obtain ⟨C, hC, hdual⟩ := exists_norm_mtWattUnitBlock_le_dual
  refine ⟨2 * C + 506, by positivity, fun N N' hN hNN' hN' T hT2 hNT hTN hY t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := ht
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have h := hdual N N' hN hNN' hN' t (by linarith) (by nlinarith) (by linarith)
  have hS := norm_sum_ubDual_le (N := N) (N' := N') ht0
  have hS' : t / (2 * π * ((N : ℝ) + 3 / 4)) ≤ 11 := by
    refine le_trans (div_le_div₀ hT0.le ht2 (by positivity) (by nlinarith [Real.pi_pos])) hY
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hst : Real.sqrt T / 2 ≤ Real.sqrt t := by
    have : Real.sqrt (T / 4) = Real.sqrt T / 2 := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    calc Real.sqrt T / 2 = Real.sqrt (T / 4) := this.symm
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
  have hinv : 1 / Real.sqrt t ≤ 2 / Real.sqrt T := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 ht0) hsT]; linarith
  have hlog : Real.log t ≤ Real.log T := Real.log_le_log ht0 ht2
  have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have a1 : (1 + Real.log t) / N ≤ (1 + Real.log T) / N :=
    div_le_div_of_nonneg_right (by linarith) hN0.le
  have a2 : 0 ≤ (1 + Real.log T) / N := div_nonneg (by linarith) hN0.le
  have hE : C * ((1 + Real.log t) / N + 1 / Real.sqrt t) ≤
      2 * C * ((1 + Real.log T) / N + 1 / Real.sqrt T) := by
    have : (1 + Real.log t) / N + 1 / Real.sqrt t ≤ 2 * ((1 + Real.log T) / N + 1 / Real.sqrt T) := by
      have : 2 / Real.sqrt T = 2 * (1 / Real.sqrt T) := by ring
      linarith
    calc C * ((1 + Real.log t) / N + 1 / Real.sqrt t) ≤
        C * (2 * ((1 + Real.log T) / N + 1 / Real.sqrt T)) := mul_le_mul_of_nonneg_left this hC.le
      _ = 2 * C * ((1 + Real.log T) / N + 1 / Real.sqrt T) := by ring
  have hR : 23 / Real.sqrt t * ‖∑ k ∈ ubDual N N' t, (k : ℂ) ^ ((t : ℂ) * I)‖ ≤
      506 * (1 / Real.sqrt T) := by
    have h23 : 23 / Real.sqrt t ≤ 46 / Real.sqrt T := by
      have := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 23)
      rw [mul_one_div, show (23 : ℝ) * (2 / Real.sqrt T) = 46 / Real.sqrt T by ring] at this
      exact this
    calc 23 / Real.sqrt t * ‖∑ k ∈ ubDual N N' t, (k : ℂ) ^ ((t : ℂ) * I)‖ ≤
        46 / Real.sqrt T * 11 := mul_le_mul h23 (hS.trans hS') (norm_nonneg _) (by positivity)
      _ = 506 * (1 / Real.sqrt T) := by ring
  have : 0 ≤ 1 / Real.sqrt T := by positivity
  nlinarith

/-- **The main term of the reflection branch.**  With `Y ≥ 9`, `M ≥ Y/9`, `Y² ≤ T/32`,
`Y·2πN = T` and nonnegative numerator, tail and energy,
`(Y⁴/T²)((5/4)Num/(M²A) + 20Q) ≤ 4(Num/(N²A) + Q)`. -/
theorem ub_main_shape {Y T N M A Num Q : ℝ} (hY : 9 ≤ Y) (hN : 1 ≤ N) (hA : 0 < A)
    (hM : Y / 9 ≤ M) (hY2 : Y ^ 2 ≤ T / 32) (hTY : T = 2 * π * N * Y) (hNum : 0 ≤ Num)
    (hQ : 0 ≤ Q) :
    Y ^ 4 / T ^ 2 * (5 / 4 * Num / (M ^ 2 * A) + 20 * Q) ≤ 4 * (Num / (N ^ 2 * A) + Q) := by
  have hπ : 3 < π := Real.pi_gt_three
  have hY0 : 0 < Y := by linarith
  have hN0 : 0 < N := by linarith
  have hT0 : 0 < T := by rw [hTY]; positivity
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  -- `Y⁴/(T²M²) ≤ 81/(4π²N²) ≤ 3/N²`
  have k1 : Y ^ 4 / T ^ 2 / M ^ 2 ≤ 3 / N ^ 2 := by
    have hM2 : (Y / 9) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) hM 2
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), hTY]
    have e1 : Y ^ 4 * N ^ 2 = 81 * (Y / 9) ^ 2 * (Y ^ 2 * N ^ 2) := by ring
    have e2 : 3 * ((2 * π * N * Y) ^ 2 * M ^ 2) = 12 * π ^ 2 * (Y ^ 2 * N ^ 2) * M ^ 2 := by ring
    rw [e1, e2]
    have hYN : 0 ≤ Y ^ 2 * N ^ 2 := by positivity
    have hπ2 : 81 ≤ 12 * π ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hM2 hYN, mul_le_mul_of_nonneg_right hπ2
      (mul_nonneg hYN (sq_nonneg M))]
  have k2 : Y ^ 4 / T ^ 2 ≤ 1 / 1024 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := pow_le_pow_left₀ (sq_nonneg Y) hY2 2
    nlinarith
  have e : Y ^ 4 / T ^ 2 * (5 / 4 * Num / (M ^ 2 * A) + 20 * Q) =
      5 / 4 * (Y ^ 4 / T ^ 2 / M ^ 2) * (Num / A) + 20 * (Y ^ 4 / T ^ 2) * Q := by
    field_simp
  rw [e]
  have hNA : 0 ≤ Num / A := by positivity
  have f1 : 5 / 4 * (Y ^ 4 / T ^ 2 / M ^ 2) * (Num / A) ≤ 4 * (Num / (N ^ 2 * A)) := by
    have : 5 / 4 * (Y ^ 4 / T ^ 2 / M ^ 2) ≤ 4 / N ^ 2 := by
      have : 5 / 4 * (3 / N ^ 2) ≤ 4 / N ^ 2 := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]; norm_num
      nlinarith
    calc 5 / 4 * (Y ^ 4 / T ^ 2 / M ^ 2) * (Num / A) ≤ 4 / N ^ 2 * (Num / A) :=
          mul_le_mul_of_nonneg_right this hNA
      _ = 4 * (Num / (N ^ 2 * A)) := by field_simp
  have f2 : 20 * (Y ^ 4 / T ^ 2) * Q ≤ 4 * Q := by nlinarith
  linarith

end

end RHTower.Sieve
