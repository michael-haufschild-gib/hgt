import GaloisForLFunctions.RHTower.XiSliceBoundedOrderPolynomialRate
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxScaledLength

/-!
# Bounded-order slice positivity at almost every height, with a stretched-exponential rate

There is `C` such that for every `K ≥ 1` and all large `T`, the heights `t ∈ [T, 2T]` with
`c_{2k}(t) ≤ 0` for some order `k ≥ K` have measure at most `C T e^{−√K/6}`
(`eventually_volume_xiSliceCoeff_nonpos_bounded_order_stretched_le`).

The dyadic scales `κ_j = 2^j κ₀`, `κ₀ = K/2`, carry the scale bound
`C T e^{−√κ_j/4} + C T^{1/2}` of `exists_volume_not_zetaLogDerivScaleData_le_sqrt`, where the
explicit-formula length `T^{1/√κ}` and the prime-moment order `⌊√κ/4⌋` grow with the scale. Since
`√(2^j κ₀) ≥ (1 + 2j/5)√κ₀`, each scale costs `≤ C T e^{−√κ₀/4} 2^{−j} + C T^{1/2}`
(`volume_dyadic_scale_sqrt_le`).
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped ComplexOrder

namespace RHTower

/-- `√(2^j κ₀) ≥ (1 + 2j/5) √κ₀`. -/
theorem one_add_mul_sqrt_le_sqrt_two_pow_mul {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (j : ℕ) :
    (1 + 2 * (j : ℝ) / 5) * Real.sqrt κ₀ ≤ Real.sqrt (2 ^ j * κ₀) := by
  have hb := one_add_mul_le_pow (a := (2 / 5 : ℝ)) (by norm_num) j
  have h1 : (1 + 2 * (j : ℝ) / 5) ^ 2 ≤ 2 ^ j := by
    have h0 : (0 : ℝ) ≤ 1 + 2 * (j : ℝ) / 5 := by positivity
    have e : 1 + 2 * (j : ℝ) / 5 = 1 + (j : ℝ) * (2 / 5) := by ring
    calc (1 + 2 * (j : ℝ) / 5) ^ 2 ≤ ((1 + 2 / 5) ^ j) ^ 2 := by
          rw [e]; exact pow_le_pow_left₀ (by rw [← e]; exact h0) hb 2
      _ = ((1 + 2 / 5) ^ 2) ^ j := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ 2 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
  rw [mul_pow, Real.sq_sqrt hκ₀]
  exact mul_le_mul_of_nonneg_right h1 hκ₀

/-- `e^{−√(2^j κ₀)/4} ≤ e^{−√κ₀/4} 2^{−j}` for `κ₀ ≥ 49`. -/
theorem exp_neg_sqrt_two_pow_le {κ₀ : ℝ} (hκ₀ : 49 ≤ κ₀) (j : ℕ) :
    Real.exp (-(Real.sqrt (2 ^ j * κ₀) / 4)) ≤ Real.exp (-(Real.sqrt κ₀ / 4)) * (1 / 2) ^ j := by
  have h7 : 7 ≤ Real.sqrt κ₀ := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hs := one_add_mul_sqrt_le_sqrt_two_pow_mul (by linarith : (0 : ℝ) ≤ κ₀) j
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hhalf : ((1 : ℝ) / 2) ^ j = Real.exp (-(j * Real.log 2)) := by
    have h2 : Real.exp (j * Real.log 2) = 2 ^ j := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [Real.exp_neg, h2, one_div_pow, one_div]
  rw [hhalf, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_two_lt_d9
  have : (j : ℝ) * Real.log 2 ≤ 2 * (j : ℝ) / 5 * Real.sqrt κ₀ / 4 := by
    have h1 : (j : ℝ) * Real.log 2 ≤ (j : ℝ) * (7 / 10) :=
      mul_le_mul_of_nonneg_left (by norm_num at hlog; linarith) hj0
    have h2 : (j : ℝ) * (7 / 10) ≤ 2 * (j : ℝ) / 5 * Real.sqrt κ₀ / 4 := by nlinarith
    linarith
  nlinarith

/-- The measure of the heights without data at the dyadic scale `2^j κ₀/log T`, at the stretched
rate. -/
theorem volume_dyadic_scale_sqrt_le {C T ε κ₀ : ℝ} (j : ℕ) (hT0 : 1 < T) (hC : 0 < C)
    (hκ₀ : max (9 * 10 ^ 8) (1000 / ε ^ 2) ≤ κ₀) (hj16 : 2 ^ j * κ₀ / Real.log T ≤ 1 / 16)
    (hTev : ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → max (9 * 10 ^ 8) (1000 / ε ^ 2) ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (ε * Real.log T)} ≤
        ENNReal.ofReal (C * T * Real.exp (-(Real.sqrt (R * Real.log T) / 4)) +
          C * T ^ ((1 : ℝ) / 2))) :
    volume {t | t ∈ Icc T (2 * T) ∧
        ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} ≤
      ENNReal.ofReal (C * Real.exp (-(Real.sqrt κ₀ / 4)) * T * (1 / 2) ^ j / 1 +
        C * T ^ ((1 : ℝ) / 2)) := by
  have hL0 : 0 < Real.log T := Real.log_pos hT0
  have hRL : 2 ^ j * κ₀ / Real.log T * Real.log T = 2 ^ j * κ₀ := div_mul_cancel₀ _ hL0.ne'
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hκ9 : 9 * 10 ^ 8 ≤ κ₀ := le_trans (le_max_left _ _) hκ₀
  have hκ₀0 : 0 < κ₀ := by linarith
  refine (hTev _ (by positivity) hj16 (by rw [hRL]; exact hκ₀.trans (le_mul_of_one_le_left
    hκ₀0.le h2j))).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hRL]
  have h := exp_neg_sqrt_two_pow_le (by linarith : (49 : ℝ) ≤ κ₀) j
  have hT : 0 ≤ T := by linarith
  have := mul_le_mul_of_nonneg_left h (show 0 ≤ C * T by positivity)
  have e : C * T * (Real.exp (-(Real.sqrt κ₀ / 4)) * (1 / 2) ^ j) =
      C * Real.exp (-(Real.sqrt κ₀ / 4)) * T * (1 / 2) ^ j / 1 := by ring
  linarith

/-- `e^{−√(K/2)/4} ≤ e^{−√K/6}`. -/
theorem exp_neg_sqrt_half_le {K : ℝ} (hK : 0 ≤ K) :
    Real.exp (-(Real.sqrt (K / 2) / 4)) ≤ Real.exp (-(Real.sqrt K / 6)) := by
  apply Real.exp_le_exp.mpr
  have h : 2 / 3 * Real.sqrt K ≤ Real.sqrt (K / 2) := by
    refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
    rw [mul_pow, Real.sq_sqrt hK]
    nlinarith
  linarith

/-- **Slice positivity at bounded orders for almost every height, with a stretched-exponential
rate.** There is `C` such that for every `K ≥ 1` and all large `T`, the heights `t ∈ [T, 2T]` with
`c_{2k}(t) ≤ 0` for some `k ≥ K` have measure at most `C T e^{−√K/6}`. -/
theorem eventually_volume_xiSliceCoeff_nonpos_bounded_order_stretched_le :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K → ∀ᶠ T in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ≤
        ENNReal.ofReal (C * T * Real.exp (-(Real.sqrt K / 6))) := by
  obtain ⟨k₁, -, hpos⟩ := exists_xiSliceCoeff_pos_of_logDerivScaleData
  set ε : ℝ := 1 / 10 ^ 9 with hε
  have hε0 : 0 < ε := by norm_num
  obtain ⟨C, hC, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le_sqrt hε0 (by norm_num)
  set K₀ : ℝ := max (2 * max (9 * 10 ^ 8) (1000 / ε ^ 2)) k₁ with hK₀
  have hK₀0 : 18 * 10 ^ 8 ≤ K₀ :=
    le_trans (by linarith [le_max_left (9 * 10 ^ 8 : ℝ) (1000 / ε ^ 2)]) (le_max_left _ _)
  set Cf : ℝ := 2 * C + 2 + Real.exp (Real.sqrt K₀ / 6) with hCf
  refine ⟨Cf, by positivity, ?_⟩
  intro K hK1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  set E := Real.exp (-(Real.sqrt K / 6)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  by_cases hKsmall : (K : ℝ) < K₀
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT1
    have hvol : volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ≤
        ENNReal.ofReal T := by
      refine (measure_mono (fun t ht => ht.1)).trans ?_
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 1 ≤ Real.exp (Real.sqrt K₀ / 6) * E := by
      rw [hE, ← Real.exp_add]
      apply Real.one_le_exp
      have := Real.sqrt_le_sqrt hKsmall.le
      linarith
    have h2 : Real.exp (Real.sqrt K₀ / 6) ≤ Cf := by
      rw [hCf]; linarith
    have h3 : 1 ≤ Cf * E := h1.trans (mul_le_mul_of_nonneg_right h2 hE0.le)
    nlinarith
  push Not at hKsmall
  set κ₀ : ℝ := K / 2 with hκ₀
  have hκ₀1 : max (9 * 10 ^ 8) (1000 / ε ^ 2) ≤ κ₀ := by
    have := le_trans (le_max_left _ _) hKsmall
    rw [hκ₀]; linarith
  have hκ₀0 : 0 < κ₀ := by
    have := le_trans (le_max_left (9 * 10 ^ 8 : ℝ) (1000 / ε ^ 2)) hκ₀1; linarith
  have hk₁K : k₁ ≤ K := le_trans (le_max_right _ _) hKsmall
  have hη := eventually_volume_xiSliceCoeff_nonpos_le (η := 1 / 16) (δ := E / 2) (by norm_num)
    (by positivity)
  have hlog := eventually_mul_log_add_pow_le_exp 1 (4 * C / E) (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hev, hη, hlog, eventually_ge_atTop (Real.exp (10 ^ 7 + 1)),
    eventually_ge_atTop 64] with T hTev hTη hTlog hTe hT64
  have hT0 : 0 < T := by linarith
  have hL : 10 ^ 7 + 1 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) hTe; rwa [Real.log_exp] at this
  set S := (Finset.range (⌊Real.log T⌋₊ + 1)).filter
    (fun j => 2 ^ j * κ₀ / Real.log T ≤ 1 / 16) with hS
  have hsub0 : {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ⊆
      {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, ⌈max (2 * κ₀) k₁⌉₊ ≤ k ∧
        ¬ 0 < xiSliceCoeff t (2 * k)} := by
    rintro t ⟨ht, k, hk, hneg⟩
    refine ⟨ht, k, le_trans (Nat.ceil_le.mpr (max_le (by rw [hκ₀]; linarith) hk₁K)) hk, hneg⟩
  have hsub := hsub0.trans (bounded_order_subset hT64 hL (by linarith) hε hpos (κ₀ := κ₀))
  set A : ℝ := C * Real.exp (-(Real.sqrt κ₀ / 4)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hscale : ∀ j ∈ S, volume {t | t ∈ Icc T (2 * T) ∧
      ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} ≤
      ENNReal.ofReal (A * T * (1 / 2) ^ j / 1 + C * T ^ ((1 : ℝ) / 2)) := fun j hj =>
    volume_dyadic_scale_sqrt_le j (by linarith) hC hκ₀1 (Finset.mem_filter.mp hj).2 hTev
  have hsum := sum_scale_bounds_le (⌊Real.log T⌋₊ + 1) hA0 hC.le hT0.le
    (show (0 : ℝ) < 1 by norm_num) S (Finset.filter_subset _ _)
  have hfirst : 2 * A * T / 1 ≤ 2 * C * T * E := by
    rw [div_one, hA]
    have := exp_neg_sqrt_half_le hKpos.le
    rw [← hκ₀] at this
    have h := mul_le_mul_of_nonneg_left this (show 0 ≤ 2 * C * T by positivity)
    linarith
  have hsecond := count_term_le hC.le hE0 (by linarith) hTlog
  have hfin : 2 * C * T * E + E * T / 4 + E / 2 * T ≤ Cf * T * E := by
    have hTE : 0 ≤ T * E := by positivity
    have hle : 2 * C + 3 / 4 ≤ Cf := by
      rw [hCf]; have := Real.exp_pos (Real.sqrt K₀ / 6); linarith
    have e1 : 2 * C * T * E + E * T / 4 + E / 2 * T = (2 * C + 3 / 4) * (T * E) := by ring
    have e2 : Cf * T * E = Cf * (T * E) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hle hTE
  calc volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)}
      ≤ volume ((⋃ j ∈ S, {t | t ∈ Icc T (2 * T) ∧
          ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)}) ∪
          {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, 1 / 16 * Real.log t ≤ k ∧
            ¬ 0 < xiSliceCoeff t (2 * k)}) := measure_mono hsub
    _ ≤ volume (⋃ j ∈ S, {t | t ∈ Icc T (2 * T) ∧
          ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)}) +
          ENNReal.ofReal (E / 2 * T) := (measure_union_le _ _).trans (by gcongr)
    _ ≤ (∑ j ∈ S, volume {t | t ∈ Icc T (2 * T) ∧
          ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)}) +
          ENNReal.ofReal (E / 2 * T) := by gcongr; exact measure_biUnion_finset_le _ _
    _ ≤ (∑ j ∈ S, ENNReal.ofReal (A * T * (1 / 2) ^ j / 1 + C * T ^ ((1 : ℝ) / 2))) +
          ENNReal.ofReal (E / 2 * T) := by gcongr with j hj; exact hscale j hj
    _ = ENNReal.ofReal (∑ j ∈ S, (A * T * (1 / 2) ^ j / 1 + C * T ^ ((1 : ℝ) / 2))) +
          ENNReal.ofReal (E / 2 * T) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
    _ ≤ ENNReal.ofReal (2 * C * T * E + E * T / 4) + ENNReal.ofReal (E / 2 * T) := by
        gcongr
        linarith
    _ = ENNReal.ofReal (2 * C * T * E + E * T / 4 + E / 2 * T) := by
        have h1 : 0 ≤ 2 * C * T * E + E * T / 4 := by positivity
        have h2 : 0 ≤ E / 2 * T := by positivity
        exact (ENNReal.ofReal_add h1 h2).symm
    _ ≤ ENNReal.ofReal (Cf * T * E) := ENNReal.ofReal_le_ofReal hfin

end RHTower
