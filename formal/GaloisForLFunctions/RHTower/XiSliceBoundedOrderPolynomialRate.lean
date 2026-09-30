import GaloisForLFunctions.RHTower.XiSliceBoundedOrderDensity
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxHighMoments

/-!
# Bounded-order slice positivity at almost every height, with a polynomial rate

For `1 ≤ m ≤ 7500` there is `C` such that for every `K ≥ 1` and all large `T`, the heights
`t ∈ [T, 2T]` with `c_{2k}(t) ≤ 0` for some order `k ≥ K` have measure at most `C T/K^{2m}`
(`eventually_volume_xiSliceCoeff_nonpos_bounded_order_pow_le`).

The orders `K ≤ k < (log t)/16` are covered by the dyadic scales `R_j = 2^j κ₀/log T`, `κ₀ = K/2`
(`bounded_order_subset`). At scale `κ_j = 2^j κ₀` the heights without log-derivative scale data have
measure `≤ C T (e^{−κ_j/120000}/ε + m! (1280/(ε²κ_j²))^m) + C T^{1/2}`
(`exists_volume_not_zetaLogDerivScaleData_le_pow`), and with `e^{−u} ≤ (2m)!/u^{2m}` this is
`≤ A T 2^{−j}/κ₀^{2m} + C T^{1/2}` (`volume_dyadic_scale_pow_le`); the sum over `j` is
`≤ 2A T/κ₀^{2m} + O(T^{1/2} log T)`. The orders `k ≥ (log t)/16` are covered by
`eventually_volume_xiSliceCoeff_nonpos_le`.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped ComplexOrder

namespace RHTower

/-- `e^{−u} ≤ n!/uⁿ` for `u > 0`. -/
theorem exp_neg_le_factorial_div_pow_of_pos {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.exp (-u) ≤ n.factorial / u ^ n := by
  have h := Real.pow_div_factorial_le_exp u hu.le n
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  exact h

/-- The scale bound at the `m`-th moment in the form `≤ A_m T/κ^{2m}`. -/
theorem scale_bound_pow_le {C T ε κ : ℝ} {m : ℕ} (hC : 0 ≤ C) (hT : 0 ≤ T) (hε : 0 < ε)
    (hκ : 0 < κ) :
    C * T * (Real.exp (-(κ / 120000)) / ε + m.factorial * (1280 / (ε ^ 2 * κ ^ 2)) ^ m) ≤
      C * ((2 * m).factorial * 120000 ^ (2 * m) / ε + m.factorial * 1280 ^ m / ε ^ (2 * m)) * T /
        κ ^ (2 * m) := by
  have h1 := exp_neg_le_factorial_div_pow_of_pos (show 0 < κ / 120000 by positivity) (2 * m)
  have e1 : ((2 * m).factorial : ℝ) / (κ / 120000) ^ (2 * m) =
      (2 * m).factorial * 120000 ^ (2 * m) / κ ^ (2 * m) := by
    rw [div_pow]; field_simp
  have e2 : (1280 / (ε ^ 2 * κ ^ 2)) ^ m = 1280 ^ m / ε ^ (2 * m) / κ ^ (2 * m) := by
    rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 m]; field_simp
  rw [e1] at h1
  rw [e2]
  have h2 : Real.exp (-(κ / 120000)) / ε ≤
      (2 * m).factorial * 120000 ^ (2 * m) / κ ^ (2 * m) / ε :=
    div_le_div_of_nonneg_right h1 hε.le
  calc C * T * (Real.exp (-(κ / 120000)) / ε +
        m.factorial * (1280 ^ m / ε ^ (2 * m) / κ ^ (2 * m)))
      ≤ C * T * ((2 * m).factorial * 120000 ^ (2 * m) / κ ^ (2 * m) / ε +
          m.factorial * (1280 ^ m / ε ^ (2 * m) / κ ^ (2 * m))) := by gcongr
    _ = C * ((2 * m).factorial * 120000 ^ (2 * m) / ε + m.factorial * 1280 ^ m / ε ^ (2 * m)) *
          T / κ ^ (2 * m) := by ring

/-- The measure of the heights without data at the dyadic scale `2^j κ₀/log T`, at the `m`-th
moment. -/
theorem volume_dyadic_scale_pow_le {C T ε κ₀ : ℝ} {m : ℕ} (j : ℕ) (hT0 : 1 < T) (hC : 0 < C)
    (hε0 : 0 < ε) (hm1 : 1 ≤ m) (hκ₀ : 30000 ≤ κ₀) (hκ₀ε : 384 / ε ≤ κ₀)
    (hj16 : 2 ^ j * κ₀ / Real.log T ≤ 1 / 16)
    (hTev : ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → 30000 ≤ R * Real.log T → 384 / ε ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (ε * Real.log T)} ≤
        ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / ε +
          m.factorial * (1280 / (ε ^ 2 * (R * Real.log T) ^ 2)) ^ m) +
            C * T ^ ((1 : ℝ) / 2))) :
    volume {t | t ∈ Icc T (2 * T) ∧
        ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} ≤
      ENNReal.ofReal (C * ((2 * m).factorial * 120000 ^ (2 * m) / ε +
          m.factorial * 1280 ^ m / ε ^ (2 * m)) * T * (1 / 2) ^ j / κ₀ ^ (2 * m) +
        C * T ^ ((1 : ℝ) / 2)) := by
  have hL0 : 0 < Real.log T := Real.log_pos hT0
  have hRL : 2 ^ j * κ₀ / Real.log T * Real.log T = 2 ^ j * κ₀ := div_mul_cancel₀ _ hL0.ne'
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hκ₀0 : 0 < κ₀ := by linarith
  refine (hTev _ (by positivity) hj16 (by rw [hRL]; nlinarith) (by rw [hRL]; nlinarith)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [hRL]
  have h1 := scale_bound_pow_le (m := m) hC.le (by linarith : (0 : ℝ) ≤ T) hε0
    (show 0 < 2 ^ j * κ₀ by positivity)
  set A := C * ((2 * m).factorial * 120000 ^ (2 * m) / ε + m.factorial * 1280 ^ m / ε ^ (2 * m))
    with hA
  have hA0 : 0 ≤ A := by positivity
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ (j * (2 * m)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right j (by omega))
  have h2 : A * T / (2 ^ j * κ₀) ^ (2 * m) ≤ A * T * (1 / 2) ^ j / κ₀ ^ (2 * m) := by
    have e : A * T * (1 / 2) ^ j / κ₀ ^ (2 * m) = A * T / (2 ^ j * κ₀ ^ (2 * m)) := by
      rw [one_div_pow]; field_simp
    rw [e, mul_pow, ← pow_mul]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right hpow (by positivity))
  linarith

/-- **Slice positivity at bounded orders for almost every height, with a polynomial rate.** For
`1 ≤ m ≤ 7500` there is `C` such that for every `K ≥ 1` and all large `T`, the heights
`t ∈ [T, 2T]` with `c_{2k}(t) ≤ 0` for some `k ≥ K` have measure at most `C T/K^{2m}`. -/
theorem eventually_volume_xiSliceCoeff_nonpos_bounded_order_pow_le {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ 7500) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K → ∀ᶠ T in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ≤
        ENNReal.ofReal (C * T / (K : ℝ) ^ (2 * m)) := by
  obtain ⟨k₁, -, hpos⟩ := exists_xiSliceCoeff_pos_of_logDerivScaleData
  set ε : ℝ := 1 / 10 ^ 9 with hε
  have hε0 : 0 < ε := by norm_num
  obtain ⟨C, hC, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le_pow hε0 (by norm_num) hm1 hm
  set A : ℝ := C * ((2 * m).factorial * 120000 ^ (2 * m) / ε +
    m.factorial * 1280 ^ m / ε ^ (2 * m)) with hAdef
  have hA0 : 0 ≤ A := by positivity
  set K₀ : ℝ := max (2 * max 30000 (384 / ε)) k₁ with hK₀
  have hK₀60 : 60000 ≤ K₀ :=
    le_trans (by linarith [le_max_left (30000 : ℝ) (384 / ε)]) (le_max_left _ _)
  set Cf : ℝ := 2 ^ (2 * m + 2) * A + 2 + K₀ ^ (2 * m) with hCf
  have hCfK : K₀ ^ (2 * m) ≤ Cf := by
    have : 0 ≤ 2 ^ (2 * m + 2) * A := by positivity
    linarith
  refine ⟨Cf, by positivity, ?_⟩
  intro K hK1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKp : (0 : ℝ) < (K : ℝ) ^ (2 * m) := by positivity
  by_cases hKsmall : (K : ℝ) < K₀
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT1
    have hvol : volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ≤
        ENNReal.ofReal T := by
      refine (measure_mono (fun t ht => ht.1)).trans ?_
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [le_div_iff₀ hKp]
    have h1 : (K : ℝ) ^ (2 * m) ≤ K₀ ^ (2 * m) := pow_le_pow_left₀ hKpos.le hKsmall.le _
    have h2 : (K : ℝ) ^ (2 * m) ≤ Cf := h1.trans hCfK
    nlinarith
  push Not at hKsmall
  set κ₀ : ℝ := K / 2 with hκ₀
  have hκ₀1 : 30000 ≤ κ₀ := by
    have := le_trans (le_max_left _ _) hKsmall
    rw [hκ₀]; linarith [le_max_left (30000 : ℝ) (384 / ε)]
  have hκ₀ε : 384 / ε ≤ κ₀ := by
    have := le_trans (le_max_left _ _) hKsmall
    rw [hκ₀]; linarith [le_max_right (30000 : ℝ) (384 / ε)]
  have hκ₀0 : 0 < κ₀ := by linarith
  have hk₁K : k₁ ≤ K := le_trans (le_max_right _ _) hKsmall
  set δ : ℝ := 1 / (K : ℝ) ^ (2 * m) with hδ
  have hδ0 : 0 < δ := by positivity
  have hη := eventually_volume_xiSliceCoeff_nonpos_le (η := 1 / 16) (δ := δ / 2) (by norm_num)
    (by linarith)
  have hlog := eventually_mul_log_add_pow_le_exp 1 (4 * C / δ) (show (0 : ℝ) < 1 / 2 by norm_num)
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
  have hscale : ∀ j ∈ S, volume {t | t ∈ Icc T (2 * T) ∧
      ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} ≤
      ENNReal.ofReal (A * T * (1 / 2) ^ j / κ₀ ^ (2 * m) + C * T ^ ((1 : ℝ) / 2)) := fun j hj =>
    volume_dyadic_scale_pow_le j (by linarith) hC hε0 hm1 hκ₀1 hκ₀ε (Finset.mem_filter.mp hj).2 hTev
  have hsum := sum_scale_bounds_le (⌊Real.log T⌋₊ + 1) hA0 hC.le hT0.le
    (show 0 < κ₀ ^ (2 * m) by positivity) S (Finset.filter_subset _ _)
  have hfirst : 2 * A * T / κ₀ ^ (2 * m) = 2 ^ (2 * m + 1) * A * T / (K : ℝ) ^ (2 * m) := by
    rw [hκ₀, div_pow]; field_simp; ring
  have hsecond := count_term_le hC.le hδ0 (by linarith) hTlog
  have hδT : δ * T = T / (K : ℝ) ^ (2 * m) := by rw [hδ]; field_simp
  have hfin : 2 ^ (2 * m + 1) * A * T / (K : ℝ) ^ (2 * m) + δ * T / 4 + δ / 2 * T ≤
      Cf * T / (K : ℝ) ^ (2 * m) := by
    have e1 : δ * T / 4 + δ / 2 * T = 3 / 4 * (T / (K : ℝ) ^ (2 * m)) := by rw [← hδT]; ring
    have e2 : Cf * T / (K : ℝ) ^ (2 * m) = Cf * (T / (K : ℝ) ^ (2 * m)) := by ring
    have e3 : 2 ^ (2 * m + 1) * A * T / (K : ℝ) ^ (2 * m) =
        2 ^ (2 * m + 1) * A * (T / (K : ℝ) ^ (2 * m)) := by ring
    rw [add_assoc, e1, e2, e3]
    have hX : 0 ≤ T / (K : ℝ) ^ (2 * m) := by positivity
    have hle : 2 ^ (2 * m + 1) * A + 3 / 4 ≤ Cf := by
      have h4 : (2 : ℝ) ^ (2 * m + 2) = 2 * 2 ^ (2 * m + 1) := by rw [pow_succ]; ring
      have h5 : 0 ≤ K₀ ^ (2 * m) := by positivity
      have h6 : 0 ≤ 2 ^ (2 * m + 1) * A := by positivity
      rw [hCf, h4]
      linarith
    nlinarith
  calc volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)}
      ≤ volume ((⋃ j ∈ S, {t | t ∈ Icc T (2 * T) ∧
          ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)}) ∪
          {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, 1 / 16 * Real.log t ≤ k ∧
            ¬ 0 < xiSliceCoeff t (2 * k)}) := measure_mono hsub
    _ ≤ volume (⋃ j ∈ S, {t | t ∈ Icc T (2 * T) ∧
          ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)}) +
          ENNReal.ofReal (δ / 2 * T) := (measure_union_le _ _).trans (by gcongr)
    _ ≤ (∑ j ∈ S, volume {t | t ∈ Icc T (2 * T) ∧
          ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)}) +
          ENNReal.ofReal (δ / 2 * T) := by gcongr; exact measure_biUnion_finset_le _ _
    _ ≤ (∑ j ∈ S, ENNReal.ofReal (A * T * (1 / 2) ^ j / κ₀ ^ (2 * m) + C * T ^ ((1 : ℝ) / 2))) +
          ENNReal.ofReal (δ / 2 * T) := by gcongr with j hj; exact hscale j hj
    _ = ENNReal.ofReal (∑ j ∈ S, (A * T * (1 / 2) ^ j / κ₀ ^ (2 * m) +
          C * T ^ ((1 : ℝ) / 2))) + ENNReal.ofReal (δ / 2 * T) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
    _ ≤ ENNReal.ofReal (2 ^ (2 * m + 1) * A * T / (K : ℝ) ^ (2 * m) + δ * T / 4) +
          ENNReal.ofReal (δ / 2 * T) := by
        gcongr
        rw [← hfirst]
        linarith
    _ = ENNReal.ofReal (2 ^ (2 * m + 1) * A * T / (K : ℝ) ^ (2 * m) + δ * T / 4 + δ / 2 * T) := by
        have h1 : 0 ≤ 2 ^ (2 * m + 1) * A * T / (K : ℝ) ^ (2 * m) + δ * T / 4 := by positivity
        have h2 : 0 ≤ δ / 2 * T := by positivity
        exact (ENNReal.ofReal_add h1 h2).symm
    _ ≤ ENNReal.ofReal (Cf * T / (K : ℝ) ^ (2 * m)) := ENNReal.ofReal_le_ofReal hfin

end RHTower
