import GaloisForLFunctions.RHTower.XiSliceBoundedOrderStretchedRate
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxPrimeCascade

/-!
# Bounded-order slice positivity at almost every height, with an exponential rate

There are `C, c > 0` such that for every `K ≥ 1` and all large `T`, the heights `t ∈ [T, 2T]` with
`c_{2k}(t) ≤ 0` for some order `k ≥ K` have measure at most `C T e^{−cK}`
(`eventually_volume_xiSliceCoeff_nonpos_bounded_order_exp_le`); one may take `c = 1/(6·10¹⁰)`.

At the scale `κ = R log T` the heights without log-derivative scale data have measure
`≤ C T (e^{−κ/120000}/ε + κ² e^{−κ/16} + e^{−κε/15}) + C T^{1/2}`
(`exists_volume_not_zetaLogDerivScaleData_le_exp`, through the cascade of prime ranges), which is
`≤ C' T e^{−κε/30} + C T^{1/2}` (`scale_bound_exp_le`). The dyadic scales `κ_j = 2^j κ₀`,
`κ₀ = K/2`, then cost `C' T e^{−κ₀ε/30} 2^{−j}` each once `κ₀ε/30 ≥ 1` (`exp_neg_two_pow_mul_le`).
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped ComplexOrder

namespace RHTower

/-- `x² e^{−x/32} ≤ 2048` for `x ≥ 0`. -/
theorem sq_mul_exp_neg_div_le {x : ℝ} (hx : 0 ≤ x) : x ^ 2 * Real.exp (-(x / 32)) ≤ 2048 := by
  have h := Real.pow_div_factorial_le_exp (x / 32) (by positivity) 2
  norm_num [Nat.factorial] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  nlinarith

/-- The scale bound in the form `≤ C(1/ε + 2049) T e^{−κε/30}`. -/
theorem scale_bound_exp_le {C T ε κ : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) (hε : 0 < ε)
    (hε4 : ε ≤ 1 / 4000) (hκ : 0 ≤ κ) :
    C * T * (Real.exp (-(κ / 120000)) / ε + (κ ^ 2 * Real.exp (-(κ / 16)) +
      Real.exp (-(κ * ε / 15)))) ≤ C * (1 / ε + 2049) * T * Real.exp (-(κ * ε / 30)) := by
  set E := Real.exp (-(κ * ε / 30)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have h1 : Real.exp (-(κ / 120000)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have : κ * ε / 30 ≤ κ / 120000 := by
      have := mul_le_mul_of_nonneg_left hε4 hκ
      linarith
    linarith
  have h2 : κ ^ 2 * Real.exp (-(κ / 16)) ≤ 2048 * E := by
    have hsplit : Real.exp (-(κ / 16)) = Real.exp (-(κ / 32)) * Real.exp (-(κ / 32)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-(κ / 32)) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr
      have : κ * ε / 30 ≤ κ / 32 := by
        have := mul_le_mul_of_nonneg_left hε4 hκ
        nlinarith
      linarith
    rw [hsplit, ← mul_assoc]
    have h4 := sq_mul_exp_neg_div_le hκ
    have := mul_le_mul h4 h3 (Real.exp_pos _).le (by norm_num)
    linarith
  have h3 : Real.exp (-(κ * ε / 15)) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have : 0 ≤ κ * ε := by positivity
    linarith
  have hsum : Real.exp (-(κ / 120000)) / ε + (κ ^ 2 * Real.exp (-(κ / 16)) +
      Real.exp (-(κ * ε / 15))) ≤ (1 / ε + 2049) * E := by
    have h1' : Real.exp (-(κ / 120000)) / ε ≤ E / ε := div_le_div_of_nonneg_right h1 hε.le
    have e : (1 / ε + 2049) * E = E / ε + 2048 * E + E := by ring
    rw [e]
    linarith
  calc C * T * (Real.exp (-(κ / 120000)) / ε + (κ ^ 2 * Real.exp (-(κ / 16)) +
        Real.exp (-(κ * ε / 15))))
      ≤ C * T * ((1 / ε + 2049) * E) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * (1 / ε + 2049) * T * E := by ring

/-- `e^{−c 2^j κ₀} ≤ e^{−cκ₀} 2^{−j}` for `cκ₀ ≥ 1`. -/
theorem exp_neg_two_pow_mul_le {c κ₀ : ℝ} (hcκ : 1 ≤ c * κ₀) (j : ℕ) :
    Real.exp (-(2 ^ j * κ₀ * c)) ≤ Real.exp (-(κ₀ * c)) * (1 / 2) ^ j := by
  have hj : (1 : ℝ) + j ≤ 2 ^ j := by
    have := one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num) j
    norm_num at this; linarith
  have hhalf : ((1 : ℝ) / 2) ^ j = Real.exp (-(j * Real.log 2)) := by
    have h2 : Real.exp (j * Real.log 2) = 2 ^ j := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [Real.exp_neg, h2, one_div_pow, one_div]
  rw [hhalf, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_two_lt_d9
  norm_num at hlog
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hκ0 : 0 ≤ κ₀ * c := by linarith
  have h1 : (1 + j) * (κ₀ * c) ≤ 2 ^ j * κ₀ * c := by
    have := mul_le_mul_of_nonneg_right hj hκ0; linarith
  nlinarith

/-- The measure of the heights without data at the dyadic scale `2^j κ₀/log T`, at the
exponential rate. -/
theorem volume_dyadic_scale_exp_le {C T ε κ₀ κ₁ : ℝ} (j : ℕ) (hT0 : 1 < T) (hC : 0 < C)
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4000) (hκ₀ : κ₁ ≤ κ₀) (hκε : 1 ≤ ε / 30 * κ₀)
    (hj16 : 2 ^ j * κ₀ / Real.log T ≤ 1 / 16)
    (hTev : ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → κ₁ ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (ε * Real.log T)} ≤
        ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / ε +
          ((R * Real.log T) ^ 2 * Real.exp (-(R * Real.log T / 16)) +
            Real.exp (-(R * Real.log T * ε / 15)))) + C * T ^ ((1 : ℝ) / 2))) :
    volume {t | t ∈ Icc T (2 * T) ∧
        ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} ≤
      ENNReal.ofReal (C * (1 / ε + 2049) * Real.exp (-(κ₀ * (ε / 30))) * T * (1 / 2) ^ j / 1 +
        C * T ^ ((1 : ℝ) / 2)) := by
  have hL0 : 0 < Real.log T := Real.log_pos hT0
  have hRL : 2 ^ j * κ₀ / Real.log T * Real.log T = 2 ^ j * κ₀ := div_mul_cancel₀ _ hL0.ne'
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hκ₀0 : 0 < κ₀ := by
    have : 0 < ε / 30 := by positivity
    by_contra h; push Not at h; nlinarith
  refine (hTev _ (by positivity) hj16 (by rw [hRL]; exact hκ₀.trans (le_mul_of_one_le_left
    hκ₀0.le h2j))).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hRL]
  have h1 := scale_bound_exp_le hC.le (by linarith : (0 : ℝ) ≤ T) hε hε4
    (show 0 ≤ 2 ^ j * κ₀ by positivity)
  have h2 := exp_neg_two_pow_mul_le (c := ε / 30) (κ₀ := κ₀) (by linarith) j
  have e1 : Real.exp (-(2 ^ j * κ₀ * ε / 30)) = Real.exp (-(2 ^ j * κ₀ * (ε / 30))) := by
    congr 1; ring
  rw [e1] at h1
  have hK : 0 ≤ C * (1 / ε + 2049) * T := by
    have : (0 : ℝ) ≤ T := by linarith
    positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hK
  have e2 : C * (1 / ε + 2049) * T * (Real.exp (-(κ₀ * (ε / 30))) * (1 / 2) ^ j) =
      C * (1 / ε + 2049) * Real.exp (-(κ₀ * (ε / 30))) * T * (1 / 2) ^ j / 1 := by ring
  linarith

/-- **Slice positivity at bounded orders for almost every height, with an exponential rate.**
There are `C, c > 0` such that for every `K ≥ 1` and all large `T`, the heights `t ∈ [T, 2T]` with
`c_{2k}(t) ≤ 0` for some `k ≥ K` have measure at most `C T e^{−cK}`. -/
theorem eventually_volume_xiSliceCoeff_nonpos_bounded_order_exp_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ K : ℕ, 1 ≤ K → ∀ᶠ T in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ≤
        ENNReal.ofReal (C * T * Real.exp (-(c * K))) := by
  obtain ⟨k₁, -, hpos⟩ := exists_xiSliceCoeff_pos_of_logDerivScaleData
  set ε : ℝ := 1 / 10 ^ 9 with hε
  have hε0 : 0 < ε := by norm_num
  have hε4 : ε ≤ 1 / 4000 := by norm_num
  obtain ⟨C, κ₁, hC, hκ₁, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le_exp hε0 (by norm_num)
  set c : ℝ := ε / 60 with hc
  have hc0 : 0 < c := by positivity
  set K₀ : ℝ := max (2 * max κ₁ (60 / ε)) k₁ with hK₀
  have hK₀2 : 2 * max κ₁ (60 / ε) ≤ K₀ := le_max_left _ _
  set A0 : ℝ := C * (1 / ε + 2049) with hA0
  have hA00 : 0 ≤ A0 := by positivity
  set Cf : ℝ := 2 * A0 + 2 + Real.exp (c * K₀) with hCf
  refine ⟨Cf, c, by positivity, hc0, ?_⟩
  intro K hK1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  set E := Real.exp (-(c * K)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  by_cases hKsmall : (K : ℝ) < K₀
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT1
    have hvol : volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ≤
        ENNReal.ofReal T := by
      refine (measure_mono (fun t ht => ht.1)).trans ?_
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 1 ≤ Real.exp (c * K₀) * E := by
      rw [hE, ← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hKsmall.le hc0.le
      linarith
    have h2 : Real.exp (c * K₀) ≤ Cf := by rw [hCf]; linarith
    have h3 : 1 ≤ Cf * E := h1.trans (mul_le_mul_of_nonneg_right h2 hE0.le)
    nlinarith
  push Not at hKsmall
  set κ₀ : ℝ := K / 2 with hκ₀
  have hκ₀1 : κ₁ ≤ κ₀ := by
    have := le_trans hK₀2 hKsmall
    rw [hκ₀]; linarith [le_max_left κ₁ (60 / ε)]
  have hκ₀ε : 1 ≤ ε / 30 * κ₀ := by
    have h1 := le_trans hK₀2 hKsmall
    have h2 : 60 / ε ≤ K / 2 := by linarith [le_max_right κ₁ (60 / ε)]
    rw [hκ₀]
    have := (div_le_iff₀ hε0).mp h2
    nlinarith
  have hκ₀0 : 0 < κ₀ := by positivity
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
  have hκ₀1' : 1 ≤ κ₀ := by
    have h1 : 1 ≤ ε / 30 * κ₀ := hκ₀ε
    have h2 : ε / 30 ≤ 1 := by norm_num
    nlinarith
  have hsub := hsub0.trans (bounded_order_subset hT64 hL hκ₀1' hε hpos (κ₀ := κ₀))
  set A : ℝ := A0 * Real.exp (-(κ₀ * (ε / 30))) with hA
  have hA0' : 0 ≤ A := by positivity
  have hscale : ∀ j ∈ S, volume {t | t ∈ Icc T (2 * T) ∧
      ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} ≤
      ENNReal.ofReal (A * T * (1 / 2) ^ j / 1 + C * T ^ ((1 : ℝ) / 2)) := fun j hj => by
    have := volume_dyadic_scale_exp_le j (by linarith) hC hε0 hε4 hκ₀1 hκ₀ε
      (Finset.mem_filter.mp hj).2 hTev
    rw [hA, hA0]
    exact this
  have hsum := sum_scale_bounds_le (⌊Real.log T⌋₊ + 1) hA0' hC.le hT0.le
    (show (0 : ℝ) < 1 by norm_num) S (Finset.filter_subset _ _)
  have hfirst : 2 * A * T / 1 ≤ 2 * A0 * T * E := by
    rw [div_one, hA]
    have h1 : Real.exp (-(κ₀ * (ε / 30))) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr
      rw [hκ₀, hc]
      have : ε / 60 * K = K / 2 * (ε / 30) := by ring
      linarith
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * A0 * T by positivity)
    linarith
  have hsecond := count_term_le hC.le hE0 (by linarith) hTlog
  have hfin : 2 * A0 * T * E + E * T / 4 + E / 2 * T ≤ Cf * T * E := by
    have hTE : 0 ≤ T * E := by positivity
    have hle : 2 * A0 + 3 / 4 ≤ Cf := by
      have h2 : 2 * A0 + 2 ≤ Cf := by
        rw [hCf]; exact le_add_of_nonneg_right (Real.exp_pos _).le
      linarith
    have e1 : 2 * A0 * T * E + E * T / 4 + E / 2 * T = (2 * A0 + 3 / 4) * (T * E) := by ring
    have e2 : Cf * T * E = Cf * (T * E) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hle hTE
  have hfin' : Cf * T * E = Cf * T * Real.exp (-(c * K)) := by rw [hE]
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
    _ ≤ ENNReal.ofReal (2 * A0 * T * E + E * T / 4) + ENNReal.ofReal (E / 2 * T) := by
        gcongr
        linarith
    _ = ENNReal.ofReal (2 * A0 * T * E + E * T / 4 + E / 2 * T) := by
        have h1 : 0 ≤ 2 * A0 * T * E + E * T / 4 := by positivity
        have h2 : 0 ≤ E / 2 * T := by positivity
        exact (ENNReal.ofReal_add h1 h2).symm
    _ ≤ ENNReal.ofReal (Cf * T * Real.exp (-(c * K))) := by
        rw [← hfin']; exact ENNReal.ofReal_le_ofReal hfin

end RHTower
