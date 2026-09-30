import GaloisForLFunctions.RHTower.XiSliceLogDerivScalePositivity
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxDensity

/-!
# Slice positivity at all orders above a bounded threshold, for almost every height

For every `δ > 0` there is `K` such that for all large `T`, the heights `t ∈ [T, 2T]` at which
`c_{2k}(t) ≤ 0` for some order `k ≥ K` have measure at most `δT`
(`eventually_volume_xiSliceCoeff_nonpos_bounded_order_le`).

The orders `K ≤ k < (log t)/16` are covered by the dyadic scales `R_j = 2^j κ₀/log T`: the order `k`
lies in `[R_j log t, 2R_j log t]` for one `j`, and at a height with log-derivative scale data at
`R_j` and level `10⁻⁹ log T` the saddle gives `c_{2k}(t) > 0`
(`exists_xiSliceCoeff_pos_of_logDerivScaleData`). The heights without such data at `R_j` have measure
`≤ C T (e^{−κ_j/120000}/ε + 1/(ε²κ_j²)) + C T^{1/2}` with `κ_j = 2^j κ₀`
(`exists_volume_not_zetaLogDerivScaleData_le`), which sums over `j` to `≤ 2CT(120000/ε + 1/ε²)/κ₀`
plus `O(T^{1/2} log T)`. The orders `k ≥ (log t)/16` are covered by
`eventually_volume_xiSliceCoeff_nonpos_le`.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped ComplexOrder

namespace RHTower

/-- **Dyadic position of an order.** For `0 < a ≤ k` there is `j` with `2^j a ≤ k ≤ 2^{j+1} a`. -/
theorem exists_dyadic_scale {a k : ℝ} (ha : 0 < a) (hk : a ≤ k) :
    ∃ j : ℕ, 2 ^ j * a ≤ k ∧ k ≤ 2 ^ (j + 1) * a := by
  classical
  have hex : ∃ j : ℕ, k < 2 ^ (j + 1) * a := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (k / a) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ ha] at hn
    have : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  refine ⟨Nat.find hex, ?_, (Nat.find_spec hex).le⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simpa using hk
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hmin
    exact not_lt.mp hmin

/-- The scale bound in the form `≤ C T (120000/ε + 1/ε²)/κ + C T^{1/2}`. -/
theorem scale_bound_le {C T ε κ : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) (hε : 0 < ε) (hκ : 1 ≤ κ) :
    C * T * (Real.exp (-(κ / 120000)) / ε + 1 / (ε ^ 2 * κ ^ 2)) ≤
      C * T * (120000 / ε + 1 / ε ^ 2) * (1 / κ) := by
  have hκ0 : 0 < κ := by linarith
  have h1 : Real.exp (-(κ / 120000)) ≤ 120000 / κ := by
    have hx : 0 < κ / 120000 := by positivity
    have := inv_anti₀ hx (by linarith [Real.add_one_le_exp (κ / 120000)] :
      κ / 120000 ≤ Real.exp (κ / 120000))
    rwa [← Real.exp_neg, inv_div] at this
  have h2 : 1 / (ε ^ 2 * κ ^ 2) ≤ 1 / ε ^ 2 * (1 / κ) := by
    rw [div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    have : κ ≤ κ ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h3 : Real.exp (-(κ / 120000)) / ε ≤ 120000 / ε * (1 / κ) := by
    rw [div_mul_div_comm, mul_one, mul_comm ε κ, ← div_div]
    exact div_le_div_of_nonneg_right h1 hε.le
  have := add_le_add h3 h2
  calc C * T * (Real.exp (-(κ / 120000)) / ε + 1 / (ε ^ 2 * κ ^ 2))
      ≤ C * T * (120000 / ε * (1 / κ) + 1 / ε ^ 2 * (1 / κ)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = C * T * (120000 / ε + 1 / ε ^ 2) * (1 / κ) := by ring

/-- The sum of the scale bounds over the dyadic scales. -/
theorem sum_scale_bounds_le {A C T κ₀ : ℝ} (N : ℕ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hκ₀ : 0 < κ₀) (S : Finset ℕ) (hS : S ⊆ Finset.range N) :
    ∑ j ∈ S, (A * T * (1 / 2) ^ j / κ₀ + C * T ^ ((1 : ℝ) / 2)) ≤
      2 * A * T / κ₀ + N * (C * T ^ ((1 : ℝ) / 2)) := by
  have hnn : ∀ j, 0 ≤ A * T * (1 / 2 : ℝ) ^ j / κ₀ + C * T ^ ((1 : ℝ) / 2) := fun j => by positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg hS fun j _ _ => hnn j).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgeo := sum_geometric_two_le N
  have e : ∑ j ∈ Finset.range N, A * T * (1 / 2 : ℝ) ^ j / κ₀ =
      A * T / κ₀ * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [e]
  have h1 : A * T / κ₀ * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j ≤ A * T / κ₀ * 2 :=
    mul_le_mul_of_nonneg_left hgeo (by positivity)
  have e2 : 2 * A * T / κ₀ = A * T / κ₀ * 2 := by ring
  rw [e2]
  linarith

/-- **Covering of the bounded orders by dyadic scales.** -/
theorem bounded_order_subset {T κ₀ k₁ ε : ℝ} (hT64 : 64 ≤ T) (hL : 10 ^ 7 + 1 ≤ Real.log T)
    (hκ₀ : 1 ≤ κ₀) (hε : ε = 1 / 10 ^ 9)
    (hpos : ∀ t R B : ℝ, ∀ k : ℕ, ZetaLogDerivScaleData t R B → 0 < R →
      R ≤ 1 / 16 → 64 ≤ t → 10 ^ 7 ≤ Real.log t → 0 ≤ B → B ≤ Real.log t / 10 ^ 9 →
      R * Real.log t ≤ k → (k : ℝ) ≤ 2 * R * Real.log t → k₁ ≤ k →
      0 < xiSliceCoeff t (2 * k)) :
    {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, ⌈max (2 * κ₀) k₁⌉₊ ≤ k ∧
      ¬ 0 < xiSliceCoeff t (2 * k)} ⊆
      (⋃ j ∈ (Finset.range (⌊Real.log T⌋₊ + 1)).filter
          (fun j => 2 ^ j * κ₀ / Real.log T ≤ 1 / 16),
        {t | t ∈ Icc T (2 * T) ∧
          ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)}) ∪
      {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, 1 / 16 * Real.log t ≤ k ∧
        ¬ 0 < xiSliceCoeff t (2 * k)} := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL0 : 0 < L := by linarith
  have hκ₀0 : 0 < κ₀ := by linarith
  rintro t ⟨ht, k, hkK, hk⟩
  by_cases hkη : 1 / 16 * Real.log t ≤ k
  · exact Or.inr ⟨ht, k, hkη, hk⟩
  left
  push Not at hkη
  have ht0 : 0 < t := by linarith [ht.1]
  have hLt : L ≤ Real.log t := Real.log_le_log hT0 ht.1
  have hLt2 : Real.log t ≤ 2 * L := by
    have h1 : Real.log t ≤ Real.log (2 * T) := Real.log_le_log ht0 ht.2
    rw [Real.log_mul (by norm_num) hT0.ne'] at h1
    have := Real.log_two_lt_d9
    linarith
  have hlt0 : 0 < Real.log t := by linarith
  have hkK' : max (2 * κ₀) k₁ ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast hkK)
  have hk2κ : 2 * κ₀ ≤ k := le_trans (le_max_left _ _) hkK'
  have hkk₁ : k₁ ≤ k := le_trans (le_max_right _ _) hkK'
  set a : ℝ := κ₀ * Real.log t / L with ha
  have ha0 : 0 < a := by positivity
  have ha2 : a ≤ 2 * κ₀ := by
    rw [ha, div_le_iff₀ hL0]; nlinarith
  obtain ⟨j, hj1, hj2⟩ := exists_dyadic_scale (k := (k : ℝ)) ha0 (by linarith)
  set Rj : ℝ := 2 ^ j * κ₀ / L with hRj
  have hRjlog : Rj * Real.log t = 2 ^ j * a := by rw [hRj, ha]; field_simp
  have hRj0 : 0 < Rj := by positivity
  have hRj16 : Rj ≤ 1 / 16 := by
    have : Rj * Real.log t < 1 / 16 * Real.log t := by rw [hRjlog]; linarith
    exact (lt_of_mul_lt_mul_right this hlt0.le).le
  have hjN : j < ⌊L⌋₊ + 1 := by
    have h2j : (2 : ℝ) ^ j * κ₀ ≤ L / 16 := by
      have : Rj ≤ 1 / 16 := hRj16
      rw [hRj, div_le_iff₀ hL0] at this
      linarith
    have hjpow : (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ j ≤ L := by
      have hκ1 : (2 : ℝ) ^ j * 1 ≤ 2 ^ j * κ₀ := mul_le_mul_of_nonneg_left hκ₀ (by positivity)
      linarith
    have hjL : (j : ℝ) < L := lt_of_lt_of_le hjpow h2
    have : j ≤ ⌊L⌋₊ := Nat.le_floor hjL.le
    omega
  refine mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hRj16⟩,
    ht, fun hdata => hk ?_⟩
  refine hpos t Rj (ε * L) k hdata hRj0 hRj16 (by linarith [ht.1]) (by linarith)
    (by rw [hε]; positivity) ?_ ?_ ?_ hkk₁
  · rw [hε]
    have := div_le_div_of_nonneg_right hLt (show (0 : ℝ) ≤ 10 ^ 9 by norm_num)
    linarith [show 1 / 10 ^ 9 * L = L / 10 ^ 9 by ring]
  · rw [hRjlog]; exact hj1
  · rw [mul_assoc, hRjlog]; rw [pow_succ] at hj2; linarith

/-- The measure of the heights without data at the dyadic scale `2^j κ₀/log T`. -/
theorem volume_dyadic_scale_le {C T ε κ₀ : ℝ} (j : ℕ) (hT0 : 1 < T) (hC : 0 < C) (hε0 : 0 < ε)
    (hκ₀ : 30000 ≤ κ₀) (hj16 : 2 ^ j * κ₀ / Real.log T ≤ 1 / 16)
    (hTev : ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → 30000 ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (ε * Real.log T)} ≤
        ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / ε +
          1 / (ε ^ 2 * (R * Real.log T) ^ 2)) + C * T ^ ((1 : ℝ) / 2))) :
    volume {t | t ∈ Icc T (2 * T) ∧
        ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} ≤
      ENNReal.ofReal (C * (120000 / ε + 1 / ε ^ 2) * T * (1 / 2) ^ j / κ₀ +
        C * T ^ ((1 : ℝ) / 2)) := by
  have hL0 : 0 < Real.log T := Real.log_pos hT0
  have hRL : 2 ^ j * κ₀ / Real.log T * Real.log T = 2 ^ j * κ₀ := div_mul_cancel₀ _ hL0.ne'
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hκj : 30000 ≤ 2 ^ j * κ₀ / Real.log T * Real.log T := by rw [hRL]; nlinarith
  refine (hTev _ (by positivity) hj16 hκj).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hRL]
  have h1 := scale_bound_le hC.le (by linarith : (0 : ℝ) ≤ T) hε0
    (show 1 ≤ 2 ^ j * κ₀ by nlinarith)
  have e : C * T * (120000 / ε + 1 / ε ^ 2) * (1 / (2 ^ j * κ₀)) =
      C * (120000 / ε + 1 / ε ^ 2) * T * (1 / 2) ^ j / κ₀ := by
    rw [one_div_pow]
    have : (2 : ℝ) ^ j ≠ 0 := by positivity
    have : κ₀ ≠ 0 := by linarith
    field_simp
  rw [e] at h1
  linarith

/-- The number of scales times `C T^{1/2}` is at most `δT/4`. -/
theorem count_term_le {C δ T : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hT : 1 < T)
    (hTlog : 4 * C / δ * (Real.log T + 3) ^ 1 ≤ Real.exp (1 / 2 * Real.log T)) :
    ((⌊Real.log T⌋₊ + 1 : ℕ) : ℝ) * (C * T ^ ((1 : ℝ) / 2)) ≤ δ * T / 4 := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL0 : 0 < L := Real.log_pos hT
  have hNL : ((⌊L⌋₊ + 1 : ℕ) : ℝ) ≤ L + 3 := by
    push_cast; linarith [Nat.floor_le hL0.le]
  have hTs : T ^ ((1 : ℝ) / 2) = Real.exp (1 / 2 * L) := by
    rw [Real.rpow_def_of_pos hT0]; congr 1; ring
  have hTT : T = Real.exp (1 / 2 * L) * Real.exp (1 / 2 * L) := by
    rw [← Real.exp_add, show 1 / 2 * L + 1 / 2 * L = L by ring, hLdef, Real.exp_log hT0]
  rw [pow_one] at hTlog
  have hs0 : 0 ≤ Real.exp (1 / 2 * L) := (Real.exp_pos _).le
  have h1 : ((⌊L⌋₊ + 1 : ℕ) : ℝ) * (C * T ^ ((1 : ℝ) / 2)) ≤
      (L + 3) * C * Real.exp (1 / 2 * L) := by
    rw [hTs]
    have := mul_le_mul_of_nonneg_right hNL (mul_nonneg hC hs0)
    linarith
  have h2 : (L + 3) * C ≤ δ / 4 * Real.exp (1 / 2 * L) := by
    have e : 4 * C / δ * (L + 3) = (L + 3) * C / (δ / 4) := by field_simp
    rw [e, div_le_iff₀ (by positivity)] at hTlog
    linarith
  calc ((⌊L⌋₊ + 1 : ℕ) : ℝ) * (C * T ^ ((1 : ℝ) / 2)) ≤ (L + 3) * C * Real.exp (1 / 2 * L) := h1
    _ ≤ δ / 4 * Real.exp (1 / 2 * L) * Real.exp (1 / 2 * L) :=
        mul_le_mul_of_nonneg_right h2 hs0
    _ = δ * T / 4 := by rw [hTT]; ring

/-- **Slice positivity at bounded orders for almost every height.** For every `δ > 0` there is
`K` such that for all large `T`, the heights `t ∈ [T, 2T]` with `c_{2k}(t) ≤ 0` for some `k ≥ K`
have measure at most `δT`. -/
theorem eventually_volume_xiSliceCoeff_nonpos_bounded_order_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ᶠ T in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, K ≤ k ∧ ¬ 0 < xiSliceCoeff t (2 * k)} ≤
        ENNReal.ofReal (δ * T) := by
  obtain ⟨k₁, -, hpos⟩ := exists_xiSliceCoeff_pos_of_logDerivScaleData
  set ε : ℝ := 1 / 10 ^ 9 with hε
  have hε0 : 0 < ε := by norm_num
  obtain ⟨C, hC, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le (ε := ε) hε0 (by norm_num)
  set A : ℝ := C * (120000 / ε + 1 / ε ^ 2) with hAdef
  have hA0 : 0 ≤ A := by positivity
  set κ₀ : ℝ := max 30000 (8 * A / δ) with hκ₀
  have hκ₀1 : 30000 ≤ κ₀ := le_max_left _ _
  have hκ₀A : 8 * A / δ ≤ κ₀ := le_max_right _ _
  have hκ₀0 : 0 < κ₀ := by linarith
  refine ⟨⌈max (2 * κ₀) k₁⌉₊, ?_⟩
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
  have hsub := bounded_order_subset hT64 hL (by linarith) hε hpos (κ₀ := κ₀)
  have hscale : ∀ j ∈ S, volume {t | t ∈ Icc T (2 * T) ∧
      ¬ ZetaLogDerivScaleData t (2 ^ j * κ₀ / Real.log T) (ε * Real.log T)} ≤
      ENNReal.ofReal (A * T * (1 / 2) ^ j / κ₀ + C * T ^ ((1 : ℝ) / 2)) := fun j hj =>
    volume_dyadic_scale_le j (by linarith) hC hε0 hκ₀1 (Finset.mem_filter.mp hj).2 hTev
  have hsum := sum_scale_bounds_le (⌊Real.log T⌋₊ + 1) hA0 hC.le hT0.le hκ₀0 S
    (Finset.filter_subset _ _)
  have hfirst : 2 * A * T / κ₀ ≤ δ * T / 4 := by
    rw [div_le_iff₀ hκ₀0]
    have := mul_le_mul_of_nonneg_left hκ₀A (show 0 ≤ δ * T / 4 by positivity)
    have e : δ * T / 4 * (8 * A / δ) = 2 * A * T := by field_simp; ring
    linarith
  have hsecond := count_term_le hC.le hδ (by linarith) hTlog
  calc volume {t | t ∈ Icc T (2 * T) ∧ ∃ k : ℕ, ⌈max (2 * κ₀) k₁⌉₊ ≤ k ∧
        ¬ 0 < xiSliceCoeff t (2 * k)}
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
    _ ≤ (∑ j ∈ S, ENNReal.ofReal (A * T * (1 / 2) ^ j / κ₀ + C * T ^ ((1 : ℝ) / 2))) +
          ENNReal.ofReal (δ / 2 * T) := by gcongr with j hj; exact hscale j hj
    _ = ENNReal.ofReal (∑ j ∈ S, (A * T * (1 / 2) ^ j / κ₀ + C * T ^ ((1 : ℝ) / 2))) +
          ENNReal.ofReal (δ / 2 * T) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
    _ ≤ ENNReal.ofReal (δ * T / 2) + ENNReal.ofReal (δ / 2 * T) := by
        gcongr
        linarith
    _ = ENNReal.ofReal (δ * T) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end RHTower
