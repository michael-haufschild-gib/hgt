import GaloisForLFunctions.RHTower.MobiusMomentMatchedAssembly
import GaloisForLFunctions.RHTower.MobiusTwoJetLinearDensity

/-!
# Three-window third-jet extraction of a literal Möbius sector

For every large `R` and every odd squarefree `q ≤ Y = ⌊R^{2/5}⌋` run the moment-matched packet of
order `d = 2` (windows at `1/4, 1/2, 3/4`) with the single cofactor `q` and block length
`L_q = H_q/ε`, `H_q = q(4R/q)^α`.  All prime factors of `q` are below `R^{2/5} < R^{3/5} ≤ R/q`, so
every cofactor is admissible, and the union over `q` of the selected atoms splits into the even
atoms `A_R = {2qr}` and the odd atoms `B_R = {qp}`, with `μ(2qr) = μ(q)`, `μ(qp) = -μ(q)`,
`|A_R| = |B_R| ≥ c R`.  Summing the third-order bounds over `q ≤ Y`,

`‖P_R‖_δ ≤ C [R^{-1/10-δ/2} + R^{-137/500-δ/2} + R^{-11/500-δ/2}/log R]`

uniformly in `0 ≤ δ ≤ 1`, where the three exponents are `2/5 - 1/2`, `α - 3/2 + (2/5)(2-α)` and
`3α - 5/2 + (2/5)(3-3α)` at `α = 71/100`.
-/

open Finset Filter Topology

noncomputable section

namespace RHTower.CubicGamma

open RHTower.MomentSelector
open scoped ArithmeticFunction.Moebius

/-! ### Atoms of admissible shape -/

/-- The Möbius value of an atom of admissible shape. -/
theorem moebius_of_shape {R : ℝ} {q n : ℕ} (hq : Odd q) (h : AtomShape R q n) :
    (Even n → μ n = μ q) ∧ (¬ Even n → μ n = -μ q) := by
  obtain ⟨r, hr, hr2, -, hrq, hn⟩ := h
  have hndvd : ¬ r ∣ q := fun hd => by have := hrq r hr hd; omega
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  rcases hn with rfl | ⟨rfl, -⟩
  · exact ⟨fun _ => moebius_two_mul_mul_prime_of_not_dvd hq hr hndvd hr2,
      fun h => absurd ⟨q * r, by ring⟩ h⟩
  · exact ⟨fun h => absurd h (Nat.not_even_iff_odd.mpr (hq.mul hrodd)),
      fun _ => moebius_mul_prime_of_not_dvd hr hndvd⟩

/-! ### Scale bookkeeping -/

/-- Large-`R` thresholds for the three-window extraction. -/
theorem exists_threeWindow_threshold (z₀ ε : ℝ) :
    ∃ R₀ : ℝ, 5 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      max z₀ 2 ≤ R ^ ((3 : ℝ) / 5) ∧ 4 / ε ≤ R ^ ((3 : ℝ) / 5 * (1 - supplyExp)) ∧
        131072 * Real.log R ≤ R ^ ((3 : ℝ) / 5 * supplyExp) ∧
        5 * (Real.log 2 + 7) ≤ Real.log R := by
  have h1 : ∀ᶠ R : ℝ in atTop, max z₀ 2 ≤ R ^ ((3 : ℝ) / 5) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _
  have h2 : ∀ᶠ R : ℝ in atTop, 4 / ε ≤ R ^ ((3 : ℝ) / 5 * (1 - supplyExp)) :=
    (tendsto_rpow_atTop (by norm_num [supplyExp])).eventually_ge_atTop _
  have h3 : ∀ᶠ R : ℝ in atTop, 131072 * Real.log R ≤ R ^ ((3 : ℝ) / 5 * supplyExp) := by
    have ho := (isLittleO_log_rpow_atTop (by norm_num [supplyExp] :
      (0 : ℝ) < 3 / 5 * supplyExp)).def (c := 1 / 131072) (by norm_num)
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with R hR hR1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hR1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hR
    linarith
  have h4 : ∀ᶠ R : ℝ in atTop, 5 * (Real.log 2 + 7) ≤ Real.log R :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨X, hX⟩ := eventually_atTop.mp (((h1.and h2).and h3).and h4)
  refine ⟨max 5 X, le_max_left _ _, fun R hR => ?_⟩
  obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := hX R (le_of_max_le_right hR)
  exact ⟨a, b, c, e⟩

/-- For `1 ≤ q ≤ R^{2/5}`: `R/q ≥ R^{3/5}`, `H_q ≤ 4 R^{α + (2/5)(1-α)}`, `(R/q)^α ≥ R^{3α/5}`. -/
theorem threeWindow_scale {R : ℝ} (hR : 1 ≤ R) {q : ℕ} (hq : 1 ≤ q)
    (hqY : (q : ℝ) ≤ R ^ ((2 : ℝ) / 5)) :
    R ^ ((3 : ℝ) / 5) ≤ R / q ∧
      (q : ℝ) * (4 * R / q) ^ supplyExp ≤ 4 * R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) ∧
      R ^ ((3 : ℝ) / 5 * supplyExp) ≤ (R / q) ^ supplyExp := by
  have hR0 : 0 < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hRq : R ^ ((3 : ℝ) / 5) ≤ R / q := by
    rw [le_div_iff₀ hq0]
    calc R ^ ((3 : ℝ) / 5) * q ≤ R ^ ((3 : ℝ) / 5) * R ^ ((2 : ℝ) / 5) := by gcongr
      _ = R := by rw [← Real.rpow_add hR0]; norm_num
  refine ⟨hRq, ?_, ?_⟩
  · rw [cofactor_H_eq hq hR0.le]
    have hqα : (q : ℝ) * (R / q) ^ supplyExp = q ^ (1 - supplyExp) * R ^ supplyExp := by
      rw [Real.div_rpow hR0.le hq0.le, Real.rpow_sub hq0, Real.rpow_one]
      field_simp
    rw [hqα]
    have h1 : (q : ℝ) ^ (1 - supplyExp) ≤ R ^ (2 / 5 * (1 - supplyExp)) := by
      calc (q : ℝ) ^ (1 - supplyExp) ≤ (R ^ ((2 : ℝ) / 5)) ^ (1 - supplyExp) :=
            Real.rpow_le_rpow hq0.le hqY (by norm_num [supplyExp])
        _ = R ^ (2 / 5 * (1 - supplyExp)) := by rw [← Real.rpow_mul hR0.le]
    have h4 := four_rpow_supplyExp_le
    have hRα : 0 ≤ R ^ supplyExp := Real.rpow_nonneg hR0.le _
    calc (4 : ℝ) ^ supplyExp * ((q : ℝ) ^ (1 - supplyExp) * R ^ supplyExp)
        ≤ 4 * (R ^ (2 / 5 * (1 - supplyExp)) * R ^ supplyExp) := by
          gcongr
      _ = 4 * R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) := by
          rw [← Real.rpow_add hR0]; ring_nf
  · calc R ^ ((3 : ℝ) / 5 * supplyExp) = (R ^ ((3 : ℝ) / 5)) ^ supplyExp := by
          rw [← Real.rpow_mul hR0.le]
      _ ≤ (R / q) ^ supplyExp :=
          Real.rpow_le_rpow (Real.rpow_nonneg hR0.le _) hRq (by norm_num [supplyExp])


/-- The order-3 block bound summed over `J` blocks with `J L ≤ 2R`. -/
theorem threeWindow_block_arith {R δ L : ℝ} (hR : 1 ≤ R) (hL : 0 ≤ L) {J m : ℕ}
    (hJL : (J : ℝ) * L ≤ 2 * R) :
    (J : ℝ) * (∑ i ∈ range 2, 2 * L ^ (i + 1) / ((i + 1).factorial : ℝ) *
        (jetConst (i + 1) * R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (i + 1)) +
      ((2 * m : ℕ) : ℝ) * (L ^ (2 + 1) / ((2 + 1).factorial : ℝ) *
        (jetConst (2 + 1) * (4 * R ^ 2) * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (2 + 1)))) ≤
      4 * jetConst 1 * (R * R * (R ^ ((5 + δ) / 2))⁻¹) +
        2 * jetConst 2 * (R * L * (R ^ ((5 + δ) / 2))⁻¹) +
        8 / 3 * jetConst 3 * (m * L ^ 2 * (R ^ ((5 + δ) / 2))⁻¹) := by
  have hR0 : 0 < R := by linarith
  have he : 0 < R ^ ((5 + δ) / 2) := Real.rpow_pos_of_pos hR0 _
  set E := (R ^ ((5 + δ) / 2))⁻¹ with hE
  have hE0 : 0 ≤ E := (inv_pos.mpr he).le
  have hj1 := jetConst_nonneg 1
  have hj2 := jetConst_nonneg 2
  have hj3 := jetConst_nonneg 3
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have e : (J : ℝ) * (∑ i ∈ range 2, 2 * L ^ (i + 1) / ((i + 1).factorial : ℝ) *
        (jetConst (i + 1) * R ^ 2 * E / R ^ (i + 1)) +
      ((2 * m : ℕ) : ℝ) * (L ^ (2 + 1) / ((2 + 1).factorial : ℝ) *
        (jetConst (2 + 1) * (4 * R ^ 2) * E / R ^ (2 + 1)))) =
      2 * jetConst 1 * (J * L) * R * E + jetConst 2 * (J * L) * L * E +
        4 / 3 * jetConst 3 * (J * L) * m * L ^ 2 * E / R := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
    field_simp
    ring
  rw [e]
  have h1 : 2 * jetConst 1 * (J * L) * R * E ≤ 4 * jetConst 1 * (R * R * E) := by
    have := mul_le_mul_of_nonneg_left hJL (by positivity : (0 : ℝ) ≤ 2 * jetConst 1)
    calc 2 * jetConst 1 * (J * L) * R * E = (2 * jetConst 1 * (J * L)) * (R * E) := by ring
      _ ≤ (2 * jetConst 1 * (2 * R)) * (R * E) := by gcongr
      _ = _ := by ring
  have h2 : jetConst 2 * (J * L) * L * E ≤ 2 * jetConst 2 * (R * L * E) := by
    calc jetConst 2 * (J * L) * L * E = jetConst 2 * (J * L) * (L * E) := by ring
      _ ≤ jetConst 2 * (2 * R) * (L * E) := by gcongr
      _ = _ := by ring
  have h3 : 4 / 3 * jetConst 3 * (J * L) * m * L ^ 2 * E / R ≤
      8 / 3 * jetConst 3 * (m * L ^ 2 * E) := by
    rw [div_le_iff₀ hR0]
    calc 4 / 3 * jetConst 3 * (J * L) * m * L ^ 2 * E = 4 / 3 * jetConst 3 * (J * L) *
          (m * L ^ 2 * E) := by ring
      _ ≤ 4 / 3 * jetConst 3 * (2 * R) * (m * L ^ 2 * E) := by gcongr
      _ = _ := by ring
  linarith

/-- `Σ_{q ∈ Q} q^s ≤ Y^{1+s}` for `Q ⊆ [1, Y]`, `s ≥ 0`. -/
theorem sum_rpow_le_of_subset {Y : ℕ} {Q : Finset ℕ} (hQ : Q ⊆ Icc 1 Y) {s : ℝ} (hs : 0 ≤ s) :
    ∑ q ∈ Q, (q : ℝ) ^ s ≤ (Y : ℝ) ^ (1 + s) := by
  rcases Nat.eq_zero_or_pos Y with hY | hY
  · have : Q = ∅ := by
      rw [hY] at hQ
      exact subset_empty.mp (hQ.trans (by simp))
    subst this
    simp only [sum_empty]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hterm : ∀ q ∈ Q, (q : ℝ) ^ s ≤ (Y : ℝ) ^ s := fun q hq =>
    Real.rpow_le_rpow (Nat.cast_nonneg q) (by exact_mod_cast (mem_Icc.mp (hQ hq)).2) hs
  have hcard : (Q.card : ℝ) ≤ Y := by
    have := card_le_card hQ
    simp at this
    exact_mod_cast this
  calc ∑ q ∈ Q, (q : ℝ) ^ s ≤ ∑ _q ∈ Q, (Y : ℝ) ^ s := sum_le_sum hterm
    _ = Q.card * (Y : ℝ) ^ s := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Y * (Y : ℝ) ^ s := by gcongr
    _ = (Y : ℝ) ^ (1 + s) := by rw [Real.rpow_add hY0, Real.rpow_one]

/-- `Σ_{q ∈ Q} q^{-c} ≤ 3 Y^{1-c}` for `Q ⊆ [1, Y]`, `0 < c ≤ 1/2`. -/
theorem sum_rpow_neg_le_of_subset {Y : ℕ} (hY : 1 ≤ Y) {Q : Finset ℕ} (hQ : Q ⊆ Icc 1 Y) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) :
    ∑ q ∈ Q, (q : ℝ) ^ (-c) ≤ 3 * (Y : ℝ) ^ (1 - c) := by
  have hsub : ∑ q ∈ Q, (q : ℝ) ^ (-c) ≤ ∑ q ∈ Icc 1 Y, (q : ℝ) ^ (-c) :=
    sum_le_sum_of_subset_of_nonneg hQ fun q _ _ => Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hhead := RHTower.sum_rpow_neg_head_le hc0 (by linarith) Y
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) ^ (1 - c) :=
    Real.one_le_rpow (by exact_mod_cast hY) (by linarith)
  have hdiv : (Y : ℝ) ^ (1 - c) / (1 - c) ≤ 2 * (Y : ℝ) ^ (1 - c) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith


/-! ### The three sums over cofactors -/

theorem threeWindow_part_one {R δ : ℝ} (hR : 1 ≤ R) {Q : Finset ℕ} {Y : ℕ}
    (hQ : Q ⊆ Icc 1 Y) (hY : (Y : ℝ) ≤ R ^ ((2 : ℝ) / 5)) :
    ∑ _q ∈ Q, 4 * jetConst 1 * (R * R * (R ^ ((5 + δ) / 2))⁻¹) ≤
      4 * jetConst 1 * R ^ (-(1 / 10 : ℝ) - δ / 2) := by
  have hR0 : 0 < R := by linarith
  have hcard : (Q.card : ℝ) ≤ R ^ ((2 : ℝ) / 5) := by
    have := card_le_card hQ
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    exact (by exact_mod_cast this : (Q.card : ℝ) ≤ Y).trans hY
  rw [sum_const, nsmul_eq_mul]
  have hid : R ^ ((2 : ℝ) / 5) * (R * R * (R ^ ((5 + δ) / 2))⁻¹) =
      R ^ (-(1 / 10 : ℝ) - δ / 2) := by
    rw [← Real.rpow_neg hR0.le, show R * R = R ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
      ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1; ring
  have h0 : 0 ≤ R * R * (R ^ ((5 + δ) / 2))⁻¹ := by
    have := Real.rpow_pos_of_pos hR0 ((5 + δ) / 2); positivity
  have hj := jetConst_nonneg 1
  calc (Q.card : ℝ) * (4 * jetConst 1 * (R * R * (R ^ ((5 + δ) / 2))⁻¹))
      ≤ R ^ ((2 : ℝ) / 5) * (4 * jetConst 1 * (R * R * (R ^ ((5 + δ) / 2))⁻¹)) := by gcongr
    _ = 4 * jetConst 1 * (R ^ ((2 : ℝ) / 5) * (R * R * (R ^ ((5 + δ) / 2))⁻¹)) := by ring
    _ = _ := by rw [hid]

theorem threeWindow_part_two {R δ ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) {Q : Finset ℕ} {Y : ℕ}
    (hQ : Q ⊆ Icc 1 Y) (hY : (Y : ℝ) ≤ R ^ ((2 : ℝ) / 5)) :
    ∑ q ∈ Q, 2 * jetConst 2 * (R * ((q : ℝ) * (4 * R / q) ^ supplyExp / ε) *
      (R ^ ((5 + δ) / 2))⁻¹) ≤ 8 * jetConst 2 / ε * R ^ (-(137 / 500 : ℝ) - δ / 2) := by
  have hR0 : 0 < R := by linarith
  have hj := jetConst_nonneg 2
  have hE : 0 ≤ (R ^ ((5 + δ) / 2))⁻¹ := (inv_pos.mpr (Real.rpow_pos_of_pos hR0 _)).le
  -- `q (4R/q)^α ≤ 4 q^{1-α} R^α`
  have hterm : ∀ q ∈ Q, (q : ℝ) * (4 * R / q) ^ supplyExp ≤
      4 * ((q : ℝ) ^ (1 - supplyExp) * R ^ supplyExp) := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp (hQ hq)).1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    rw [cofactor_H_eq hq1 hR0.le]
    have e : (q : ℝ) * (R / q) ^ supplyExp = (q : ℝ) ^ (1 - supplyExp) * R ^ supplyExp := by
      rw [Real.div_rpow hR0.le hq0.le, Real.rpow_sub hq0, Real.rpow_one]; field_simp
    rw [e]
    have := four_rpow_supplyExp_le
    have : 0 ≤ (q : ℝ) ^ (1 - supplyExp) * R ^ supplyExp := by
      have := Real.rpow_nonneg hq0.le (1 - supplyExp)
      have := Real.rpow_nonneg hR0.le supplyExp
      positivity
    gcongr
  have hsum := sum_rpow_le_of_subset hQ (s := 1 - supplyExp) (by norm_num [supplyExp])
  have hY1 : (Y : ℝ) ^ (1 + (1 - supplyExp)) ≤ R ^ ((2 : ℝ) / 5 * (2 - supplyExp)) := by
    calc (Y : ℝ) ^ (1 + (1 - supplyExp)) ≤ (R ^ ((2 : ℝ) / 5)) ^ (1 + (1 - supplyExp)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg Y) hY (by norm_num [supplyExp])
      _ = R ^ ((2 : ℝ) / 5 * (2 - supplyExp)) := by rw [← Real.rpow_mul hR0.le]; ring_nf
  have hid : R * R ^ supplyExp * R ^ ((2 : ℝ) / 5 * (2 - supplyExp)) * (R ^ ((5 + δ) / 2))⁻¹ =
      R ^ (-(137 / 500 : ℝ) - δ / 2) := by
    rw [← Real.rpow_neg hR0.le, show R * R ^ supplyExp = R ^ (1 : ℝ) * R ^ supplyExp by
      rw [Real.rpow_one], ← Real.rpow_add hR0, ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1; norm_num [supplyExp]; ring
  have hrewrite : ∑ q ∈ Q, 2 * jetConst 2 * (R * ((q : ℝ) * (4 * R / q) ^ supplyExp / ε) *
      (R ^ ((5 + δ) / 2))⁻¹) = 2 * jetConst 2 * R * (R ^ ((5 + δ) / 2))⁻¹ / ε *
        ∑ q ∈ Q, (q : ℝ) * (4 * R / q) ^ supplyExp := by
    rw [mul_sum]; apply sum_congr rfl; intro q _; field_simp
  rw [hrewrite]
  have hc : 0 ≤ 2 * jetConst 2 * R * (R ^ ((5 + δ) / 2))⁻¹ / ε := by positivity
  have hRα : 0 ≤ R ^ supplyExp := Real.rpow_nonneg hR0.le _
  calc 2 * jetConst 2 * R * (R ^ ((5 + δ) / 2))⁻¹ / ε * ∑ q ∈ Q, (q : ℝ) * (4 * R / q) ^ supplyExp
      ≤ 2 * jetConst 2 * R * (R ^ ((5 + δ) / 2))⁻¹ / ε *
          ∑ q ∈ Q, 4 * ((q : ℝ) ^ (1 - supplyExp) * R ^ supplyExp) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) hc
    _ = 8 * jetConst 2 / ε * (R * R ^ supplyExp * (∑ q ∈ Q, (q : ℝ) ^ (1 - supplyExp)) *
          (R ^ ((5 + δ) / 2))⁻¹) := by
        rw [← mul_sum, ← sum_mul]; ring
    _ ≤ 8 * jetConst 2 / ε * (R * R ^ supplyExp * R ^ ((2 : ℝ) / 5 * (2 - supplyExp)) *
          (R ^ ((5 + δ) / 2))⁻¹) := by
        gcongr
        exact hsum.trans hY1
    _ = _ := by rw [hid]

/-- `m_q L_q² ≤ R^{3α} q^{2-3α} / (2048 ε² log R)` for `m_q ≤ (R/q)^α/(32768 log 5R)`,
`L_q = q(4R/q)^α/ε`. -/
theorem supply_mul_length_sq_le {R ε : ℝ} (hR : 5 ≤ R) (hε : 0 < ε) {q : ℕ} (hq1 : 1 ≤ q)
    {mq : ℝ} (hm : mq ≤ (R / q) ^ supplyExp / (32768 * Real.log (5 * R))) :
    mq * ((q : ℝ) * (4 * R / q) ^ supplyExp / ε) ^ 2 ≤
      R ^ (3 * supplyExp) * (q : ℝ) ^ (-(3 * supplyExp - 2)) / (2048 * ε ^ 2 * Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog5 : Real.log R ≤ Real.log (5 * R) := Real.log_le_log hR0 (by linarith)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  rw [cofactor_H_eq hq1 hR0.le]
  have h16 : ((4 : ℝ) ^ supplyExp) ^ 2 ≤ 16 := by
    have := four_rpow_supplyExp_le
    have h0 : 0 ≤ (4 : ℝ) ^ supplyExp := Real.rpow_nonneg (by norm_num) _
    nlinarith
  have hRq : 0 < R / q := by positivity
  have hkey : (R / q) ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp) ^ 2 =
      R ^ (3 * supplyExp) * (q : ℝ) ^ (-(3 * supplyExp - 2)) := by
    have e1 : ((R / q) ^ supplyExp) ^ 2 = (R / q) ^ (2 * supplyExp) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hRq.le]; ring_nf
    have e2 : (R / q) ^ supplyExp * (R / q) ^ (2 * supplyExp) = (R / q) ^ (3 * supplyExp) := by
      rw [← Real.rpow_add hRq]; ring_nf
    have e3 : (R / q) ^ (3 * supplyExp) = R ^ (3 * supplyExp) / (q : ℝ) ^ (3 * supplyExp) :=
      Real.div_rpow hR0.le hq0.le _
    have e4 : (q : ℝ) ^ (-(3 * supplyExp - 2)) = (q : ℝ) ^ 2 / (q : ℝ) ^ (3 * supplyExp) := by
      rw [show -(3 * supplyExp - 2) = (2 : ℝ) - 3 * supplyExp by ring, Real.rpow_sub hq0,
        Real.rpow_two]
    calc (R / q) ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp) ^ 2
        = (q : ℝ) ^ 2 * ((R / q) ^ supplyExp * ((R / q) ^ supplyExp) ^ 2) := by ring
      _ = (q : ℝ) ^ 2 * (R / q) ^ (3 * supplyExp) := by rw [e1, e2]
      _ = _ := by rw [e3, e4]; ring
  have hA0 : 0 ≤ ((q : ℝ) * (R / q) ^ supplyExp) ^ 2 := sq_nonneg _
  calc mq * (4 ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp) / ε) ^ 2
      = mq * ((4 : ℝ) ^ supplyExp) ^ 2 * ((q : ℝ) * (R / q) ^ supplyExp) ^ 2 / ε ^ 2 := by
        ring
    _ ≤ (R / q) ^ supplyExp / (32768 * Real.log R) * 16 * ((q : ℝ) * (R / q) ^ supplyExp) ^ 2 /
          ε ^ 2 := by
        gcongr
        exact hm.trans (by gcongr)
    _ = R ^ (3 * supplyExp) * (q : ℝ) ^ (-(3 * supplyExp - 2)) / (2048 * ε ^ 2 * Real.log R) := by
        rw [← hkey]; field_simp; ring

theorem threeWindow_part_three {R δ ε : ℝ} (hR : 5 ≤ R) (hε : 0 < ε) {Q : Finset ℕ} {Y : ℕ}
    (hY1 : 1 ≤ Y) (hQ : Q ⊆ Icc 1 Y) (hY : (Y : ℝ) ≤ R ^ ((2 : ℝ) / 5)) (m : ℕ → ℕ)
    (hm : ∀ q ∈ Q, (m q : ℝ) ≤ (R / q) ^ supplyExp / (32768 * Real.log (5 * R))) :
    ∑ q ∈ Q, 8 / 3 * jetConst 3 * ((m q : ℝ) * ((q : ℝ) * (4 * R / q) ^ supplyExp / ε) ^ 2 *
      (R ^ ((5 + δ) / 2))⁻¹) ≤
      jetConst 3 / (256 * ε ^ 2) * (R ^ (-(11 / 500 : ℝ) - δ / 2) / Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog5 : Real.log R ≤ Real.log (5 * R) := Real.log_le_log hR0 (by linarith)
  have hj := jetConst_nonneg 3
  have hE : 0 < (R ^ ((5 + δ) / 2))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hR0 _)
  have hterm : ∀ q ∈ Q, (m q : ℝ) * ((q : ℝ) * (4 * R / q) ^ supplyExp / ε) ^ 2 ≤
      R ^ (3 * supplyExp) * (q : ℝ) ^ (-(3 * supplyExp - 2)) / (2048 * ε ^ 2 * Real.log R) :=
    fun q hq => supply_mul_length_sq_le hR hε (mem_Icc.mp (hQ hq)).1 (hm q hq)
  have hsum := sum_rpow_neg_le_of_subset hY1 hQ (c := 3 * supplyExp - 2)
    (by norm_num [supplyExp]) (by norm_num [supplyExp])
  have hYR : (Y : ℝ) ^ (1 - (3 * supplyExp - 2)) ≤ R ^ ((2 : ℝ) / 5 * (3 - 3 * supplyExp)) := by
    calc (Y : ℝ) ^ (1 - (3 * supplyExp - 2)) ≤ (R ^ ((2 : ℝ) / 5)) ^ (1 - (3 * supplyExp - 2)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg Y) hY (by norm_num [supplyExp])
      _ = R ^ ((2 : ℝ) / 5 * (3 - 3 * supplyExp)) := by rw [← Real.rpow_mul hR0.le]; ring_nf
  have hid : R ^ (3 * supplyExp) * R ^ ((2 : ℝ) / 5 * (3 - 3 * supplyExp)) *
      (R ^ ((5 + δ) / 2))⁻¹ = R ^ (-(11 / 500 : ℝ) - δ / 2) := by
    rw [← Real.rpow_neg hR0.le, ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1; norm_num [supplyExp]; ring
  calc ∑ q ∈ Q, 8 / 3 * jetConst 3 * ((m q : ℝ) * ((q : ℝ) * (4 * R / q) ^ supplyExp / ε) ^ 2 *
        (R ^ ((5 + δ) / 2))⁻¹)
      ≤ ∑ q ∈ Q, 8 / 3 * jetConst 3 * (R ^ (3 * supplyExp) * (q : ℝ) ^ (-(3 * supplyExp - 2)) /
          (2048 * ε ^ 2 * Real.log R) * (R ^ ((5 + δ) / 2))⁻¹) := by
        apply sum_le_sum; intro q hq; gcongr; exact hterm q hq
    _ = jetConst 3 / (768 * ε ^ 2) * (R ^ (3 * supplyExp) * (R ^ ((5 + δ) / 2))⁻¹ / Real.log R) *
          ∑ q ∈ Q, (q : ℝ) ^ (-(3 * supplyExp - 2)) := by
        rw [mul_sum]; apply sum_congr rfl; intro q _; field_simp; ring
    _ ≤ jetConst 3 / (768 * ε ^ 2) * (R ^ (3 * supplyExp) * (R ^ ((5 + δ) / 2))⁻¹ / Real.log R) *
          (3 * R ^ ((2 : ℝ) / 5 * (3 - 3 * supplyExp))) := by
        have := Real.rpow_nonneg hR0.le (3 * supplyExp)
        gcongr
        exact hsum.trans (by gcongr)
    _ = jetConst 3 / (256 * ε ^ 2) * (R ^ (3 * supplyExp) * R ^ ((2 : ℝ) / 5 * (3 - 3 * supplyExp)) *
          (R ^ ((5 + δ) / 2))⁻¹ / Real.log R) := by field_simp; ring
    _ = _ := by rw [hid]


/-! ### The extraction (1) -/

/-- Per-cofactor structure of a single-cofactor packet: the even atoms are exactly one Möbius side
and the odd atoms the other, so each has `J m_q` elements. -/
theorem card_filter_even_single {R : ℝ} {q : ℕ} (hq : Odd q) (hqs : Squarefree q)
    {UP UN : Finset ℕ} (hμP : ∀ n ∈ UP, μ n = 1)
    (hμN : ∀ n ∈ UN, μ n = -1) (hsh : ∀ n ∈ UP ∪ UN, AtomShape R q n) {k : ℕ}
    (hcP : UP.card = k) (hcN : UN.card = k) :
    ((UP ∪ UN).filter Even).card = k ∧ ((UP ∪ UN).filter fun n => ¬ Even n).card = k := by
  have hsgn : ∀ n ∈ UP ∪ UN, (Even n → μ n = μ q) ∧ (¬ Even n → μ n = -μ q) :=
    fun n hn => moebius_of_shape hq (hsh n hn)
  rw [filter_union, filter_union]
  rcases moebius_squarefree_cases hqs with h | h
  · -- `μ(q) = 1`: the positive side is even
    have hP : UP.filter Even = UP := filter_true_of_mem fun n hn => by
      by_contra he
      have := (hsgn n (mem_union_left _ hn)).2 he
      rw [hμP n hn, h] at this; norm_num at this
    have hN : UN.filter Even = ∅ := filter_false_of_mem fun n hn he => by
      have := (hsgn n (mem_union_right _ hn)).1 he
      rw [hμN n hn, h] at this; norm_num at this
    have hP' : UP.filter (fun n => ¬ Even n) = ∅ := filter_false_of_mem fun n hn he => by
      have := (hsgn n (mem_union_left _ hn)).2 he
      rw [hμP n hn, h] at this; norm_num at this
    have hN' : UN.filter (fun n => ¬ Even n) = UN := filter_true_of_mem fun n hn he => by
      have := (hsgn n (mem_union_right _ hn)).1 he
      rw [hμN n hn, h] at this; norm_num at this
    rw [hP, hN, hP', hN', union_empty, empty_union]
    exact ⟨hcP, hcN⟩
  · -- `μ(q) = -1`: the negative side is even
    have hP : UP.filter Even = ∅ := filter_false_of_mem fun n hn he => by
      have := (hsgn n (mem_union_left _ hn)).1 he
      rw [hμP n hn, h] at this; norm_num at this
    have hN : UN.filter Even = UN := filter_true_of_mem fun n hn => by
      by_contra he
      have := (hsgn n (mem_union_right _ hn)).2 he
      rw [hμN n hn, h] at this; norm_num at this
    have hP' : UP.filter (fun n => ¬ Even n) = UP := filter_true_of_mem fun n hn he => by
      have := (hsgn n (mem_union_left _ hn)).1 he
      rw [hμP n hn, h] at this; norm_num at this
    have hN' : UN.filter (fun n => ¬ Even n) = ∅ := filter_false_of_mem fun n hn he => by
      have := (hsgn n (mem_union_right _ hn)).2 he
      rw [hμN n hn, h] at this; norm_num at this
    rw [hP, hN, hP', hN', union_empty, empty_union]
    exact ⟨hcN, hcP⟩

/-- The block length `L_q = H_q/ε` is positive and at most `R` for `q ≤ R^{2/5}`. -/
theorem threeWindow_length {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) {q : ℕ} (hq : 1 ≤ q)
    (hqY : (q : ℝ) ≤ R ^ ((2 : ℝ) / 5)) (hLR : 4 / ε ≤ R ^ ((3 : ℝ) / 5 * (1 - supplyExp))) :
    0 < (q : ℝ) * (4 * R / q) ^ supplyExp / ε ∧ (q : ℝ) * (4 * R / q) ^ supplyExp / ε ≤ R := by
  have hR0 : 0 < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨-, hH, -⟩ := threeWindow_scale hR hq hqY
  refine ⟨by have := Real.rpow_pos_of_pos (by positivity : 0 < 4 * R / q) supplyExp; positivity,
    ?_⟩
  rw [div_le_iff₀ hε]
  have hsplit : R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) * R ^ ((3 : ℝ) / 5 * (1 - supplyExp)) =
      R := by rw [← Real.rpow_add hR0]; norm_num [supplyExp]
  have h1 : 4 ≤ R ^ ((3 : ℝ) / 5 * (1 - supplyExp)) * ε := by
    have := (div_le_iff₀ hε).mp hLR
    linarith
  have h0 : 0 ≤ R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) := Real.rpow_nonneg hR0.le _
  calc (q : ℝ) * (4 * R / q) ^ supplyExp ≤ 4 * R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) := hH
    _ ≤ R ^ ((3 : ℝ) / 5 * (1 - supplyExp)) * ε * R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) :=
        by nlinarith
    _ = (R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) * R ^ ((3 : ℝ) / 5 * (1 - supplyExp))) * ε := by
        ring
    _ = R * ε := by rw [hsplit]

/-- The selected count of one cofactor: `J_q m_q ≥ ε R/(2^{19} q log R)`. -/
theorem threeWindow_count {R ε : ℝ} (hR : 5 ≤ R) (hε : 0 < ε) {q : ℕ} (hq : 1 ≤ q)
    (hqY : (q : ℝ) ≤ R ^ ((2 : ℝ) / 5)) (hLR : 4 / ε ≤ R ^ ((3 : ℝ) / 5 * (1 - supplyExp)))
    (hlogm : 131072 * Real.log R ≤ R ^ ((3 : ℝ) / 5 * supplyExp)) :
    ε * R / (2 ^ 19 * Real.log R) * (1 / (q : ℝ)) ≤
      (⌊2 * R / ((q : ℝ) * (4 * R / q) ^ supplyExp / ε)⌋₊ : ℝ) * (cofactorSupply R q : ℝ) := by
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog5 : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
  have hlog52 : Real.log (5 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) hR0.ne']
    have : Real.log 5 ≤ Real.log R := Real.log_le_log (by norm_num) hR
    linarith
  obtain ⟨hL0, hLR'⟩ := threeWindow_length hR1 hε hq hqY hLR
  obtain ⟨-, -, hRqα⟩ := threeWindow_scale hR1 hq hqY
  set L := (q : ℝ) * (4 * R / q) ^ supplyExp / ε with hLdef
  -- `J ≥ R/L`
  have hJ : R / L ≤ (⌊2 * R / L⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (2 * R / L)
    have hRL : 1 ≤ R / L := by rw [le_div_iff₀ hL0]; linarith
    have : 2 * R / L = 2 * (R / L) := by ring
    linarith
  -- `m ≥ (R/q)^α/(65536 log 5R)`
  set x := (R / q) ^ supplyExp / (32768 * Real.log (5 * R)) with hx
  have hx2 : 2 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]
    nlinarith
  have hm : x / 2 ≤ (cofactorSupply R q : ℝ) := by
    have h := Nat.lt_floor_add_one x
    unfold cofactorSupply
    rw [← hx]
    linarith
  have hRqpos : 0 < (R / q) ^ supplyExp := Real.rpow_pos_of_pos (by positivity) _
  have hLeq : L = 4 ^ supplyExp * ((q : ℝ) * (R / q) ^ supplyExp) / ε := by
    rw [hLdef, cofactor_H_eq hq hR0.le]
  have h4 := four_rpow_supplyExp_le
  have h40 : 0 < (4 : ℝ) ^ supplyExp := Real.rpow_pos_of_pos (by norm_num) _
  have e : R / L * (x / 2) = ε * R / (2 * 4 ^ supplyExp * 32768 * Real.log (5 * R) * q) := by
    rw [hLeq, hx]
    field_simp
  have hden : 2 * 4 ^ supplyExp * 32768 * Real.log (5 * R) * q ≤ 2 ^ 19 * Real.log R * q := by
    have : (4 : ℝ) ^ supplyExp * Real.log (5 * R) ≤ 4 * (2 * Real.log R) :=
      mul_le_mul h4 hlog52 hlog5.le (by norm_num)
    nlinarith
  calc ε * R / (2 ^ 19 * Real.log R) * (1 / (q : ℝ)) = ε * R / (2 ^ 19 * Real.log R * q) := by
        field_simp
    _ ≤ ε * R / (2 * 4 ^ supplyExp * 32768 * Real.log (5 * R) * q) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = R / L * (x / 2) := e.symm
    _ ≤ _ := mul_le_mul hJ hm (by positivity) (Nat.cast_nonneg _)

/-- **Three-window third-jet extraction (1).**  For all large `R` there are disjoint sets
`A_R = {2qr}` and `B_R = {qp}` in `(2R, 4R)`, `q ≤ ⌊R^{2/5}⌋` odd squarefree, `r > R/q`,
`p > 2R/q` primes, with `μ(2qr) = μ(q)`, `μ(qp) = -μ(q)`, `|A_R| = |B_R| ≥ c R`, and uniformly in
`0 ≤ δ ≤ 1`
`‖Σ_{n ∈ A_R ∪ B_R} μ(n) f_n‖_δ ≤ C [R^{-1/10-δ/2} + R^{-137/500-δ/2} + R^{-11/500-δ/2}/log R]`. -/
theorem exists_threeWindow_extraction :
    ∃ c C R₀ : ℝ, 0 < c ∧ 0 < C ∧ 5 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ A B : Finset ℕ, Disjoint A B ∧ (∀ a ∈ A, Even a) ∧ (∀ b ∈ B, ¬ Even b) ∧
        (∀ a ∈ A, 2 * R < a ∧ (a : ℝ) < 4 * R ∧ ∃ q r : ℕ, Odd q ∧ Squarefree q ∧
          q ≤ ⌊R ^ ((2 : ℝ) / 5)⌋₊ ∧ r.Prime ∧ R / q < r ∧ a = 2 * q * r ∧ μ a = μ q) ∧
        (∀ b ∈ B, 2 * R < b ∧ (b : ℝ) < 4 * R ∧ ∃ q p : ℕ, Odd q ∧ Squarefree q ∧
          q ≤ ⌊R ^ ((2 : ℝ) / 5)⌋₊ ∧ p.Prime ∧ 2 * R / q < p ∧ b = q * p ∧ μ b = -μ q) ∧
        A.card = B.card ∧ c * R ≤ A.card ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ A ∪ B, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (R ^ (-(1 / 10 : ℝ) - δ / 2) + R ^ (-(137 / 500 : ℝ) - δ / 2) +
              R ^ (-(11 / 500 : ℝ) - δ / 2) / Real.log R) := by
  obtain ⟨ε, hε0, z₀, hz₀, hfam⟩ := exists_family_packet (d := 2) (by norm_num)
  obtain ⟨R₀, hR₀, hthr⟩ := exists_threeWindow_threshold z₀ ε
  have hj1 := jetConst_nonneg 1
  have hj2 := jetConst_nonneg 2
  have hj3 := jetConst_nonneg 3
  refine ⟨ε / (40 * 2 ^ 19), 4 * jetConst 1 + 8 * jetConst 2 / ε + jetConst 3 / (256 * ε ^ 2) + 1,
    R₀, by positivity, by positivity, hR₀, fun R hR => ?_⟩
  obtain ⟨hz, hLR, hlogm, hlogR⟩ := hthr R hR
  have hR5 : 5 ≤ R := hR₀.trans hR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hlogpos : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog5 : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
  have hlog52 : Real.log (5 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) hR0.ne']
    have : Real.log 5 ≤ Real.log R := Real.log_le_log (by norm_num) hR5
    linarith
  set Y : ℕ := ⌊R ^ ((2 : ℝ) / 5)⌋₊ with hYdef
  have hR25 : 1 ≤ R ^ ((2 : ℝ) / 5) := Real.one_le_rpow hR1 (by norm_num)
  have hY1 : 1 ≤ Y := Nat.le_floor (by exact_mod_cast hR25)
  have hYR : (Y : ℝ) ≤ R ^ ((2 : ℝ) / 5) := Nat.floor_le (by linarith)
  set Q : Finset ℕ := (Icc 1 Y).filter fun q => Odd q ∧ Squarefree q with hQdef
  have hQsub : Q ⊆ Icc 1 Y := filter_subset _ _
  have hQmem : ∀ q ∈ Q, 1 ≤ q ∧ (q : ℝ) ≤ R ^ ((2 : ℝ) / 5) ∧ Odd q ∧ Squarefree q := by
    intro q hq
    rw [hQdef, mem_filter, mem_Icc] at hq
    exact ⟨hq.1.1, (by exact_mod_cast hq.1.2 : (q : ℝ) ≤ Y).trans hYR, hq.2⟩
  have hR35 : R ^ ((2 : ℝ) / 5) < R ^ ((3 : ℝ) / 5) := by
    rcases eq_or_lt_of_le hR1 with h | h
    · rw [← h] at hR5; norm_num at hR5
    · exact Real.rpow_lt_rpow_of_exponent_lt h (by norm_num)
  set L : ℕ → ℝ := fun q => (q : ℝ) * (4 * R / q) ^ supplyExp / ε with hLdef
  -- the single-cofactor packets
  have hex : ∀ q ∈ Q, ∃ UP UN : Finset ℕ, Disjoint UP UN ∧
      (∀ n ∈ UP, μ n = 1) ∧ (∀ n ∈ UN, μ n = -1) ∧
      (∀ n ∈ UP ∪ UN, 2 * R < n ∧ (n : ℝ) < 4 * R ∧ AtomShape R q n) ∧
      UP.card = ⌊2 * R / L q⌋₊ * cofactorSupply R q ∧
      UN.card = ⌊2 * R / L q⌋₊ * cofactorSupply R q ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ n ∈ UP ∪ UN, ((μ n : ℤ) : ℝ) * atom n t) ≤
          4 * jetConst 1 * (R * R * (R ^ ((5 + δ) / 2))⁻¹) +
            2 * jetConst 2 * (R * L q * (R ^ ((5 + δ) / 2))⁻¹) +
            8 / 3 * jetConst 3 * (cofactorSupply R q * L q ^ 2 * (R ^ ((5 + δ) / 2))⁻¹) := by
    intro q hq
    obtain ⟨hq1, hqY, hqodd, hqsq⟩ := hQmem q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    obtain ⟨hRq, hH, -⟩ := threeWindow_scale hR1 hq1 hqY
    have hH0 : 0 < (q : ℝ) * (4 * R / q) ^ supplyExp := by
      have := Real.rpow_pos_of_pos (by positivity : 0 < 4 * R / q) supplyExp; positivity
    have hL0 : 0 < L q := by simp only [hLdef]; positivity
    have hLq : L q ≤ R := by
      simp only [hLdef]
      rw [div_le_iff₀ hε0]
      have hsplit : R * ε = 4 * R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) *
          (R ^ ((3 : ℝ) / 5 * (1 - supplyExp)) * ε / 4) := by
        have : R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) * R ^ ((3 : ℝ) / 5 * (1 - supplyExp)) = R := by
          rw [← Real.rpow_add hR0]; norm_num [supplyExp]
        calc R * ε = R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) *
              R ^ ((3 : ℝ) / 5 * (1 - supplyExp)) * ε := by rw [this]
          _ = _ := by ring
      have h1 : 1 ≤ R ^ ((3 : ℝ) / 5 * (1 - supplyExp)) * ε / 4 := by
        rw [le_div_iff₀ (by norm_num)]
        have := (div_le_iff₀ hε0).mp hLR
        linarith
      rw [hsplit]
      have h4 : 0 ≤ 4 * R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) := by
        have := Real.rpow_nonneg hR0.le (supplyExp + 2 / 5 * (1 - supplyExp)); positivity
      calc (q : ℝ) * (4 * R / q) ^ supplyExp ≤ 4 * R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) := hH
        _ = 4 * R ^ (supplyExp + 2 / 5 * (1 - supplyExp)) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 h4
    have hadm : AdmissibleCofactor R q := by
      refine ⟨hq1, hqodd, hqsq, fun ℓ hℓ hℓq => ?_⟩
      have : (ℓ : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) hℓq
      linarith
    have hFq : ∀ q' ∈ ({q} : Finset ℕ), AdmissibleCofactor R q' ∧ 2 ≤ R / q' ∧ z₀ ≤ R / q' ∧
        (q' : ℝ) * (4 * R / q') ^ supplyExp ≤ ε * L q := by
      intro q' hq'
      rw [mem_singleton] at hq'
      subst hq'
      refine ⟨hadm, (le_max_right _ _).trans (hz.trans hRq), (le_max_left _ _).trans
        (hz.trans hRq), ?_⟩
      simp only [hLdef]
      rw [mul_div_cancel₀ _ hε0.ne']
    obtain ⟨UP, UN, hd, hμP, hμN, hpos, hcP, hcN, hnorm⟩ := hfam R (L q) {q} hR5 hL0 hLq hFq
    have hJL : ((⌊2 * R / L q⌋₊ : ℕ) : ℝ) * L q ≤ 2 * R := by
      have h := Nat.floor_le (show 0 ≤ 2 * R / L q by positivity)
      calc ((⌊2 * R / L q⌋₊ : ℕ) : ℝ) * L q ≤ 2 * R / L q * L q := by gcongr
        _ = 2 * R := by field_simp
    refine ⟨UP, UN, hd, hμP, hμN, fun n hn => ?_, by rw [hcP, sum_singleton],
      by rw [hcN, sum_singleton], fun δ hδ0 hδ1 => ?_⟩
    · obtain ⟨h1, h2, q', hq', hsh⟩ := hpos n hn
      rw [mem_singleton] at hq'
      subst hq'
      exact ⟨h1, h2, hsh⟩
    · refine (hnorm δ hδ0 hδ1).trans ?_
      rw [sum_singleton]
      exact threeWindow_block_arith hR1 hL0.le hJL
  choose! UP UN hdisj hμP hμN hpos hcP hcN hnorm using hex
  set U : ℕ → Finset ℕ := fun q => UP q ∪ UN q with hU
  have hpair : (↑Q : Set ℕ).PairwiseDisjoint U := by
    intro q hq q' hq' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    exact hne (cofactor_eq_of_shape (hQmem q hq).2.2.1 (hQmem q' hq').2.2.1
      (hpos q hq n hn).2.2 (hpos q' hq' n hn').2.2)
  have hfilt : ∀ q ∈ Q, ((U q).filter Even).card = ⌊2 * R / L q⌋₊ * cofactorSupply R q ∧
      ((U q).filter fun n => ¬ Even n).card = ⌊2 * R / L q⌋₊ * cofactorSupply R q := fun q hq =>
    card_filter_even_single (hQmem q hq).2.2.1 (hQmem q hq).2.2.2 (hμP q hq) (hμN q hq)
      (fun n hn => (hpos q hq n hn).2.2) (hcP q hq) (hcN q hq)
  set A : Finset ℕ := (Q.biUnion U).filter Even with hA
  set B : Finset ℕ := (Q.biUnion U).filter fun n => ¬ Even n with hB
  have hAB : A ∪ B = Q.biUnion U := filter_union_filter_not_eq _ _
  have hcardA : A.card = ∑ q ∈ Q, ⌊2 * R / L q⌋₊ * cofactorSupply R q := by
    rw [hA, filter_biUnion, card_biUnion (hpair.mono fun q => filter_subset _ _)]
    exact sum_congr rfl fun q hq => (hfilt q hq).1
  have hcardB : B.card = ∑ q ∈ Q, ⌊2 * R / L q⌋₊ * cofactorSupply R q := by
    rw [hB, filter_biUnion, card_biUnion (hpair.mono fun q => filter_subset _ _)]
    exact sum_congr rfl fun q hq => (hfilt q hq).2
  refine ⟨A, B, disjoint_filter_filter_not _ _ _, fun a ha => (mem_filter.mp ha).2,
    fun b hb => (mem_filter.mp hb).2, fun a ha => ?_, fun b hb => ?_,
    by rw [hcardA, hcardB], ?_, fun δ hδ0 hδ1 => ?_⟩
  · -- the even atoms
    rw [hA, mem_filter] at ha
    obtain ⟨ha, hev⟩ := ha
    obtain ⟨q, hq, haq⟩ := mem_biUnion.mp ha
    obtain ⟨h1, h2, hsh⟩ := hpos q hq a haq
    obtain ⟨hq1, -, hqodd, hqsq⟩ := hQmem q hq
    have hμ := (moebius_of_shape hqodd hsh).1 hev
    obtain ⟨r, hr, hr2, hRr, -, hform⟩ := hsh
    rcases hform with hform | ⟨hform, -⟩
    · exact ⟨h1, h2, q, r, hqodd, hqsq, (mem_Icc.mp (hQsub hq)).2, hr, hRr, hform, hμ⟩
    · exfalso
      rw [hform] at hev
      exact (Nat.not_even_iff_odd.mpr (hqodd.mul (hr.odd_of_ne_two (by omega)))) hev
  · -- the odd atoms
    rw [hB, mem_filter] at hb
    obtain ⟨hb, hodd⟩ := hb
    obtain ⟨q, hq, hbq⟩ := mem_biUnion.mp hb
    obtain ⟨h1, h2, hsh⟩ := hpos q hq b hbq
    obtain ⟨hq1, -, hqodd, hqsq⟩ := hQmem q hq
    have hμ := (moebius_of_shape hqodd hsh).2 hodd
    obtain ⟨r, hr, hr2, hRr, -, hform⟩ := hsh
    rcases hform with hform | ⟨hform, h2Rr⟩
    · exfalso
      exact hodd (by rw [hform]; exact ⟨q * r, by ring⟩)
    · exact ⟨h1, h2, q, r, hqodd, hqsq, (mem_Icc.mp (hQsub hq)).2, hr, h2Rr, hform, hμ⟩
  · -- the count
    rw [hcardA]
    push_cast
    have hQsum := sum_inv_odd_squarefree_ge hY1
    rw [← hQdef] at hQsum
    have hlogY := log_floor_rpow_ge hR1 (show (0 : ℝ) ≤ 2 / 5 by norm_num)
    rw [← hYdef] at hlogY
    have hper : ∀ q ∈ Q, ε * R / (2 ^ 19 * Real.log R) * (1 / (q : ℝ)) ≤
        (⌊2 * R / L q⌋₊ : ℝ) * (cofactorSupply R q : ℝ) := fun q hq =>
      threeWindow_count hR5 hε0 (hQmem q hq).1 (hQmem q hq).2.1 hLR hlogm
    have hsum : ε * R / (2 ^ 19 * Real.log R) * ∑ q ∈ Q, 1 / (q : ℝ) ≤
        ∑ q ∈ Q, (⌊2 * R / L q⌋₊ : ℝ) * (cofactorSupply R q : ℝ) := by
      rw [mul_sum]; exact sum_le_sum hper
    refine le_trans ?_ hsum
    have hc0 : 0 ≤ ε * R / (2 ^ 19 * Real.log R) := by positivity
    have hharm : Real.log R / 40 ≤ ∑ q ∈ Q, 1 / (q : ℝ) := by
      refine le_trans ?_ hQsum
      have : 2 / 5 * Real.log R - Real.log 2 ≤ Real.log (Y : ℝ) := hlogY
      linarith
    calc ε / (40 * 2 ^ 19) * R = ε * R / (2 ^ 19 * Real.log R) * (Real.log R / 40) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hharm hc0
  · -- the norm
    have hδ : 0 < 5 + δ := by linarith
    have hfun : (fun t => ∑ n ∈ A ∪ B, ((μ n : ℤ) : ℝ) * atom n t) =
        fun t => ∑ q ∈ Q, ∑ n ∈ U q, ((μ n : ℤ) : ℝ) * atom n t := by
      funext t
      rw [hAB, sum_biUnion hpair]
    rw [hfun]
    have hfin : ∀ q ∈ Q, GammaFinite δ (fun t => ∑ n ∈ U q, ((μ n : ℤ) : ℝ) * atom n t) := by
      intro q hq
      refine gammaFinite_atomSum hδ _ _ fun n hn => ?_
      have := (hpos q hq n hn).1
      have : (1 : ℝ) ≤ n := by linarith
      exact_mod_cast this
    refine (gammaNorm_sum_le hδ _ hfin).trans ?_
    refine (sum_le_sum fun q hq => hnorm q hq δ hδ0 hδ1).trans ?_
    rw [sum_add_distrib, sum_add_distrib]
    have p1 := threeWindow_part_one (δ := δ) hR1 hQsub hYR
    have p2 := threeWindow_part_two (δ := δ) hR1 hε0 hQsub hYR
    have p3 := threeWindow_part_three (δ := δ) hR5 hε0 hY1 hQsub hYR (cofactorSupply R)
      (fun q hq => Nat.floor_le (by
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (hQmem q hq).1
        have := Real.rpow_nonneg (div_nonneg hR0.le hq0.le) supplyExp
        positivity))
    have a1 : 0 ≤ R ^ (-(1 / 10 : ℝ) - δ / 2) := Real.rpow_nonneg hR0.le _
    have a2 : 0 ≤ R ^ (-(137 / 500 : ℝ) - δ / 2) := Real.rpow_nonneg hR0.le _
    have a3 : 0 ≤ R ^ (-(11 / 500 : ℝ) - δ / 2) / Real.log R := by
      have := Real.rpow_nonneg hR0.le (-(11 / 500 : ℝ) - δ / 2); positivity
    have c2 : 0 ≤ 8 * jetConst 2 / ε := by positivity
    have c3 : 0 ≤ jetConst 3 / (256 * ε ^ 2) := by positivity
    calc _ ≤ 4 * jetConst 1 * R ^ (-(1 / 10 : ℝ) - δ / 2) +
          8 * jetConst 2 / ε * R ^ (-(137 / 500 : ℝ) - δ / 2) +
          jetConst 3 / (256 * ε ^ 2) * (R ^ (-(11 / 500 : ℝ) - δ / 2) / Real.log R) := by
          gcongr
      _ ≤ _ := by nlinarith


/-- The representation `n = qr` of (1) is unique: `q ≤ R^{2/5} < R^{3/5} ≤ R/q < r`. -/
theorem threeWindow_form_unique {R : ℝ} (hR : 1 < R) {q q' r r' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hqY : (q : ℝ) ≤ R ^ ((2 : ℝ) / 5)) (hq'Y : (q' : ℝ) ≤ R ^ ((2 : ℝ) / 5))
    (hr : r.Prime) (hr' : r'.Prime) (hRr : R / q < r) (hRr' : R / q' < r')
    (h : q * r = q' * r') : q = q' ∧ r = r' := by
  have hsmall : ∀ {c s : ℕ}, 1 ≤ c → (c : ℝ) ≤ R ^ ((2 : ℝ) / 5) → R / c < s →
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ c → ℓ < s := by
    intro c s hc hcY hs ℓ hℓ hℓc
    have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
    have hℓle : (ℓ : ℝ) ≤ c := by exact_mod_cast Nat.le_of_dvd hc hℓc
    have h35 := (threeWindow_scale hR.le hc hcY).1
    have h23 : R ^ ((2 : ℝ) / 5) < R ^ ((3 : ℝ) / 5) :=
      Real.rpow_lt_rpow_of_exponent_lt hR (by norm_num)
    have : (ℓ : ℝ) < s := by linarith
    exact_mod_cast this
  exact cofactor_eq_of_largest_prime hr hr' (hsmall hq hqY hRr) (hsmall hq' hq'Y hRr') h

/-- **Dyadic three-window packets and the cofinal reduction.**  The packets of (1) at `R = 2^j`
occupy disjoint dyadic shells, keep balanced parities with at least `c 2^j` atoms of each, and
have norms with a summable majorant uniform in `0 ≤ δ ≤ 1`; removing them from `S_{2^{J+2}}` is a
bounded perturbation. -/
theorem threeWindow_cofinal_reduction :
    ∃ c : ℝ, 0 < c ∧ ∃ U : ℕ → Finset ℕ,
      (∀ j, ∀ n ∈ U j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2)) ∧
      (∀ j, ((U j).filter Even).card = ((U j).filter fun n => ¬ Even n).card) ∧
      (∀ᶠ j in atTop, c * 2 ^ j ≤ ((U j).filter Even).card) ∧
      (∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        ((∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (mobiusCubicSource (2 ^ (J + 2))) ≤ B) ↔
          ∃ B : ℝ, ∀ J : ℕ, gammaNorm δ (fun t => mobiusCubicSource (2 ^ (J + 2)) t -
            ∑ j ∈ range (J + 1), ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ B) := by
  obtain ⟨c, C, R₀, hc, hC, hR₀, hpk⟩ := exists_threeWindow_extraction
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, R₀ ≤ (2 : ℝ) ^ j₀ :=
    pow_unbounded_of_one_lt R₀ (by norm_num) |>.imp fun _ h => h.le
  have hex : ∀ j : ℕ, ∃ U : Finset ℕ,
      (j₀ ≤ j → (∀ n ∈ U, 2 * (2 : ℝ) ^ j < n ∧ (n : ℝ) < 4 * 2 ^ j) ∧
        (U.filter Even).card = (U.filter fun n => ¬ Even n).card ∧
        c * 2 ^ j ≤ (U.filter Even).card ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ U, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (((2 : ℝ) ^ j) ^ (-(1 / 10 : ℝ) - δ / 2) +
              ((2 : ℝ) ^ j) ^ (-(137 / 500 : ℝ) - δ / 2) +
              ((2 : ℝ) ^ j) ^ (-(11 / 500 : ℝ) - δ / 2) / Real.log (2 ^ j))) ∧
      (j < j₀ → U = ∅) := by
    intro j
    by_cases hj : j₀ ≤ j
    · have hR : R₀ ≤ (2 : ℝ) ^ j := hj₀.trans (pow_le_pow_right₀ (by norm_num) hj)
      obtain ⟨A, B, hAB, hAe, hBo, hA, hB, hcard, hcount, hnorm⟩ := hpk _ hR
      have hfe : (A ∪ B).filter Even = A := by
        rw [filter_union, filter_true_of_mem hAe, filter_false_of_mem hBo, union_empty]
      have hfo : (A ∪ B).filter (fun n => ¬ Even n) = B := by
        rw [filter_union, filter_false_of_mem (fun a ha h => h (hAe a ha)),
          filter_true_of_mem hBo, empty_union]
      refine ⟨A ∪ B, fun _ => ⟨fun n hn => ?_, by rw [hfe, hfo, hcard], by rw [hfe]; exact hcount,
        hnorm⟩, fun h => absurd hj (by omega)⟩
      rcases mem_union.mp hn with hn | hn
      · exact ⟨(hA n hn).1, (hA n hn).2.1⟩
      · exact ⟨(hB n hn).1, (hB n hn).2.1⟩
    · exact ⟨∅, fun h => absurd h hj, fun _ => rfl⟩
  choose U hU hU0 using hex
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set b : ℕ → ℝ := fun j => C * (((2 : ℝ) ^ (-(1 / 10 : ℝ))) ^ j +
    ((2 : ℝ) ^ (-(137 / 500 : ℝ))) ^ j + ((2 : ℝ) ^ (-(11 / 500 : ℝ))) ^ j / Real.log 2) with hbdef
  have hgeo : ∀ x : ℝ, 0 < x → Summable (fun j : ℕ => ((2 : ℝ) ^ (-x)) ^ j) := fun x hx =>
    summable_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hb : Summable b :=
    ((((hgeo _ (by norm_num)).add (hgeo _ (by norm_num))).add
      ((hgeo _ (by norm_num)).div_const _))).mul_left C
  have hpow : ∀ (j : ℕ) (x : ℝ), ((2 : ℝ) ^ j) ^ (-x) = ((2 : ℝ) ^ (-x)) ^ j := fun j x =>
    two_pow_rpow_neg j x
  have hsupp : ∀ j, ∀ n ∈ U j, 2 ^ (j + 1) < n ∧ n < 2 ^ (j + 2) := by
    intro j n hn
    by_cases hj : j₀ ≤ j
    · obtain ⟨h1, h2⟩ := (hU j hj).1 n hn
      have e1 : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by push_cast; ring
      have e2 : ((2 ^ (j + 2) : ℕ) : ℝ) = 4 * (2 : ℝ) ^ j := by push_cast; ring
      constructor
      · have : ((2 ^ (j + 1) : ℕ) : ℝ) < (n : ℝ) := by rw [e1]; exact h1
        exact_mod_cast this
      · have : (n : ℝ) < ((2 ^ (j + 2) : ℕ) : ℝ) := by rw [e2]; exact h2
        exact_mod_cast this
    · simp [hU0 j (by omega)] at hn
  have hnorm : ∀ j, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      gammaNorm δ (fun t => ∑ n ∈ U j, ((μ n : ℤ) : ℝ) * atom n t) ≤ b j := by
    intro j δ hδ0 hδ1
    by_cases hj : j₀ ≤ j
    · refine ((hU j hj).2.2.2 δ hδ0 hδ1).trans ?_
      have hj1 : 1 ≤ j := by
        by_contra h
        have hj0 : j = 0 := by omega
        subst hj0
        have : R₀ ≤ 1 := by simpa using hj₀.trans (pow_le_pow_right₀ (by norm_num) hj)
        linarith
      have hlogj : Real.log 2 ≤ Real.log (2 ^ j) := by
        rw [Real.log_pow]
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        nlinarith
      have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hp : ∀ x y : ℝ, y ≤ x → ((2 : ℝ) ^ j) ^ (-x - δ / 2) ≤ ((2 : ℝ) ^ (-y)) ^ j := by
        intro x y hxy
        rw [← hpow]
        exact Real.rpow_le_rpow_of_exponent_le h2j (by linarith)
      have hq0 : 0 ≤ ((2 : ℝ) ^ j) ^ (-(11 / 500 : ℝ) - δ / 2) := Real.rpow_nonneg (by positivity) _
      have hdiv : ((2 : ℝ) ^ j) ^ (-(11 / 500 : ℝ) - δ / 2) / Real.log (2 ^ j) ≤
          ((2 : ℝ) ^ (-(11 / 500 : ℝ))) ^ j / Real.log 2 :=
        (div_le_div_of_nonneg_left hq0 hlog2 hlogj).trans (by gcongr; exact hp _ _ le_rfl)
      simp only [hbdef]
      gcongr
      · exact hp _ _ le_rfl
      · exact hp _ _ le_rfl
    · simp only [hU0 j (by omega), Finset.sum_empty]
      have : gammaNorm δ (fun _ : ℝ => (0 : ℝ)) = 0 := by
        simp [gammaNorm, gammaEnergy, gammaInner]
      rw [this]
      simp only [hbdef]
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(1 / 10 : ℝ))
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(137 / 500 : ℝ))
      have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(11 / 500 : ℝ))
      positivity
  refine ⟨c, hc, U, hsupp, fun j => ?_, ?_, ⟨b, hb, hnorm⟩, fun δ hδ0 hδ1 => ?_⟩
  · by_cases hj : j₀ ≤ j
    · exact (hU j hj).2.1
    · simp [hU0 j (by omega)]
  · filter_upwards [eventually_ge_atTop j₀] with j hj
    exact (hU j hj).2.2.1
  · exact (cofinal_packet_reduction U b hb hsupp hδ0 fun j => hnorm j δ hδ0 hδ1).2

end RHTower.CubicGamma
