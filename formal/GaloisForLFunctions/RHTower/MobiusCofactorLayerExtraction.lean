import GaloisForLFunctions.RHTower.MobiusThreeWindowExtraction

/-!
# Global rounding across dyadic cofactor layers

Fix `d ≥ 1` and `0 < η < 1` with `(d+1)(1-α)(1-η) > 1/2`, `α = 71/100`.  Group the admissible
cofactors `q ≤ R^η` into dyadic layers `2^k ≤ q < 2^{k+1}`.  One layer uses the common block
length `L_k = 4 (2^{k+1})^{1-α} R^α / ε ≥ H_q/ε`, pools all of its cofactors in each block, and
rounds each actual Möbius sign once, so both signs have exactly `M_k = Σ_q m_q` atoms per block
and centered moments of orders `1, …, d` within `2 L_k^j`.  With `M_k ≤ ε L_k/(131072 log R)` the
order-`(d+1)` Taylor bound of a layer is

`≪_d R^{-1/2-δ/2} + (L_k/R)^{d+1} R^{1/2-δ/2}/log R ≪_d R^{-1/2-δ/2} + R^{1/2-(d+1)(1-α)(1-η)-δ/2}/log R`,

and there are `O(log R)` layers:

`‖P_R‖_δ ≪_{d,η} R^{-1/2-δ/2} log R + R^{1/2-(d+1)(1-α)(1-η)-δ/2}`.   (7)

All odd squarefree `q ≤ R^β`, `β = min(η, 1/2)/2`, are admissible, and `J_k m_q ≫ R/(q log R)`;
the odd-squarefree harmonic bound makes each sign count `≫_{d,η} R`.  For every `η < 1` a large
fixed `d` satisfies the exponent condition; for `d = 3` it is `η < 33/58`.
-/

open Finset Filter Topology

noncomputable section

namespace RHTower.CubicGamma

open RHTower.MomentSelector
open scoped ArithmeticFunction.Moebius

/-- The order-`(d+1)` family bound over `J` blocks with `J L ≤ 2R`, `L ≤ R`. -/
theorem family_bound_arith {d : ℕ} {R δ L : ℝ} (hR : 1 ≤ R) (hL : 0 ≤ L) (hLR : L ≤ R) {J : ℕ}
    (hJL : (J : ℝ) * L ≤ 2 * R) (M : ℕ) :
    (J : ℝ) * (∑ i ∈ range d, 2 * L ^ (i + 1) / ((i + 1).factorial : ℝ) *
        (jetConst (i + 1) * R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (i + 1)) +
      ((2 * M : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ) *
        (jetConst (d + 1) * (4 * R ^ 2) * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (d + 1)))) ≤
      (∑ i ∈ range d, 4 * jetConst (i + 1)) * (R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹) +
        16 * jetConst (d + 1) * ((M : ℝ) * L ^ d * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (d + 1)) := by
  have hR0 : 0 < R := by linarith
  set E := (R ^ ((5 + δ) / 2))⁻¹ with hE
  have hE0 : 0 ≤ E := (inv_pos.mpr (Real.rpow_pos_of_pos hR0 _)).le
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rw [mul_add, mul_sum, sum_mul]
  apply add_le_add
  · apply sum_le_sum
    intro i _
    have hjc := jetConst_nonneg (i + 1)
    have hf : (1 : ℝ) ≤ ((i + 1).factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos _)
    have hRi : 0 < R ^ (i + 1) := by positivity
    have hLi : L ^ i ≤ R ^ i := pow_le_pow_left₀ hL hLR i
    have e : (J : ℝ) * (2 * L ^ (i + 1) / ((i + 1).factorial : ℝ) *
        (jetConst (i + 1) * R ^ 2 * E / R ^ (i + 1))) =
        2 * jetConst (i + 1) * ((J * L) * L ^ i) * (R ^ 2 * E) /
          (((i + 1).factorial : ℝ) * R ^ (i + 1)) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : (J * L) * L ^ i ≤ (2 * R) * R ^ i :=
      mul_le_mul hJL hLi (pow_nonneg hL i) (by positivity)
    have hR2E : 0 ≤ R ^ 2 * E := by positivity
    calc 2 * jetConst (i + 1) * ((J * L) * L ^ i) * (R ^ 2 * E)
        ≤ 2 * jetConst (i + 1) * ((2 * R) * R ^ i) * (R ^ 2 * E) := by gcongr
      _ = 4 * jetConst (i + 1) * (R ^ 2 * E) * (1 * R ^ (i + 1)) := by ring
      _ ≤ 4 * jetConst (i + 1) * (R ^ 2 * E) * (((i + 1).factorial : ℝ) * R ^ (i + 1)) := by
          gcongr
  · have hjc := jetConst_nonneg (d + 1)
    have hf : (1 : ℝ) ≤ ((d + 1).factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos _)
    have e : (J : ℝ) * (((2 * M : ℕ) : ℝ) * (L ^ (d + 1) / ((d + 1).factorial : ℝ) *
        (jetConst (d + 1) * (4 * R ^ 2) * E / R ^ (d + 1)))) =
        8 * jetConst (d + 1) * (J * L) * ((M : ℝ) * L ^ d * R ^ 2 * E / R ^ (d + 1)) /
          ((d + 1).factorial : ℝ) := by
      push_cast; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have hX : 0 ≤ (M : ℝ) * L ^ d * R ^ 2 * E / R ^ (d + 1) := by positivity
    calc 8 * jetConst (d + 1) * (J * L) * ((M : ℝ) * L ^ d * R ^ 2 * E / R ^ (d + 1))
        ≤ 8 * jetConst (d + 1) * (2 * R) * ((M : ℝ) * L ^ d * R ^ 2 * E / R ^ (d + 1)) := by
          gcongr
      _ = 16 * jetConst (d + 1) * ((M : ℝ) * L ^ d * R ^ 3 * E / R ^ (d + 1)) * 1 := by ring
      _ ≤ _ := by gcongr


/-! ### One dyadic layer -/

/-- The common block length of the layer `2^k ≤ q < 2^{k+1}`. -/
def layerLength (ε R : ℝ) (k : ℕ) : ℝ :=
  4 * ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) * R ^ supplyExp / ε

theorem layerLength_pos {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (k : ℕ) : 0 < layerLength ε R k := by
  unfold layerLength
  have := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 ^ (k + 1)) (1 - supplyExp)
  have := Real.rpow_pos_of_pos hR supplyExp
  positivity

/-- `H_q ≤ ε L_k` for `1 ≤ q < 2^{k+1}`. -/
theorem layer_H_le {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) {k q : ℕ} (hq : 1 ≤ q)
    (hqk : q < 2 ^ (k + 1)) :
    (q : ℝ) * (4 * R / q) ^ supplyExp ≤ ε * layerLength ε R k := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [cofactor_H_eq hq hR.le]
  have e : (q : ℝ) * (R / q) ^ supplyExp = (q : ℝ) ^ (1 - supplyExp) * R ^ supplyExp := by
    rw [Real.div_rpow hR.le hq0.le, Real.rpow_sub hq0, Real.rpow_one]; field_simp
  rw [e]
  unfold layerLength
  rw [mul_div_cancel₀ _ hε.ne']
  have h1 : (q : ℝ) ^ (1 - supplyExp) ≤ ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) :=
    Real.rpow_le_rpow hq0.le (by exact_mod_cast hqk.le) (by norm_num [supplyExp])
  have h4 := four_rpow_supplyExp_le
  have hRα : 0 ≤ R ^ supplyExp := Real.rpow_nonneg hR.le _
  have hqα : 0 ≤ (q : ℝ) ^ (1 - supplyExp) := Real.rpow_nonneg hq0.le _
  calc (4 : ℝ) ^ supplyExp * ((q : ℝ) ^ (1 - supplyExp) * R ^ supplyExp)
      ≤ 4 * (((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) * R ^ supplyExp) := by gcongr
    _ = _ := by ring

/-- `L_k/R ≤ (8/ε) R^{-(1-α)(1-η)}` for `2^k ≤ R^η`. -/
theorem layerLength_div_le {ε R η : ℝ} (hε : 0 < ε) (hR : 1 ≤ R) {k : ℕ}
    (hk : (2 : ℝ) ^ k ≤ R ^ η) :
    layerLength ε R k / R ≤ 8 / ε * R ^ (-((1 - supplyExp) * (1 - η))) := by
  have hR0 : 0 < R := by linarith
  have h2k : ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) ≤ 2 * R ^ (η * (1 - supplyExp)) := by
    rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num)]
    have h1 : ((2 : ℝ) ^ k) ^ (1 - supplyExp) ≤ (R ^ η) ^ (1 - supplyExp) :=
      Real.rpow_le_rpow (by positivity) hk (by norm_num [supplyExp])
    have h2 : (2 : ℝ) ^ (1 - supplyExp) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - supplyExp) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [supplyExp])
        _ = 2 := Real.rpow_one 2
    rw [← Real.rpow_mul hR0.le] at h1
    have h0 : 0 ≤ ((2 : ℝ) ^ k) ^ (1 - supplyExp) := Real.rpow_nonneg (by positivity) _
    calc ((2 : ℝ) ^ k) ^ (1 - supplyExp) * (2 : ℝ) ^ (1 - supplyExp)
        ≤ R ^ (η * (1 - supplyExp)) * 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
  have hid : R ^ (η * (1 - supplyExp)) * R ^ supplyExp / R =
      R ^ (-((1 - supplyExp) * (1 - η))) := by
    rw [← Real.rpow_add hR0, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hR0]
    congr 1; ring
  unfold layerLength
  have hRα : 0 ≤ R ^ supplyExp := Real.rpow_nonneg hR0.le _
  calc 4 * ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) * R ^ supplyExp / ε / R
      ≤ 4 * (2 * R ^ (η * (1 - supplyExp))) * R ^ supplyExp / ε / R := by gcongr
    _ = 8 / ε * (R ^ (η * (1 - supplyExp)) * R ^ supplyExp / R) := by ring
    _ = _ := by rw [hid]

/-- The layer supply: `Σ_{q ∈ F} m_q ≤ ε L_k/(131072 log R)` for `F ⊆ [2^k, 2^{k+1})`. -/
theorem layer_supply_le {ε R : ℝ} (hε : 0 < ε) (hR : 5 ≤ R) {k : ℕ} {F : Finset ℕ}
    (hF : ∀ q ∈ F, 2 ^ k ≤ q ∧ q < 2 ^ (k + 1)) :
    ((∑ q ∈ F, cofactorSupply R q : ℕ) : ℝ) ≤ ε * layerLength ε R k / (131072 * Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog5 : Real.log R ≤ Real.log (5 * R) := Real.log_le_log hR0 (by linarith)
  have hlog5' : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hterm : ∀ q ∈ F, (cofactorSupply R q : ℝ) ≤ (R / 2 ^ k) ^ supplyExp / (32768 * Real.log R) := by
    intro q hq
    have hq0 : (0 : ℝ) < q := by
      have := (hF q hq).1
      exact_mod_cast (Nat.pos_of_ne_zero (by positivity : (2 : ℕ) ^ k ≠ 0)).trans_le this
    have hRq := Real.rpow_nonneg (div_nonneg hR0.le hq0.le) supplyExp
    unfold cofactorSupply
    refine (Nat.floor_le (by positivity)).trans ?_
    have hqk : (2 : ℝ) ^ k ≤ q := by exact_mod_cast (hF q hq).1
    have h1 : (R / q) ^ supplyExp ≤ (R / 2 ^ k) ^ supplyExp :=
      Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hR0.le h2k hqk)
        (by norm_num [supplyExp])
    calc (R / q) ^ supplyExp / (32768 * Real.log (5 * R))
        ≤ (R / 2 ^ k) ^ supplyExp / (32768 * Real.log (5 * R)) := by gcongr
      _ ≤ _ := by gcongr
  have hcard : (F.card : ℝ) ≤ 2 ^ k := by
    have hsub : F ⊆ Ico (2 ^ k) (2 ^ (k + 1)) := fun q hq =>
      mem_Ico.mpr ⟨(hF q hq).1, (hF q hq).2⟩
    have := card_le_card hsub
    rw [Nat.card_Ico, pow_succ] at this
    have : F.card ≤ 2 ^ k := by omega
    exact_mod_cast this
  have hkey : (2 : ℝ) ^ k * (R / 2 ^ k) ^ supplyExp ≤ ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) *
      R ^ supplyExp := by
    rw [Real.div_rpow hR0.le h2k.le]
    have e : (2 : ℝ) ^ k * (R ^ supplyExp / ((2 : ℝ) ^ k) ^ supplyExp) =
        ((2 : ℝ) ^ k) ^ (1 - supplyExp) * R ^ supplyExp := by
      rw [Real.rpow_sub h2k, Real.rpow_one]; field_simp
    rw [e]
    have hk1 : ((2 : ℝ) ^ k) ^ (1 - supplyExp) ≤ ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) :=
      Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
        (by norm_num [supplyExp])
    exact mul_le_mul_of_nonneg_right hk1 (Real.rpow_nonneg hR0.le _)
  push_cast
  have hRk := Real.rpow_nonneg (div_nonneg hR0.le h2k.le) supplyExp
  calc ∑ q ∈ F, (cofactorSupply R q : ℝ) ≤ ∑ _q ∈ F, (R / 2 ^ k) ^ supplyExp /
        (32768 * Real.log R) := sum_le_sum hterm
    _ = F.card * ((R / 2 ^ k) ^ supplyExp / (32768 * Real.log R)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ k * ((R / 2 ^ k) ^ supplyExp / (32768 * Real.log R)) := by gcongr
    _ = (2 : ℝ) ^ k * (R / 2 ^ k) ^ supplyExp / (32768 * Real.log R) := by ring
    _ ≤ ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) * R ^ supplyExp / (32768 * Real.log R) := by gcongr
    _ = ε * layerLength ε R k / (131072 * Real.log R) := by
        unfold layerLength; field_simp; ring

/-- The selected count of one cofactor in its layer: `J_k m_q ≥ ε R/(2^{20} q log R)`. -/
theorem layer_count_ge {ε R : ℝ} (hε : 0 < ε) (hR : 5 ≤ R) {k q : ℕ} (hq : 1 ≤ q)
    (hkq : 2 ^ k ≤ q) (hLR : layerLength ε R k ≤ R)
    (hsupp : 131072 * Real.log R ≤ (R / q) ^ supplyExp) :
    ε * R / (2 ^ 20 * Real.log R) * (1 / (q : ℝ)) ≤
      (⌊2 * R / layerLength ε R k⌋₊ : ℝ) * (cofactorSupply R q : ℝ) := by
  have hR0 : 0 < R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  have hlog5 : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
  have hlog52 : Real.log (5 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) hR0.ne']
    have : Real.log 5 ≤ Real.log R := Real.log_le_log (by norm_num) hR
    linarith
  set L := layerLength ε R k with hLdef
  have hL0 : 0 < L := layerLength_pos hε hR0 k
  have hJ : R / L ≤ (⌊2 * R / L⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (2 * R / L)
    have hRL : 1 ≤ R / L := by rw [le_div_iff₀ hL0]; linarith
    have : 2 * R / L = 2 * (R / L) := by ring
    linarith
  set x := (R / q) ^ supplyExp / (32768 * Real.log (5 * R)) with hx
  have hx2 : 2 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]
    nlinarith
  have hm : x / 2 ≤ (cofactorSupply R q : ℝ) := by
    have h := Nat.lt_floor_add_one x
    unfold cofactorSupply
    rw [← hx]
    linarith
  -- `(R/q)^α / L ≥ ε/(8q)`
  have hRq := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < R / q) supplyExp
  have hratio : ε / (8 * q) ≤ (R / q) ^ supplyExp / L := by
    rw [hLdef]
    unfold layerLength
    rw [Real.div_rpow hR0.le hq0.le]
    have h2 : ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) ≤ (2 * q) ^ (1 - supplyExp) :=
      Real.rpow_le_rpow (by positivity) (by
        have : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ 2 * q := by
          have : 2 ^ (k + 1) ≤ 2 * q := by rw [pow_succ]; omega
          exact_mod_cast this
        simpa using this) (by norm_num [supplyExp])
    have h3 : (2 * (q : ℝ)) ^ (1 - supplyExp) = 2 ^ (1 - supplyExp) * (q : ℝ) ^ (1 - supplyExp) :=
      Real.mul_rpow (by norm_num) hq0.le
    have h4 : (2 : ℝ) ^ (1 - supplyExp) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - supplyExp) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [supplyExp])
        _ = 2 := Real.rpow_one 2
    have h5 : (q : ℝ) ^ (1 - supplyExp) * (q : ℝ) ^ supplyExp = q := by
      rw [← Real.rpow_add hq0]; norm_num
    have hRα := Real.rpow_pos_of_pos hR0 supplyExp
    have hqα := Real.rpow_pos_of_pos hq0 supplyExp
    have hq1α := Real.rpow_pos_of_pos hq0 (1 - supplyExp)
    have h2kα : 0 < ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) := Real.rpow_pos_of_pos (by positivity) _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ε * (4 * ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) * R ^ supplyExp / ε)
        = 4 * ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) * R ^ supplyExp := by field_simp
      _ ≤ 4 * (2 * (q : ℝ) ^ (1 - supplyExp)) * R ^ supplyExp := by
          gcongr
          calc ((2 : ℝ) ^ (k + 1)) ^ (1 - supplyExp) ≤ (2 * q) ^ (1 - supplyExp) := h2
            _ = 2 ^ (1 - supplyExp) * (q : ℝ) ^ (1 - supplyExp) := h3
            _ ≤ 2 * (q : ℝ) ^ (1 - supplyExp) := by gcongr
      _ = R ^ supplyExp / (q : ℝ) ^ supplyExp * (8 * q) := by
          rw [Real.rpow_sub hq0, Real.rpow_one]; field_simp; ring
  calc ε * R / (2 ^ 20 * Real.log R) * (1 / (q : ℝ))
      = R * (ε / (8 * q)) / (2 * 65536 * Real.log R) := by field_simp; ring
    _ ≤ R * ((R / q) ^ supplyExp / L) / (65536 * Real.log (5 * R)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : R * (ε / (8 * q)) ≤ R * ((R / q) ^ supplyExp / L) :=
          mul_le_mul_of_nonneg_left hratio hR0.le
        have h2 : 65536 * Real.log (5 * R) ≤ 2 * 65536 * Real.log R := by linarith
        have h3 : 0 ≤ R * (ε / (8 * q)) := by positivity
        nlinarith
    _ = R / L * (x / 2) := by rw [hx]; field_simp; ring
    _ ≤ _ := mul_le_mul hJ hm (by positivity) (Nat.cast_nonneg _)


/-! ### The layered extraction (7) -/

theorem layer_mix_le {G A D x y : ℝ} (hG : 1 ≤ G) (hA : 0 ≤ A) (hD : 0 ≤ D) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : G * (A * x + D * y) ≤ (G * (A + D) + 1) * (x + y) := by
  have hG0 : 0 ≤ G := by linarith
  nlinarith [mul_nonneg (mul_nonneg hG0 hA) hy, mul_nonneg (mul_nonneg hG0 hD) hx]

/-- Large-`R` thresholds for the layered extraction. -/
theorem exists_layer_threshold (z₀ ε η β : ℝ) (hη : η < 1) :
    ∃ R₀ : ℝ, 5 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      max z₀ 2 ≤ R ^ (1 - η) ∧ 8 / ε ≤ R ^ ((1 - supplyExp) * (1 - η)) ∧
        131072 * Real.log R ≤ R ^ (supplyExp * (1 - η)) ∧
        2 * (Real.log 2 + 7) / β ≤ Real.log R ∧ 1 ≤ Real.log R := by
  have h1 : ∀ᶠ R : ℝ in atTop, max z₀ 2 ≤ R ^ (1 - η) :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _
  have h2 : ∀ᶠ R : ℝ in atTop, 8 / ε ≤ R ^ ((1 - supplyExp) * (1 - η)) :=
    (tendsto_rpow_atTop (mul_pos (by norm_num [supplyExp]) (by linarith))).eventually_ge_atTop _
  have h3 : ∀ᶠ R : ℝ in atTop, 131072 * Real.log R ≤ R ^ (supplyExp * (1 - η)) := by
    have ho := (isLittleO_log_rpow_atTop
      (show (0 : ℝ) < supplyExp * (1 - η) from mul_pos supplyExp_pos (by linarith))).def
      (c := 1 / 131072) (by norm_num)
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with R hR hR1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hR1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hR
    linarith
  have h4 : ∀ᶠ R : ℝ in atTop, 2 * (Real.log 2 + 7) / β ≤ Real.log R :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have h5 : ∀ᶠ R : ℝ in atTop, 1 ≤ Real.log R := Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((((h1.and h2).and h3).and h4).and h5)
  refine ⟨max 5 X, le_max_left _ _, fun R hR => ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩ := hX R (le_of_max_le_right hR)
  exact ⟨a, b, c, e, f⟩

/-- **Layered extraction (7).**  For `d ≥ 1` and `0 < η < 1`, for all large `R` there are disjoint
atom sets of Möbius signs `+1` and `-1`, of equal size at least `c R`, all of admissible shape
with cofactors `q ≤ R^η`, whose literal packet obeys, uniformly in `0 ≤ δ ≤ 1`,
`‖·‖_δ ≤ C [R^{-1/2-δ/2} log R + R^{1/2-(d+1)(1-α)(1-η)-δ/2}]`. -/
theorem exists_layer_extraction {d : ℕ} (hd : 1 ≤ d) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ c C R₀ : ℝ, 0 < c ∧ 0 < C ∧ 5 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ UP UN : Finset ℕ, Disjoint UP UN ∧ (∀ n ∈ UP, μ n = 1) ∧ (∀ n ∈ UN, μ n = -1) ∧
        (∀ n ∈ UP ∪ UN, 2 * R < n ∧ (n : ℝ) < 4 * R ∧
          ∃ q : ℕ, (q : ℝ) ≤ R ^ η ∧ AdmissibleCofactor R q ∧ AtomShape R q n) ∧
        UP.card = UN.card ∧ c * R ≤ UP.card ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ UP ∪ UN, ((μ n : ℤ) : ℝ) * atom n t) ≤
            C * (R ^ (-(1 / 2 : ℝ) - δ / 2) * Real.log R +
              R ^ (1 / 2 - (d + 1) * (1 - supplyExp) * (1 - η) - δ / 2)) := by
  classical
  obtain ⟨ε, hε0, z₀, hz₀, hfam⟩ := exists_family_packet hd
  set β : ℝ := min η (1 / 2) / 2 with hβdef
  have hβ0 : 0 < β := by positivity
  have hβη : β < η := by have := min_le_left η (1 / 2); linarith
  have hβh : β < 1 / 2 := by have := min_le_right η (1 / 2); linarith
  obtain ⟨R₀, hR₀, hthr⟩ := exists_layer_threshold z₀ ε η β hη1
  set A : ℝ := ∑ i ∈ range d, 4 * jetConst (i + 1) with hAdef
  set B : ℝ := 16 * jetConst (d + 1) with hBdef
  have hA0 : 0 ≤ A := sum_nonneg fun i _ => by have := jetConst_nonneg (i + 1); positivity
  have hB0 : 0 ≤ B := by have := jetConst_nonneg (d + 1); positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D : ℝ := B * ε / 131072 * (8 / ε) ^ (d + 1) with hDdef
  have hD0 : 0 ≤ D := by positivity
  set G : ℝ := η / Real.log 2 + 1 with hGdef
  have hG1 : 1 ≤ G := by have : 0 ≤ η / Real.log 2 := by positivity
                         linarith
  refine ⟨ε * β / (16 * 2 ^ 20), G * (A + D) + 1, R₀, by positivity, by positivity, hR₀,
    fun R hR => ?_⟩
  obtain ⟨hz, h8, hsup, hlogβ, hlog1⟩ := hthr R hR
  have hR5 : 5 ≤ R := hR₀.trans hR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hlogpos : 0 < Real.log R := by linarith
  set Y : ℕ := ⌊R ^ η⌋₊ with hYdef
  have hRη1 : 1 ≤ R ^ η := Real.one_le_rpow hR1 hη0.le
  have hY1 : 1 ≤ Y := Nat.le_floor (by exact_mod_cast hRη1)
  have hYR : (Y : ℝ) ≤ R ^ η := Nat.floor_le (by linarith)
  set K : ℕ := Nat.log 2 Y with hKdef
  set Fall : Finset ℕ := (Icc 1 Y).filter (AdmissibleCofactor R) with hFall
  set F : ℕ → Finset ℕ := fun k => Fall.filter fun q => Nat.log 2 q = k with hFdef
  have hFmem : ∀ k, ∀ q ∈ F k, AdmissibleCofactor R q ∧ 1 ≤ q ∧ q ≤ Y ∧ Nat.log 2 q = k := by
    intro k q hq
    simp only [hFdef, hFall, mem_filter, mem_Icc] at hq
    exact ⟨hq.1.2, hq.1.1.1, hq.1.1.2, hq.2⟩
  have hFband : ∀ k, ∀ q ∈ F k, 2 ^ k ≤ q ∧ q < 2 ^ (k + 1) := by
    intro k q hq
    obtain ⟨-, hq1, -, hk⟩ := hFmem k q hq
    subst hk
    exact ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) q⟩
  -- scale facts for `q ≤ Y`
  have hRq : ∀ q : ℕ, 1 ≤ q → q ≤ Y → R ^ (1 - η) ≤ R / q := by
    intro q hq hqY
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    rw [le_div_iff₀ hq0]
    calc R ^ (1 - η) * q ≤ R ^ (1 - η) * R ^ η :=
          mul_le_mul_of_nonneg_left ((by exact_mod_cast hqY : (q : ℝ) ≤ Y).trans hYR)
            (Real.rpow_nonneg hR0.le _)
      _ = R := by rw [← Real.rpow_add hR0]; simp
  have hk2 : ∀ k ∈ range (K + 1), (2 : ℝ) ^ k ≤ R ^ η := by
    intro k hk
    have hkK : k ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have h1 : 2 ^ k ≤ Y := (Nat.pow_le_pow_right (by norm_num) hkK).trans
      (Nat.pow_log_le_self 2 (by omega))
    exact (by exact_mod_cast h1 : (2 : ℝ) ^ k ≤ Y).trans hYR
  have hLk : ∀ k ∈ range (K + 1), layerLength ε R k ≤ R := by
    intro k hk
    have h := layerLength_div_le hε0 hR1 (hk2 k hk)
    have hx : 8 / ε * R ^ (-((1 - supplyExp) * (1 - η))) ≤ 1 := by
      rw [Real.rpow_neg hR0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hR0 _)]
      exact h8
    have := h.trans hx
    rwa [div_le_one hR0] at this
  -- one packet per layer
  have hlayer : ∀ k ∈ range (K + 1), ∃ UP UN : Finset ℕ, Disjoint UP UN ∧
      (∀ n ∈ UP, μ n = 1) ∧ (∀ n ∈ UN, μ n = -1) ∧
      (∀ n ∈ UP ∪ UN, 2 * R < n ∧ (n : ℝ) < 4 * R ∧ ∃ q ∈ F k, AtomShape R q n) ∧
      UP.card = ⌊2 * R / layerLength ε R k⌋₊ * ∑ q ∈ F k, cofactorSupply R q ∧
      UN.card = ⌊2 * R / layerLength ε R k⌋₊ * ∑ q ∈ F k, cofactorSupply R q ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ n ∈ UP ∪ UN, ((μ n : ℤ) : ℝ) * atom n t) ≤
          A * (R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹) +
            D * (R ^ (-((d + 1) * ((1 - supplyExp) * (1 - η)))) * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ /
              Real.log R) := by
    intro k hk
    have hL0 := layerLength_pos hε0 hR0 k
    have hF : ∀ q ∈ F k, AdmissibleCofactor R q ∧ 2 ≤ R / q ∧ z₀ ≤ R / q ∧
        (q : ℝ) * (4 * R / q) ^ supplyExp ≤ ε * layerLength ε R k := by
      intro q hq
      obtain ⟨hadm, hq1, hqY, -⟩ := hFmem k q hq
      have h1 := hRq q hq1 hqY
      exact ⟨hadm, (le_max_right _ _).trans (hz.trans h1), (le_max_left _ _).trans (hz.trans h1),
        layer_H_le hε0 hR0 hq1 (hFband k q hq).2⟩
    obtain ⟨UP, UN, hd, hμP, hμN, hpos, hcP, hcN, hnorm⟩ :=
      hfam R (layerLength ε R k) (F k) hR5 hL0 (hLk k hk) hF
    refine ⟨UP, UN, hd, hμP, hμN, hpos, hcP, hcN, fun δ hδ0 hδ1 => ?_⟩
    refine (hnorm δ hδ0 hδ1).trans ?_
    have hJL : ((⌊2 * R / layerLength ε R k⌋₊ : ℕ) : ℝ) * layerLength ε R k ≤ 2 * R := by
      have h := Nat.floor_le (show 0 ≤ 2 * R / layerLength ε R k by positivity)
      calc ((⌊2 * R / layerLength ε R k⌋₊ : ℕ) : ℝ) * layerLength ε R k
          ≤ 2 * R / layerLength ε R k * layerLength ε R k := by gcongr
        _ = 2 * R := by field_simp
    refine (family_bound_arith hR1 hL0.le (hLk k hk) hJL _).trans ?_
    apply add_le_add le_rfl
    -- the remainder of the layer
    have hM := layer_supply_le hε0 hR5 (hFband k)
    have hdiv := layerLength_div_le hε0 hR1 (hk2 k hk)
    set L := layerLength ε R k with hL
    set M := ((∑ q ∈ F k, cofactorSupply R q : ℕ) : ℝ) with hMdef
    have hE : 0 < (R ^ ((5 + δ) / 2))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hR0 _)
    have hLR : (L / R) ^ (d + 1) ≤ (8 / ε) ^ (d + 1) * R ^ (-((d + 1) * ((1 - supplyExp) * (1 - η)))) := by
      calc (L / R) ^ (d + 1) ≤ (8 / ε * R ^ (-((1 - supplyExp) * (1 - η)))) ^ (d + 1) :=
            pow_le_pow_left₀ (by positivity) hdiv _
        _ = (8 / ε) ^ (d + 1) * R ^ (-((d + 1) * ((1 - supplyExp) * (1 - η)))) := by
            rw [mul_pow, ← Real.rpow_natCast (R ^ _), ← Real.rpow_mul hR0.le]
            congr 2; push_cast; ring
    have hM0 : 0 ≤ M := Nat.cast_nonneg _
    have hRne : R ≠ 0 := hR0.ne'
    have hlogne : Real.log R ≠ 0 := hlogpos.ne'
    have hBM : B * M ≤ B * (ε * L / (131072 * Real.log R)) := mul_le_mul_of_nonneg_left hM hB0
    have hX : 0 ≤ L ^ d * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (d + 1) := by
      have := layerLength_pos hε0 hR0 k
      positivity
    have e2 : B * (ε * L / (131072 * Real.log R)) * (L ^ d * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ /
        R ^ (d + 1)) = B * ε / 131072 * (L / R) ^ (d + 1) * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ /
          Real.log R := by
      rw [div_pow, pow_succ L d]
      field_simp
    calc 16 * jetConst (d + 1) * (M * L ^ d * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (d + 1))
        = B * M * (L ^ d * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ / R ^ (d + 1)) := by rw [hBdef]; ring
      _ ≤ B * (ε * L / (131072 * Real.log R)) * (L ^ d * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ /
            R ^ (d + 1)) := mul_le_mul_of_nonneg_right hBM hX
      _ = B * ε / 131072 * (L / R) ^ (d + 1) * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ / Real.log R := e2
      _ ≤ B * ε / 131072 * ((8 / ε) ^ (d + 1) *
            R ^ (-((d + 1) * ((1 - supplyExp) * (1 - η))))) * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ /
            Real.log R := by gcongr
      _ = D * (R ^ (-((d + 1) * ((1 - supplyExp) * (1 - η)))) * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ /
            Real.log R) := by rw [hDdef]; ring
  choose! UPk UNk hd hμP hμN hpos hcP hcN hnorm using hlayer
  -- the layers are disjoint
  have hoddF : ∀ k, ∀ q ∈ F k, Odd q := fun k q hq => (hFmem k q hq).1.2.1
  have hsep : ∀ k ∈ range (K + 1), ∀ k' ∈ range (K + 1), ∀ n : ℕ,
      n ∈ UPk k ∪ UNk k → n ∈ UPk k' ∪ UNk k' → k = k' := by
    intro k hk k' hk' n hn hn'
    obtain ⟨-, -, q, hq, hsh⟩ := hpos k hk n hn
    obtain ⟨-, -, q', hq', hsh'⟩ := hpos k' hk' n hn'
    have hqq := cofactor_eq_of_shape (hoddF k q hq) (hoddF k' q' hq') hsh hsh'
    subst hqq
    exact (hFmem k q hq).2.2.2.symm.trans (hFmem k' q hq').2.2.2
  have hpairU : (↑(range (K + 1)) : Set ℕ).PairwiseDisjoint fun k => UPk k ∪ UNk k := by
    intro k hk k' hk' hne
    rw [Function.onFun, Finset.disjoint_left]
    exact fun n hn hn' => hne (hsep k hk k' hk' n hn hn')
  have hpairP : (↑(range (K + 1)) : Set ℕ).PairwiseDisjoint UPk :=
    hpairU.mono fun k => subset_union_left
  have hpairN : (↑(range (K + 1)) : Set ℕ).PairwiseDisjoint UNk :=
    hpairU.mono fun k => subset_union_right
  set UP : Finset ℕ := (range (K + 1)).biUnion UPk with hUP
  set UN : Finset ℕ := (range (K + 1)).biUnion UNk with hUN
  have hμUP : ∀ n ∈ UP, μ n = 1 := by
    intro n hn
    obtain ⟨k, hk, hn⟩ := mem_biUnion.mp hn
    exact hμP k hk n hn
  have hμUN : ∀ n ∈ UN, μ n = -1 := by
    intro n hn
    obtain ⟨k, hk, hn⟩ := mem_biUnion.mp hn
    exact hμN k hk n hn
  have hdisj : Disjoint UP UN := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    have := (hμUP n hn).symm.trans (hμUN n hn')
    norm_num at this
  have hcardP : UP.card = ∑ k ∈ range (K + 1),
      ⌊2 * R / layerLength ε R k⌋₊ * ∑ q ∈ F k, cofactorSupply R q := by
    rw [hUP, card_biUnion hpairP]
    exact sum_congr rfl hcP
  have hcardN : UN.card = ∑ k ∈ range (K + 1),
      ⌊2 * R / layerLength ε R k⌋₊ * ∑ q ∈ F k, cofactorSupply R q := by
    rw [hUN, card_biUnion hpairN]
    exact sum_congr rfl hcN
  have hUPUN : UP ∪ UN = (range (K + 1)).biUnion fun k => UPk k ∪ UNk k := by
    rw [hUP, hUN, biUnion_union]
  refine ⟨UP, UN, hdisj, hμUP, hμUN, fun n hn => ?_, by rw [hcardP, hcardN], ?_,
    fun δ hδ0 hδ1 => ?_⟩
  · rw [hUPUN] at hn
    obtain ⟨k, hk, hn⟩ := mem_biUnion.mp hn
    obtain ⟨h1, h2, q, hq, hsh⟩ := hpos k hk n hn
    obtain ⟨hadm, -, hqY, -⟩ := hFmem k q hq
    exact ⟨h1, h2, q, (by exact_mod_cast hqY : (q : ℝ) ≤ Y).trans hYR, hadm, hsh⟩
  · -- the count
    rw [hcardP]
    push_cast
    set Yβ : ℕ := ⌊R ^ β⌋₊ with hYβ
    have hRβ1 : 1 ≤ R ^ β := Real.one_le_rpow hR1 hβ0.le
    have hYβ1 : 1 ≤ Yβ := Nat.le_floor (by exact_mod_cast hRβ1)
    have hYβR : (Yβ : ℝ) ≤ R ^ β := Nat.floor_le (by linarith)
    set Gs : Finset ℕ := (Icc 1 Yβ).filter fun q => Odd q ∧ Squarefree q with hGs
    have hRββ : R ^ β ≤ R ^ (1 - β) := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
    have hGsub : Gs ⊆ Fall := by
      intro q hq
      simp only [hGs, mem_filter, mem_Icc] at hq
      obtain ⟨⟨hq1, hqY⟩, hqodd, hqsq⟩ := hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
      have hqβ : (q : ℝ) ≤ R ^ β := (by exact_mod_cast hqY : (q : ℝ) ≤ Yβ).trans hYβR
      have hYle : Yβ ≤ Y := Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hR1 hβη.le)
      simp only [hFall, mem_filter, mem_Icc]
      refine ⟨⟨hq1, hqY.trans hYle⟩, hq1, hqodd, hqsq, fun ℓ hℓ hℓq => ?_⟩
      have hℓ : (ℓ : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) hℓq
      have hRq' : R ^ (1 - β) ≤ R / q := by
        rw [le_div_iff₀ hq0]
        calc R ^ (1 - β) * q ≤ R ^ (1 - β) * R ^ β :=
              mul_le_mul_of_nonneg_left hqβ (Real.rpow_nonneg hR0.le _)
          _ = R := by rw [← Real.rpow_add hR0]; simp
      have hstrict : R ^ β < R ^ (1 - β) := by
        rcases eq_or_lt_of_le hR1 with h | h
        · rw [← h] at hR5; norm_num at hR5
        · exact Real.rpow_lt_rpow_of_exponent_lt h (by linarith)
      linarith
    have hmaps : ∀ q ∈ Fall, Nat.log 2 q ∈ range (K + 1) := by
      intro q hq
      simp only [hFall, mem_filter, mem_Icc] at hq
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hq.1.2))
    have hfib : ∑ k ∈ range (K + 1), (⌊2 * R / layerLength ε R k⌋₊ : ℝ) *
        ∑ q ∈ F k, (cofactorSupply R q : ℝ) =
        ∑ q ∈ Fall, (⌊2 * R / layerLength ε R (Nat.log 2 q)⌋₊ : ℝ) * (cofactorSupply R q : ℝ) := by
      rw [← sum_fiberwise_of_maps_to hmaps]
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      rw [(mem_filter.mp hq).2]
    rw [hfib]
    have hper : ∀ q ∈ Gs, ε * R / (2 ^ 20 * Real.log R) * (1 / (q : ℝ)) ≤
        (⌊2 * R / layerLength ε R (Nat.log 2 q)⌋₊ : ℝ) * (cofactorSupply R q : ℝ) := by
      intro q hq
      have hqF := hGsub hq
      have hq1 : 1 ≤ q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hqY : q ≤ Y := (mem_Icc.mp (mem_filter.mp hqF).1).2
      have hsupp : 131072 * Real.log R ≤ (R / q) ^ supplyExp := by
        have h1 := hRq q hq1 hqY
        calc 131072 * Real.log R ≤ R ^ (supplyExp * (1 - η)) := hsup
          _ = (R ^ (1 - η)) ^ supplyExp := by rw [← Real.rpow_mul hR0.le]; ring_nf
          _ ≤ (R / q) ^ supplyExp :=
              Real.rpow_le_rpow (Real.rpow_nonneg hR0.le _) h1 supplyExp_pos.le
      exact layer_count_ge hε0 hR5 hq1 (Nat.pow_log_le_self 2 (by omega))
        (hLk _ (hmaps q hqF)) hsupp
    have hnonneg : ∀ q ∈ Fall, 0 ≤ (⌊2 * R / layerLength ε R (Nat.log 2 q)⌋₊ : ℝ) *
        (cofactorSupply R q : ℝ) := fun q _ => by positivity
    have hGsum := sum_inv_odd_squarefree_ge hYβ1
    rw [← hGs] at hGsum
    have hlogY := log_floor_rpow_ge hR1 hβ0.le
    rw [← hYβ] at hlogY
    have hharm : β * Real.log R / 16 ≤ ∑ q ∈ Gs, 1 / (q : ℝ) := by
      refine le_trans ?_ hGsum
      have h1 : 2 * (Real.log 2 + 7) ≤ β * Real.log R := by
        rw [div_le_iff₀ hβ0] at hlogβ; linarith
      linarith
    have hc0 : 0 ≤ ε * R / (2 ^ 20 * Real.log R) := by positivity
    calc ε * β / (16 * 2 ^ 20) * R = ε * R / (2 ^ 20 * Real.log R) * (β * Real.log R / 16) := by
          field_simp
      _ ≤ ε * R / (2 ^ 20 * Real.log R) * ∑ q ∈ Gs, 1 / (q : ℝ) :=
          mul_le_mul_of_nonneg_left hharm hc0
      _ = ∑ q ∈ Gs, ε * R / (2 ^ 20 * Real.log R) * (1 / (q : ℝ)) := by rw [mul_sum]
      _ ≤ ∑ q ∈ Gs, (⌊2 * R / layerLength ε R (Nat.log 2 q)⌋₊ : ℝ) * (cofactorSupply R q : ℝ) :=
          sum_le_sum hper
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hGsub fun q hq _ => hnonneg q hq
  · -- the norm
    have hδ : 0 < 5 + δ := by linarith
    have hfun : (fun t => ∑ n ∈ UP ∪ UN, ((μ n : ℤ) : ℝ) * atom n t) =
        fun t => ∑ k ∈ range (K + 1), ∑ n ∈ UPk k ∪ UNk k, ((μ n : ℤ) : ℝ) * atom n t := by
      funext t
      rw [hUPUN, sum_biUnion hpairU]
    rw [hfun]
    have hfin : ∀ k ∈ range (K + 1), GammaFinite δ (fun t => ∑ n ∈ UPk k ∪ UNk k,
        ((μ n : ℤ) : ℝ) * atom n t) := by
      intro k hk
      refine gammaFinite_atomSum hδ _ _ fun n hn => ?_
      have := (hpos k hk n hn).1
      have : (1 : ℝ) ≤ n := by linarith
      exact_mod_cast this
    refine (gammaNorm_sum_le hδ _ hfin).trans ?_
    refine (sum_le_sum fun k hk => hnorm k hk δ hδ0 hδ1).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
    -- the number of layers
    have hK : ((K + 1 : ℕ) : ℝ) ≤ G * Real.log R := by
      have h2K : (2 : ℝ) ^ K ≤ R ^ η := by
        have : 2 ^ K ≤ Y := Nat.pow_log_le_self 2 (by omega)
        exact (by exact_mod_cast this : (2 : ℝ) ^ K ≤ Y).trans hYR
      have hKlog : (K : ℝ) * Real.log 2 ≤ η * Real.log R := by
        rw [← Real.log_rpow hR0, ← Real.log_pow]
        exact Real.log_le_log (by positivity) h2K
      have : (K : ℝ) ≤ η / Real.log 2 * Real.log R := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]; linarith
      push_cast
      rw [hGdef]
      nlinarith
    have hE : 0 < (R ^ ((5 + δ) / 2))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hR0 _)
    have hid1 : R ^ 2 * (R ^ ((5 + δ) / 2))⁻¹ = R ^ (-(1 / 2 : ℝ) - δ / 2) := by
      rw [← Real.rpow_neg hR0.le, ← Real.rpow_natCast, ← Real.rpow_add hR0]
      congr 1; push_cast; ring
    have hid2 : R ^ (-((d + 1) * ((1 - supplyExp) * (1 - η)))) * R ^ 3 * (R ^ ((5 + δ) / 2))⁻¹ =
        R ^ (1 / 2 - (d + 1) * (1 - supplyExp) * (1 - η) - δ / 2) := by
      rw [← Real.rpow_neg hR0.le, ← Real.rpow_natCast R 3, ← Real.rpow_add hR0,
        ← Real.rpow_add hR0]
      congr 1; push_cast; ring
    rw [hid1, hid2]
    have a1 : 0 ≤ R ^ (-(1 / 2 : ℝ) - δ / 2) := Real.rpow_nonneg hR0.le _
    have a2 : 0 ≤ R ^ (1 / 2 - (d + 1) * (1 - supplyExp) * (1 - η) - δ / 2) :=
      Real.rpow_nonneg hR0.le _
    have hin : 0 ≤ A * R ^ (-(1 / 2 : ℝ) - δ / 2) + D *
        (R ^ (1 / 2 - (d + 1) * (1 - supplyExp) * (1 - η) - δ / 2) / Real.log R) := by positivity
    calc ((K + 1 : ℕ) : ℝ) * (A * R ^ (-(1 / 2 : ℝ) - δ / 2) + D *
          (R ^ (1 / 2 - (d + 1) * (1 - supplyExp) * (1 - η) - δ / 2) / Real.log R))
        ≤ G * Real.log R * (A * R ^ (-(1 / 2 : ℝ) - δ / 2) + D *
          (R ^ (1 / 2 - (d + 1) * (1 - supplyExp) * (1 - η) - δ / 2) / Real.log R)) := by
          gcongr
      _ = G * (A * (R ^ (-(1 / 2 : ℝ) - δ / 2) * Real.log R) +
            D * R ^ (1 / 2 - (d + 1) * (1 - supplyExp) * (1 - η) - δ / 2)) := by
          field_simp
      _ ≤ (G * (A + D) + 1) * (R ^ (-(1 / 2 : ℝ) - δ / 2) * Real.log R +
            R ^ (1 / 2 - (d + 1) * (1 - supplyExp) * (1 - η) - δ / 2)) := by
          exact layer_mix_le hG1 hA0 hD0 (by positivity) a2

end RHTower.CubicGamma
