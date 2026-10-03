import GaloisForLFunctions.RHTower.Sieve.VinogradovLogPhaseWeyl

/-!
# The Vinogradov parameters are uniform in the degree

For the estimate `norm_sum_logPhase_le_vinogradov`:

* the constant is absolute: `M_r ≤ e^{20}` for every `r ≥ 1` (`vinogradovWeylConstant_le`), because
  `log(C_{k,b}² (24b²)^k) ≤ 80 b²` once `b ≥ k²`;
* the saving is `δ_r ≥ 1/(5184 r² m_r²)` with `m_r = ⌊log₂(9r²)⌋ + 1` for `r ≥ 22`
  (`vinogradovWeylSaving_ge`): there are `≥ r/3` useful coordinates each saving `⌊r/4⌋ ≥ r/5`, and
  `b ≤ 9r² m_r`.

Hence `‖Σ_{A<n≤A+L} n^{it}‖ ≤ 4e^{20} L P^{-1/(5184 r² m_r²)} + 400P²`
(`norm_sum_logPhase_le_vinogradov_uniform`).
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem reservoirSize_le_cube {k : ℕ} (hk : 2 ≤ k) :
    vinogradovChebyshevReservoirSize k ≤ k ^ 3 := by
  unfold vinogradovChebyshevReservoirSize
  have h1 : k * (k * k - k) + 1 ≤ k * (k * k) := by
    have : k ≤ k * k := Nat.le_mul_self k
    have h2 : k * (k * k - k) = k * (k * k) - k * k := by rw [Nat.mul_sub]
    have h3 : k * k ≤ k * (k * k) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  calc k * (k * k - k) + 1 ≤ k * (k * k) := h1
    _ = k ^ 3 := by ring

theorem nat_le_exp (n : ℕ) : (n : ℝ) ≤ Real.exp n := by
  have := Real.add_one_le_exp (n : ℝ)
  linarith

/-- `log z ≤ 22 + 6k`. -/
theorem vinogradovExplicitThreshold_le_exp {k : ℕ} (hk : 2 ≤ k) :
    (vinogradovExplicitThreshold k : ℝ) ≤ Real.exp (22 + 6 * k) := by
  have hR := reservoirSize_le_cube hk
  have hz : vinogradovExplicitThreshold k ≤ 2 ^ 24 * 81 * k ^ 6 := by
    unfold vinogradovExplicitThreshold
    have hk1 : 1 ≤ k ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h81 : 81 * vinogradovChebyshevReservoirSize k ^ 2 ≤ 2 ^ 24 * 81 * k ^ 6 := by
      have : vinogradovChebyshevReservoirSize k ^ 2 ≤ (k ^ 3) ^ 2 := Nat.pow_le_pow_left hR 2
      have h6 : (k ^ 3) ^ 2 = k ^ 6 := by ring
      have h24 : 1 ≤ 2 ^ 24 := Nat.one_le_two_pow
      calc 81 * vinogradovChebyshevReservoirSize k ^ 2 ≤ 81 * k ^ 6 := by omega
        _ ≤ 2 ^ 24 * 81 * k ^ 6 := by
            have : 81 * k ^ 6 ≤ 2 ^ 24 * (81 * k ^ 6) := Nat.le_mul_of_pos_left _ (by positivity)
            linarith
    have h2 : 2 ^ 24 ≤ 2 ^ 24 * 81 * k ^ 6 := by
      have : 1 ≤ 81 * k ^ 6 := by omega
      calc 2 ^ 24 = 2 ^ 24 * 1 := by ring
        _ ≤ 2 ^ 24 * (81 * k ^ 6) := Nat.mul_le_mul_left _ this
        _ = 2 ^ 24 * 81 * k ^ 6 := by ring
    have h3 : k ≤ 2 ^ 24 * 81 * k ^ 6 := by
      have : k ≤ k ^ 6 := Nat.le_self_pow (by norm_num) k
      have : k ^ 6 ≤ 2 ^ 24 * 81 * k ^ 6 := Nat.le_mul_of_pos_left _ (by positivity)
      omega
    exact max_le (max_le h2 h81) h3
  have hzR : (vinogradovExplicitThreshold k : ℝ) ≤ 2 ^ 24 * 81 * (k : ℝ) ^ 6 := by
    exact_mod_cast hz
  have hc : (2 : ℝ) ^ 24 * 81 ≤ Real.exp 22 := by
    have h := Real.add_one_le_exp (22 : ℝ)
    have h2 : Real.exp 22 = Real.exp 1 ^ 22 := by rw [← Real.exp_nat_mul]; norm_num
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have : (2.7 : ℝ) ^ 22 ≤ Real.exp 1 ^ 22 := pow_le_pow_left₀ (by norm_num) he 22
    rw [h2]; norm_num at this ⊢; linarith
  have hk6 : (k : ℝ) ^ 6 ≤ Real.exp (6 * k) := by
    calc (k : ℝ) ^ 6 ≤ Real.exp k ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) (nat_le_exp k) 6
      _ = Real.exp (6 * k) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  calc (vinogradovExplicitThreshold k : ℝ) ≤ 2 ^ 24 * 81 * (k : ℝ) ^ 6 := hzR
    _ ≤ Real.exp 22 * Real.exp (6 * k) := mul_le_mul hc hk6 (by positivity) (by positivity)
    _ = Real.exp (22 + 6 * k) := (Real.exp_add _ _).symm

/-- `log Λ ≤ 8k²`. -/
theorem vinogradovExplicitGrowth_le_exp {k : ℕ} (hk : 2 ≤ k) :
    (vinogradovExplicitGrowth k : ℝ) ≤ Real.exp (8 * (k : ℝ) ^ 2) := by
  have hR := reservoirSize_le_cube hk
  have hRR : (vinogradovChebyshevReservoirSize k : ℝ) ≤ (k : ℝ) ^ 3 := by exact_mod_cast hR
  have hfact : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hkexp := nat_le_exp k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  -- `4 ≤ e²`, `k^6 ≤ e^{6k}`, `k^k ≤ e^{k²}`, `16^{k²} ≤ e^{3k²}`
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    rw [h2]; nlinarith
  have hpowexp : ∀ n : ℕ, (k : ℝ) ^ n ≤ Real.exp (n * k) := by
    intro n
    calc (k : ℝ) ^ n ≤ Real.exp k ^ n := pow_le_pow_left₀ hk0 hkexp n
      _ = Real.exp (n * k) := by rw [← Real.exp_nat_mul]
  have h16 : (16 : ℝ) ^ (k * k) ≤ Real.exp (3 * (k : ℝ) ^ 2) := by
    have h16e : (16 : ℝ) ≤ Real.exp 3 := by
      have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he 3
      rw [h2]; norm_num at this ⊢; linarith
    calc (16 : ℝ) ^ (k * k) ≤ Real.exp 3 ^ (k * k) := pow_le_pow_left₀ (by norm_num) h16e _
      _ = Real.exp (3 * (k : ℝ) ^ 2) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hval : (vinogradovExplicitGrowth k : ℝ) =
      4 * (vinogradovChebyshevReservoirSize k : ℝ) ^ 2 * (k.factorial : ℝ) * 16 ^ (k * k) := by
    simp only [vinogradovExplicitGrowth, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hval]
  calc 4 * (vinogradovChebyshevReservoirSize k : ℝ) ^ 2 * (k.factorial : ℝ) * 16 ^ (k * k)
      ≤ Real.exp 2 * ((k : ℝ) ^ 3) ^ 2 * (k : ℝ) ^ k * Real.exp (3 * (k : ℝ) ^ 2) := by
        gcongr
    _ = Real.exp 2 * (k : ℝ) ^ 6 * (k : ℝ) ^ k * Real.exp (3 * (k : ℝ) ^ 2) := by ring
    _ ≤ Real.exp 2 * Real.exp (6 * k) * Real.exp (k * k) * Real.exp (3 * (k : ℝ) ^ 2) := by
        gcongr
        · exact_mod_cast hpowexp 6
        · exact hpowexp k
    _ = Real.exp (2 + 6 * k + k * k + 3 * (k : ℝ) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (8 * (k : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith

/-- **The constant is absolute.** `M_r ≤ e^{20}`. -/
theorem vinogradovWeylConstant_le {r : ℕ} (hr : 1 ≤ r) :
    vinogradovWeylConstant r ≤ Real.exp 20 := by
  set k := vinogradovWeylDegree r with hkdef
  set b := vinogradovWeylMoment r with hbdef
  have hk3 : 3 ≤ k := three_le_vinogradovWeylDegree hr
  have hb1 : 1 ≤ b := one_le_vinogradovWeylMoment r
  have hkb : k ^ 2 ≤ b := by
    rw [hbdef, vinogradovWeylMoment, ← hkdef]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hkbR : (k : ℝ) ^ 2 ≤ b := by exact_mod_cast hkb
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hkbR' : (k : ℝ) ≤ b := le_trans hkk hkbR
  have hk4 : (k : ℝ) ^ 4 ≤ (b : ℝ) ^ 2 := by
    have : ((k : ℝ) ^ 2) ^ 2 ≤ (b : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hkbR 2
    nlinarith
  -- the explicit constant
  have hC : vinogradovExplicitConstant k b ≤ Real.exp (37 * (b : ℝ) ^ 2) := by
    unfold vinogradovExplicitConstant
    have hz := vinogradovExplicitThreshold_le_exp (k := k) (by omega)
    have hΛ := vinogradovExplicitGrowth_le_exp (k := k) (by omega)
    have hKn : ((k * (k * (k + 1) / 2) : ℕ) : ℝ) ≤ (k : ℝ) ^ 3 := by
      have : k * (k * (k + 1) / 2) ≤ k ^ 3 := by
        have h1 : k * (k + 1) / 2 ≤ k * k := by
          have : k * (k + 1) ≤ 2 * (k * k) := by nlinarith
          omega
        calc k * (k * (k + 1) / 2) ≤ k * (k * k) := Nat.mul_le_mul_left _ h1
          _ = k ^ 3 := by ring
      exact_mod_cast this
    have hzpow : (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2)) ≤
        Real.exp (28 * (k : ℝ) ^ 4) := by
      calc (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2))
          ≤ Real.exp (22 + 6 * k) ^ (k * (k * (k + 1) / 2)) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hz _
        _ = Real.exp ((k * (k * (k + 1) / 2) : ℕ) * (22 + 6 * k)) := by
            rw [← Real.exp_nat_mul]
        _ ≤ Real.exp ((k : ℝ) ^ 3 * (22 + 6 * k)) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_right hKn (by positivity)
        _ ≤ Real.exp (28 * (k : ℝ) ^ 4) := by
            apply Real.exp_le_exp.mpr
            nlinarith
    have hΛpow : (vinogradovExplicitGrowth k : ℝ) ^ b ≤ Real.exp (8 * (b : ℝ) ^ 2) := by
      calc (vinogradovExplicitGrowth k : ℝ) ^ b ≤ Real.exp (8 * (k : ℝ) ^ 2) ^ b :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hΛ _
        _ = Real.exp (b * (8 * (k : ℝ) ^ 2)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (8 * (b : ℝ) ^ 2) := by
            apply Real.exp_le_exp.mpr; nlinarith
    have h2pow : (2 : ℝ) ^ ((b : ℝ) ^ 2 / k) ≤ Real.exp ((b : ℝ) ^ 2) := by
      rw [Real.rpow_def_of_pos (by norm_num), Real.exp_le_exp]
      have hl : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      have hdiv : (b : ℝ) ^ 2 / k ≤ (b : ℝ) ^ 2 := div_le_self (by positivity) (by linarith)
      have : 0 ≤ (b : ℝ) ^ 2 / k := by positivity
      have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    calc (vinogradovExplicitThreshold k : ℝ) ^ (k * (k * (k + 1) / 2)) *
          (vinogradovExplicitGrowth k : ℝ) ^ b * (2 : ℝ) ^ ((b : ℝ) ^ 2 / k)
        ≤ Real.exp (28 * (k : ℝ) ^ 4) * Real.exp (8 * (b : ℝ) ^ 2) * Real.exp ((b : ℝ) ^ 2) := by
          gcongr
      _ = Real.exp (28 * (k : ℝ) ^ 4 + 8 * (b : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (37 * (b : ℝ) ^ 2) := by
          apply Real.exp_le_exp.mpr; nlinarith
  have hfac : (24 * (b : ℝ) ^ 2) ^ k ≤ Real.exp (6 * (b : ℝ) ^ 2) := by
    have hlog : Real.log (24 * (b : ℝ) ^ 2) ≤ 4 + 2 * b := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have h24 : Real.log 24 ≤ 4 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he 4
        rw [h2]; norm_num at this ⊢; linarith
      have hb : Real.log b ≤ b := by
        have := Real.log_le_sub_one_of_pos hb0; linarith
      push_cast
      linarith
    rw [← Real.exp_log (show (0 : ℝ) < 24 * (b : ℝ) ^ 2 by positivity), ← Real.exp_nat_mul,
      Real.exp_le_exp]
    calc (k : ℝ) * Real.log (24 * (b : ℝ) ^ 2) ≤ k * (4 + 2 * b) :=
          mul_le_mul_of_nonneg_left hlog hk0.le
      _ ≤ 6 * (b : ℝ) ^ 2 := by nlinarith
  have hbase : vinogradovExplicitConstant k b ^ 2 * (24 * (b : ℝ) ^ 2) ^ k ≤
      Real.exp (80 * (b : ℝ) ^ 2) := by
    have hC0 := (vinogradovExplicitConstant_pos k b).le
    calc vinogradovExplicitConstant k b ^ 2 * (24 * (b : ℝ) ^ 2) ^ k
        ≤ Real.exp (37 * (b : ℝ) ^ 2) ^ 2 * Real.exp (6 * (b : ℝ) ^ 2) := by gcongr
      _ = Real.exp (80 * (b : ℝ) ^ 2) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  unfold vinogradovWeylConstant
  rw [← hkdef, ← hbdef]
  have hbase0 : 0 ≤ vinogradovExplicitConstant k b ^ 2 * (24 * (b : ℝ) ^ 2) ^ k := by
    have := (vinogradovExplicitConstant_pos k b).le; positivity
  calc (vinogradovExplicitConstant k b ^ 2 * (24 * (b : ℝ) ^ 2) ^ k) ^
        ((((4 * b ^ 2 : ℕ) : ℝ))⁻¹)
      ≤ Real.exp (80 * (b : ℝ) ^ 2) ^ ((((4 * b ^ 2 : ℕ) : ℝ))⁻¹) :=
        Real.rpow_le_rpow hbase0 hbase (by positivity)
    _ = Real.exp 20 := by
        rw [← Real.exp_mul]
        congr 1
        push_cast
        field_simp
        ring

/-- **The saving is `≫ 1/(r² log² r)`.** For `r ≥ 22`,
`δ_r ≥ 1/(5184 r² m_r²)`, `m_r = ⌊log₂(9r²)⌋ + 1`. -/
theorem vinogradovWeylSaving_ge {r : ℕ} (hr : 22 ≤ r) :
    1 / (5184 * (r : ℝ) ^ 2 * ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ^ 2) ≤
      vinogradovWeylSaving r := by
  set m := Nat.log 2 (vinogradovWeylK r) + 1 with hm
  set m' := Nat.log 2 (9 * r ^ 2) + 1 with hm'
  have hmm : m ≤ m' := by
    have hK : vinogradovWeylK r ≤ 9 * r ^ 2 := by
      unfold vinogradovWeylK vinogradovWeylDegree
      have : (2 * r + 2) * (2 * r + 2 + 1) ≤ 2 * (9 * r ^ 2) := by nlinarith
      omega
    have := Nat.log_mono_right (b := 2) hK
    omega
  -- count and save
  have hcount : r ≤ 3 * vinogradovWeylCount r := by
    unfold vinogradovWeylCount vinogradovWeylHigh vinogradovWeylLow
    omega
  have hsave : r ≤ 5 * vinogradovWeylSave r := by
    unfold vinogradovWeylSave; omega
  have hnum : (r : ℝ) ^ 2 / 16 ≤ ((vinogradovWeylCount r * vinogradovWeylSave r : ℕ) : ℝ) - 2 := by
    have h1 : (r : ℝ) ≤ 3 * vinogradovWeylCount r := by exact_mod_cast hcount
    have h2 : (r : ℝ) ≤ 5 * vinogradovWeylSave r := by exact_mod_cast hsave
    have hr22 : (22 : ℝ) ≤ r := by exact_mod_cast hr
    have h0 : (0 : ℝ) ≤ r := by linarith
    have hprod : (r : ℝ) * r ≤ 15 * ((vinogradovWeylCount r : ℝ) * vinogradovWeylSave r) := by
      nlinarith
    push_cast
    nlinarith
  -- the moment
  have hb : (vinogradovWeylMoment r : ℝ) ≤ 9 * (r : ℝ) ^ 2 * m' := by
    have h1 : vinogradovWeylMoment r ≤ 9 * r ^ 2 * m' := by
      unfold vinogradovWeylMoment vinogradovWeylDegree
      rw [← hm]
      have hk : (2 * r + 2) ^ 2 ≤ 9 * r ^ 2 := by nlinarith
      exact Nat.mul_le_mul hk hmm
    exact_mod_cast h1
  have hb0 : (0 : ℝ) < vinogradovWeylMoment r := by
    exact_mod_cast (one_le_vinogradovWeylMoment r)
  have hm'0 : (0 : ℝ) < m' := by positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  unfold vinogradovWeylSaving
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hb2 : (vinogradovWeylMoment r : ℝ) ^ 2 ≤ (9 * (r : ℝ) ^ 2 * m') ^ 2 :=
    pow_le_pow_left₀ hb0.le hb 2
  calc 1 * (4 * (vinogradovWeylMoment r : ℝ) ^ 2) ≤ 4 * (9 * (r : ℝ) ^ 2 * m') ^ 2 := by
        linarith
    _ = (r : ℝ) ^ 2 / 16 * (5184 * (r : ℝ) ^ 2 * (m' : ℝ) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hnum (by positivity)

/-- **Vinogradov's estimate with uniform parameters.** -/
theorem norm_sum_logPhase_le_vinogradov_uniform {r Q A L : ℕ} {t : ℝ} (hr : 22 ≤ r)
    (hP : vinogradovWeylThreshold r ≤ 2 * Q)
    (ht1 : ((2 * Q : ℕ) : ℝ) ^ (4 * r) ≤ t) (ht2 : t ≤ ((2 * Q : ℕ) : ℝ) ^ (4 * r + 4))
    (hA : 4 * (2 * Q) ^ 4 ≤ A) (hAL : A + L ≤ 162 * (2 * Q) ^ 4) :
    ‖∑ n ∈ Finset.Ioc A (A + L), vinogradovLogPhase t n‖ ≤
      4 * Real.exp 20 * L * ((2 * Q : ℕ) : ℝ) ^
          (-(1 / (5184 * (r : ℝ) ^ 2 * ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ^ 2))) +
        400 * ((2 * Q : ℕ) : ℝ) ^ 2 := by
  have h := norm_sum_logPhase_le_vinogradov (by omega) hP ht1 ht2 hA hAL
  have hP1 : (1 : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := by
    have : 2 ^ 48 ≤ 2 * Q := le_trans (le_max_left _ _) hP
    have h1 : 1 ≤ 2 ^ 48 := Nat.one_le_two_pow
    exact_mod_cast (by omega : 1 ≤ 2 * Q)
  have hM := vinogradovWeylConstant_le (r := r) (by omega)
  have hM0 : 0 ≤ vinogradovWeylConstant r := Real.rpow_nonneg (by
    have := (vinogradovExplicitConstant_pos (vinogradovWeylDegree r) (vinogradovWeylMoment r)).le
    positivity) _
  have hδ := vinogradovWeylSaving_ge hr
  have hpow : ((2 * Q : ℕ) : ℝ) ^ (-vinogradovWeylSaving r) ≤ ((2 * Q : ℕ) : ℝ) ^
      (-(1 / (5184 * (r : ℝ) ^ 2 * ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ^ 2))) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hw0 : 0 ≤ ((2 * Q : ℕ) : ℝ) ^ (-vinogradovWeylSaving r) := Real.rpow_nonneg (by linarith) _
  refine h.trans ?_
  gcongr

end

end RHTower.Sieve
