import GaloisForLFunctions.RHTower.Sieve.VinogradovWeylParameters

/-!
# Vinogradov's estimate on a dyadic block `[N, 2N]`

For `N ≥ 3⁸`, `N^{22} ≤ t ≤ (N^{1/4}/3)^{4R}` and `P₀(R) ≤ N^{1/4}/3`, every interval
`(A, A+L] ⊂ [N, 2N]` satisfies

`‖Σ_{A<n≤A+L} n^{it}‖ ≤ 12 e^{20} L N^{-δ_R/4} + 200 N^{1/2}`,   `δ_R = 1/(5184 R² m_R²)`

(`norm_sum_logPhase_le_dyadic`), `m_R = ⌊log₂(9R²)⌋ + 1`.  The proof picks the even integer
`P = 2⌈N^{1/4}/6⌉ ∈ [N^{1/4}/3, N^{1/4}/√2]`, so that `[N, 2N] ⊂ [4P⁴, 162P⁴]`, and the order
`r = ⌊log t/(4 log P)⌋ ∈ [22, R]`, so that `P^{4r} ≤ t ≤ P^{4r+4}`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The saving exponent `δ_R = 1/(5184 R² m_R²)`. -/
def vinogradovDyadicSaving (R : ℕ) : ℝ :=
  1 / (5184 * (R : ℝ) ^ 2 * ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) ^ 2)

theorem vinogradovDyadicSaving_pos (R : ℕ) (hR : 1 ≤ R) : 0 < vinogradovDyadicSaving R := by
  unfold vinogradovDyadicSaving
  have : (1 : ℝ) ≤ R := by exact_mod_cast hR
  positivity

theorem vinogradovDyadicSaving_anti {r R : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R) :
    vinogradovDyadicSaving R ≤ vinogradovDyadicSaving r := by
  unfold vinogradovDyadicSaving
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrRR : (r : ℝ) ≤ R := by exact_mod_cast hrR
  have hm : Nat.log 2 (9 * r ^ 2) + 1 ≤ Nat.log 2 (9 * R ^ 2) + 1 := by
    have : 9 * r ^ 2 ≤ 9 * R ^ 2 := by
      have := Nat.pow_le_pow_left hrR 2
      omega
    have := Nat.log_mono_right (b := 2) this
    omega
  have hmR : ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_left 1 _)
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem vinogradovWeylThreshold_mono {r R : ℕ} (hrR : r ≤ R) :
    vinogradovWeylThreshold r ≤ vinogradovWeylThreshold R := by
  unfold vinogradovWeylThreshold
  apply max_le_max le_rfl
  apply Nat.pow_le_pow_left
  have hk : vinogradovWeylDegree r ≤ vinogradovWeylDegree R := by
    unfold vinogradovWeylDegree; omega
  have hK : vinogradovWeylK r ≤ vinogradovWeylK R := by
    unfold vinogradovWeylK
    exact Nat.div_le_div_right (Nat.mul_le_mul hk (by omega))
  have hb : vinogradovWeylMoment r ≤ vinogradovWeylMoment R := by
    unfold vinogradovWeylMoment
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hk 2)
      (by have := Nat.log_mono_right (b := 2) hK; omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)) hk

/-- **Vinogradov's estimate on a dyadic block.** -/
theorem norm_sum_logPhase_le_dyadic {N R A L : ℕ} {t : ℝ} (hR : 22 ≤ R) (hN : 3 ^ 8 ≤ N)
    (hNt : (N : ℝ) ^ 22 ≤ t) (htR : t ≤ ((N : ℝ) ^ ((1 : ℝ) / 4) / 3) ^ (4 * R))
    (hthr : (vinogradovWeylThreshold R : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) / 3)
    (hA : N ≤ A) (hAL : A + L ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc A (A + L), vinogradovLogPhase t n‖ ≤
      12 * Real.exp 20 * L * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4)) +
        200 * (N : ℝ) ^ ((1 : ℝ) / 2) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (N : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hy] at htR hthr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hy0 : 0 < y := by rw [hy]; exact Real.rpow_pos_of_pos hN0 _
  have hy4 : y ^ 4 = N := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hy9 : (9 : ℝ) ≤ y := by
    have h : ((3 : ℝ) ^ 8) ^ ((1 : ℝ) / 4) ≤ y := by
      rw [hy]; exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN) (by norm_num)
    have e : ((3 : ℝ) ^ 8) ^ ((1 : ℝ) / 4) = 9 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  -- the even integer `P`
  set Q : ℕ := ⌈y / 6⌉₊ with hQ
  set P : ℝ := ((2 * Q : ℕ) : ℝ) with hP
  have hQlow : y / 6 ≤ Q := Nat.le_ceil _
  have hQup : (Q : ℝ) < y / 6 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hPlow : y / 3 ≤ P := by rw [hP]; push_cast; linarith
  have hPup : P ≤ y * (7 / 10) := by
    rw [hP]; push_cast; nlinarith
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hPlow
  have hP1 : 1 < P := by nlinarith
  have hQ1 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ Q := by nlinarith
    exact_mod_cast this
  -- `[N, 2N] ⊂ [4P⁴, 162P⁴]`
  have hP4up : 4 * P ^ 4 ≤ N := by
    rw [← hy4]
    have : P ^ 4 ≤ (y * (7 / 10)) ^ 4 := pow_le_pow_left₀ hP0.le hPup 4
    nlinarith [pow_nonneg hy0.le 4]
  have hP4low : (2 * N : ℝ) ≤ 162 * P ^ 4 := by
    rw [← hy4]
    have : (y / 3) ^ 4 ≤ P ^ 4 := pow_le_pow_left₀ (by positivity) hPlow 4
    nlinarith
  have hPQ : P = 2 * (Q : ℝ) := by rw [hP]; push_cast; ring
  have hAnat : 4 * (2 * Q) ^ 4 ≤ A := by
    have : ((4 * (2 * Q) ^ 4 : ℕ) : ℝ) ≤ N := by
      push_cast; rw [hPQ] at hP4up; exact hP4up
    have : 4 * (2 * Q) ^ 4 ≤ N := by exact_mod_cast this
    omega
  have hALnat : A + L ≤ 162 * (2 * Q) ^ 4 := by
    have : ((2 * N : ℕ) : ℝ) ≤ ((162 * (2 * Q) ^ 4 : ℕ) : ℝ) := by
      push_cast; rw [hPQ] at hP4low; exact hP4low
    have : 2 * N ≤ 162 * (2 * Q) ^ 4 := by exact_mod_cast this
    omega
  -- the order `r`
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hNt
  set r : ℕ := ⌊Real.log t / (4 * Real.log P)⌋₊ with hr
  have hlogt : Real.log t = Real.log t := rfl
  have hr_le : (r : ℝ) ≤ Real.log t / (4 * Real.log P) := Nat.floor_le (by
    have : 0 ≤ Real.log t := Real.log_nonneg (le_trans (one_le_pow₀ (by
      exact_mod_cast (by omega : 1 ≤ N))) hNt)
    positivity)
  have hr_lt : Real.log t / (4 * Real.log P) < r + 1 := Nat.lt_floor_add_one _
  have ht1 : P ^ (4 * r) ≤ t := by
    rw [← Real.rpow_natCast, Real.rpow_le_iff_le_log hP0 ht0]
    rw [le_div_iff₀ (by positivity)] at hr_le
    push_cast; linarith
  have ht2 : t ≤ P ^ (4 * r + 4) := by
    rw [← Real.rpow_natCast, Real.le_rpow_iff_log_le ht0 hP0]
    rw [div_lt_iff₀ (by positivity)] at hr_lt
    push_cast; linarith
  have hlogPy : Real.log P ≤ Real.log y := Real.log_le_log hP0 (by linarith)
  have hlogyN : 4 * Real.log y = Real.log N := by
    rw [← hy4, Real.log_pow]; push_cast; ring
  have hr22 : 22 ≤ r := by
    have h1 : 22 * Real.log N ≤ Real.log t := by
      have := Real.log_le_log (by positivity) hNt
      rwa [Real.log_pow] at this
    have h2 : (22 : ℝ) ≤ Real.log t / (4 * Real.log P) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    exact Nat.le_floor (by exact_mod_cast h2)
  have hrR : r ≤ R := by
    have hle : t ≤ P ^ (4 * R) := htR.trans (pow_le_pow_left₀ (by positivity) hPlow _)
    have h1 : Real.log t ≤ (4 * R) * Real.log P := by
      have := Real.log_le_log ht0 hle
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have h2 : Real.log t / (4 * Real.log P) ≤ R := by
      rw [div_le_iff₀ (by positivity)]; linarith
    exact Nat.floor_le_of_le h2
  have hthrP : vinogradovWeylThreshold r ≤ 2 * Q := by
    have h1 := vinogradovWeylThreshold_mono hrR
    have h2 : (vinogradovWeylThreshold R : ℝ) ≤ P := hthr.trans hPlow
    have : (vinogradovWeylThreshold R : ℝ) ≤ ((2 * Q : ℕ) : ℝ) := h2
    have h3 : vinogradovWeylThreshold R ≤ 2 * Q := by exact_mod_cast this
    omega
  have hmain := norm_sum_logPhase_le_vinogradov_uniform hr22 hthrP ht1 ht2 hAnat hALnat
  rw [← hP] at hmain
  -- convert to `N`
  have hδ := vinogradovDyadicSaving_anti (by omega : 1 ≤ r) hrR
  have hδ0 := vinogradovDyadicSaving_pos R (by omega)
  have hpow1 : P ^ (-(1 / (5184 * (r : ℝ) ^ 2 * ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ^ 2))) ≤
      P ^ (-vinogradovDyadicSaving R) := by
    apply Real.rpow_le_rpow_of_exponent_le hP1.le
    unfold vinogradovDyadicSaving at hδ ⊢
    linarith
  have hpow2 : P ^ (-vinogradovDyadicSaving R) ≤
      3 * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4)) := by
    calc P ^ (-vinogradovDyadicSaving R) ≤ (y / 3) ^ (-vinogradovDyadicSaving R) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hPlow (by linarith)
      _ = 3 ^ vinogradovDyadicSaving R * y ^ (-vinogradovDyadicSaving R) := by
          rw [Real.div_rpow hy0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
          field_simp
      _ ≤ 3 * y ^ (-vinogradovDyadicSaving R) := by
          gcongr
          calc (3 : ℝ) ^ vinogradovDyadicSaving R ≤ 3 ^ (1 : ℝ) := by
                apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
                unfold vinogradovDyadicSaving
                rw [div_le_one (by positivity)]
                have hR22 : (22 : ℝ) ≤ R := by exact_mod_cast hR
                have hm1 : (1 : ℝ) ≤ ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) := by
                  exact_mod_cast (Nat.le_add_left 1 _)
                have hR2 : (1 : ℝ) ≤ (R : ℝ) ^ 2 := one_le_pow₀ (by linarith)
                have hm2 : (1 : ℝ) ≤ ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) ^ 2 := one_le_pow₀ hm1
                have h := mul_le_mul (mul_le_mul (show (1 : ℝ) ≤ 5184 by norm_num) hR2
                  (by norm_num) (by norm_num)) hm2 (by norm_num) (by positivity)
                linarith
            _ = 3 := Real.rpow_one 3
      _ = 3 * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4)) := by
          rw [hy, ← Real.rpow_mul hN0.le,
            show (1 : ℝ) / 4 * -vinogradovDyadicSaving R = -(vinogradovDyadicSaving R / 4) by ring]
  have hP2 : P ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) / 2 := by
    have hy2 : y ^ 2 = (N : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    have h1 : P ^ 2 ≤ (y * (7 / 10)) ^ 2 := pow_le_pow_left₀ hP0.le hPup 2
    have h2 : (y * (7 / 10)) ^ 2 = 49 / 100 * y ^ 2 := by ring
    have h3 : 0 ≤ y ^ 2 := sq_nonneg y
    rw [← hy2]
    linarith
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hE : (0 : ℝ) ≤ 4 * Real.exp 20 := by positivity
  calc ‖∑ n ∈ Finset.Ioc A (A + L), vinogradovLogPhase t n‖
      ≤ 4 * Real.exp 20 * L *
          P ^ (-(1 / (5184 * (r : ℝ) ^ 2 * ((Nat.log 2 (9 * r ^ 2) + 1 : ℕ) : ℝ) ^ 2))) +
        400 * P ^ 2 := hmain
    _ ≤ 4 * Real.exp 20 * L * (3 * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4))) +
        400 * ((N : ℝ) ^ ((1 : ℝ) / 2) / 2) := by
        gcongr
        exact hpow1.trans hpow2
    _ = 12 * Real.exp 20 * L * (N : ℝ) ^ (-(vinogradovDyadicSaving R / 4)) +
        200 * (N : ℝ) ^ ((1 : ℝ) / 2) := by ring

end

end RHTower.Sieve
