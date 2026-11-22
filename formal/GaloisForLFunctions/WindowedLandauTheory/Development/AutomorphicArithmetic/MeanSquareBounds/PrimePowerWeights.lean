import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimePowerPairs
import GaloisForLFunctions.RHTower.MertensFirst

/-! Chebyshev and Mertens bounds for the total and prime-power masses of the smoothed coefficients. -/

open Finset Classical
open ArithmeticFunction (vonMangoldt)

noncomputable section

namespace QH

theorem cN_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cN x n := by
  unfold cN
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))

theorem cN_primePow (x : ℝ) (n : ℕ) (h : cN x n ≠ 0) : IsPrimePow n := by
  unfold cN at h
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h)

def chebyshevConstant : ℝ := Real.log 4 + 4

lemma chebyshevConstant_pos : 0 < chebyshevConstant := by
  have h : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold chebyshevConstant
  linarith

private lemma Icc_one_eq_Ioc_zero (M : ℕ) : Icc 1 M = Ioc 0 M := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

lemma sum_vonMangoldt_mul_le (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : ∀ n, 1 ≤ n → g (n + 1) ≤ g n) (N : ℕ) :
    ∑ n ∈ Icc 1 N, vonMangoldt n * g n ≤ chebyshevConstant * ∑ n ∈ Icc 1 N, g n := by
  have key : ∀ M : ℕ, (∑ n ∈ Icc 1 M, vonMangoldt n * g n) - (∑ n ∈ Icc 1 M, vonMangoldt n) * g M
      ≤ chebyshevConstant * ((∑ n ∈ Icc 1 M, g n) - (M : ℝ) * g M) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega)]
      have h1 : (∑ n ∈ Icc 1 M, vonMangoldt n) * (g M - g (M + 1))
          ≤ chebyshevConstant * M * (g M - g (M + 1)) := by
        rcases Nat.eq_zero_or_pos M with h | h
        · subst h
          simp
        · exact mul_le_mul_of_nonneg_right (RHTower.Mertens.sum_vonMangoldt_Icc_le M) (by linarith [hg M h])
      push_cast
      linarith
  have h2 : (∑ n ∈ Icc 1 N, vonMangoldt n) * g N ≤ chebyshevConstant * N * g N :=
    mul_le_mul_of_nonneg_right (RHTower.Mertens.sum_vonMangoldt_Icc_le N) (hg0 N)
  have h3 := key N
  linarith

private lemma sum_truncated_le_cutoff_add_tail (u : ℕ → ℝ) (_hu : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1) (T : ℕ) (B : ℝ)
    (hB : ∀ M, T ≤ M → ∑ n ∈ Ioc T M, u n ≤ B) (M : ℕ) : ∑ n ∈ Icc 1 M, u n ≤ T + B := by
  have hcard : ∀ K : ℕ, ∑ n ∈ Icc 1 K, u n ≤ K := fun K => by
    calc ∑ n ∈ Icc 1 K, u n ≤ ∑ n ∈ Icc 1 K, (1:ℝ) := Finset.sum_le_sum (fun n _ => hu1 n)
      _ = K := by simp
  have hB0 : 0 ≤ B := by simpa using hB T le_rfl
  rcases le_or_gt M T with h | h
  · have hMT : (M:ℝ) ≤ T := by exact_mod_cast h
    linarith [hcard M]
  · have h2 := hcard T
    rw [Icc_one_eq_Ioc_zero] at h2 ⊢
    rw [← Finset.sum_Ioc_consecutive u (Nat.zero_le T) h.le]
    linarith [hB M h.le]

private lemma sum_inv_sq_le_sub_inv (T : ℕ) (hT : 1 ≤ T) (M : ℕ) (hM : T ≤ M) :
    ∑ n ∈ Ioc T M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / T - 1 / M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hTM ih =>
    rw [Finset.sum_Ioc_succ_top hTM]
    have hM : (0:ℝ) < M := Nat.cast_pos.mpr (by omega)
    have e : 1 / (M:ℝ) - 1 / ((M:ℝ) + 1) = 1 / ((M:ℝ) * ((M:ℝ) + 1)) := by
      rw [div_sub_div _ _ hM.ne' (by positivity)]
      ring
    have k : 1 / ((M:ℝ) + 1) ^ 2 ≤ 1 / ((M:ℝ) * ((M:ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    push_cast
    linarith

private lemma sum_geometric_add_last_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (T M : ℕ) (hM : T ≤ M) :
    ∑ i ∈ Ioc T M, r ^ i + r ^ M ≤ r ^ T := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hTM ih =>
    rw [Finset.sum_Ioc_succ_top hTM, pow_succ]
    have hp : 0 ≤ r ^ M := pow_nonneg hr0 M
    have hq := mul_le_mul_of_nonneg_left hr hp
    linarith

private lemma sum_min_prime_power_le (x : ℝ) (hx : 1 ≤ x) (p : ℕ) (hp : 2 ≤ p) (L : ℕ) :
    Real.log p * ∑ i ∈ Icc 1 L, min 1 (x / (p : ℝ) ^ i) ≤ Real.log x + 2 * Real.log p := by
  have hp0 : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hx0 : (0:ℝ) < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set T := ⌊Real.log x / Real.log p⌋₊ + 1 with hT
  have hTlt : Real.log x / Real.log p < (T:ℝ) := by
    rw [hT]
    push_cast
    exact Nat.lt_floor_add_one _
  have hTle : (T:ℝ) - 1 ≤ Real.log x / Real.log p := by
    rw [hT]
    push_cast
    linarith [Nat.floor_le (div_nonneg hlx hlp.le)]
  have hTlog : ((T:ℝ) - 1) * Real.log p ≤ Real.log x := (le_div_iff₀ hlp).mp hTle
  have hxT : x ≤ (p:ℝ) ^ T := by
    have h1 : Real.log x < Real.log ((p:ℝ) ^ T) := by
      rw [Real.log_pow]
      rwa [div_lt_iff₀ hlp] at hTlt
    exact ((Real.log_lt_log_iff hx0 (by positivity)).mp h1).le
  have hr0 : (0:ℝ) ≤ 1 / p := by positivity
  have hr : (1:ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp0
  have htail : ∀ M, T ≤ M → ∑ i ∈ Ioc T M, min 1 (x / (p:ℝ) ^ i) ≤ 1 := by
    intro M hM
    have hg := sum_geometric_add_last_le (1 / (p:ℝ)) hr0 hr T M hM
    have hpos : (0:ℝ) ≤ (1 / (p:ℝ)) ^ M := pow_nonneg hr0 M
    calc ∑ i ∈ Ioc T M, min 1 (x / (p:ℝ) ^ i) ≤ ∑ i ∈ Ioc T M, x * (1 / (p:ℝ)) ^ i :=
          Finset.sum_le_sum (fun i _ => (min_le_right _ _).trans
            (le_of_eq (by rw [one_div_pow, mul_one_div])))
      _ = x * ∑ i ∈ Ioc T M, (1 / (p:ℝ)) ^ i := by rw [Finset.mul_sum]
      _ ≤ x * (1 / (p:ℝ)) ^ T := mul_le_mul_of_nonneg_left (by linarith) hx0.le
      _ = x / (p:ℝ) ^ T := by rw [one_div_pow, mul_one_div]
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hxT
  have hsplit := sum_truncated_le_cutoff_add_tail (fun i => min 1 (x / (p:ℝ) ^ i))
    (fun i => le_min zero_le_one (div_nonneg hx0.le (by positivity)))
    (fun i => min_le_left _ _) T 1 htail L
  have hmul := mul_le_mul_of_nonneg_left hsplit hlp.le
  linarith

lemma sum_min_square_le (x : ℝ) (hx : 1 ≤ x) (M : ℕ) :
    ∑ m ∈ Icc 1 M, min 1 (x / (m : ℝ) ^ 2) ≤ 3 * Real.sqrt x := by
  have hs1 : 1 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    rwa [Real.sqrt_one] at h
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hT1 : 1 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hs1)
  have hTgt : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hTpos : (0:ℝ) < ⌊Real.sqrt x⌋₊ := Nat.cast_pos.mpr (by omega)
  have hT1' : (1:ℝ) ≤ ⌊Real.sqrt x⌋₊ := by exact_mod_cast hT1
  have h2T : Real.sqrt x ≤ 2 * (⌊Real.sqrt x⌋₊ : ℝ) := by linarith
  have htail : ∀ K, ⌊Real.sqrt x⌋₊ ≤ K →
      ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, min 1 (x / (m:ℝ) ^ 2) ≤ 2 * Real.sqrt x := by
    intro K hK
    have h1 := sum_inv_sq_le_sub_inv ⌊Real.sqrt x⌋₊ hT1 K hK
    have hK0 : (0:ℝ) ≤ 1 / (K:ℝ) := by positivity
    calc ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, min 1 (x / (m:ℝ) ^ 2)
        ≤ ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, x * (1 / (m:ℝ) ^ 2) :=
          Finset.sum_le_sum (fun m _ => (min_le_right _ _).trans (le_of_eq (by rw [mul_one_div])))
      _ = x * ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, 1 / (m:ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ x * (1 / (⌊Real.sqrt x⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ 2 * Real.sqrt x := by
          rw [mul_one_div, div_le_iff₀ hTpos]
          nlinarith [mul_le_mul_of_nonneg_left h2T (Real.sqrt_nonneg x)]
  have hs := sum_truncated_le_cutoff_add_tail (fun m => min 1 (x / (m:ℝ) ^ 2))
    (fun m => le_min zero_le_one (div_nonneg (by linarith) (by positivity)))
    (fun m => min_le_left _ _) ⌊Real.sqrt x⌋₊ (2 * Real.sqrt x) htail M
  have hTle : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  linarith

private lemma primePowerSum_le_log_mul_sum_min {x : ℝ} (hx0 : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    sP (cN x) N p ≤ Real.log p * ∑ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) := by
  have hp2 : 2 ≤ p := hp.two_le
  have key : ∀ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
      ∃ k ∈ Icc 1 N, p ^ k = n := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_, hnN⟩, hpp, hmin⟩ := hn
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    rw [hq.pow_minFac hk.ne'] at hmin
    subst hmin
    refine ⟨k, Finset.mem_Icc.2 ⟨hk, ?_⟩, rfl⟩
    exact ((Nat.lt_pow_self (by omega : 1 < q)).le).trans hnN
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  unfold sP
  calc ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), cN x n
      = ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
          Real.log p * min 1 (x / (n : ℝ)) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        obtain ⟨k, hk, rfl⟩ := key n hn
        have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
        rw [cN, ArithmeticFunction.vonMangoldt_apply_pow hk0,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ ≤ ∑ n ∈ (Icc 1 N).image (fun k => p ^ k), Real.log p * min 1 (x / (n : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_
        · intro n hn
          obtain ⟨k, hk, rfl⟩ := key n hn
          exact Finset.mem_image.2 ⟨k, hk, rfl⟩
        · exact mul_nonneg hlogp (le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg _)))
    _ = ∑ k ∈ Icc 1 N, Real.log p * min 1 (x / (p : ℝ) ^ k) := by
        rw [Finset.sum_image fun a _ b _ h => Nat.pow_right_injective hp2 h]
        push_cast
        rfl
    _ = _ := (Finset.mul_sum _ _ _).symm

private lemma sum_min_le_div {x : ℝ} (hx0 : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    ∑ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) ≤ 2 * (x / p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  set r : ℝ := 1 / p with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ≤ 1 / 2 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hterm : ∀ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) ≤ x * r ^ i := by
    intro i _
    refine (min_le_right _ _).trans (le_of_eq ?_)
    rw [hr, one_div_pow, mul_one_div]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, mul_zero]
    positivity
  · have h1 := sum_geometric_add_last_le r hr0 hr2 1 N hN
    simp only [pow_one] at h1
    have hsplit : ∑ i ∈ Icc 1 N, r ^ i = r + ∑ i ∈ Ioc 1 N, r ^ i := by
      rw [Icc_one_eq_Ioc_zero, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hN]
      simp
    have hle : ∑ i ∈ Icc 1 N, r ^ i ≤ 2 * r := by
      rw [hsplit]
      linarith [pow_nonneg hr0 N]
    calc x * ∑ i ∈ Icc 1 N, r ^ i ≤ x * (2 * r) := mul_le_mul_of_nonneg_left hle hx0
      _ = 2 * (x / p) := by rw [hr]; ring

/-- A single prime-base progression contributes at most `3 log y`. -/
theorem exists_primePowerSum_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N p : ℕ, sP (cN y) N p ≤ C * Real.log y := by
  refine ⟨3, by norm_num, fun y hy N p => ?_⟩
  have hy0 : 0 < y := by linarith
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  by_cases hp : p.Prime
  · have h1 := primePowerSum_le_log_mul_sum_min hy0.le N hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    rcases le_total (p : ℝ) y with hpy | hpy
    · have h2 := sum_min_prime_power_le y (by linarith) p hp.two_le N
      have h3 : Real.log p ≤ Real.log y := Real.log_le_log hp0 hpy
      linarith
    · have h2 := mul_le_mul_of_nonneg_left (sum_min_le_div hy0.le N hp) hlogp
      have he : Real.exp 1 ≤ y := by linarith [Real.exp_one_lt_d9]
      have h4 : Real.log p / p ≤ Real.log y / y :=
        Real.log_div_self_antitoneOn he (le_trans he hpy) hpy
      have h5 : Real.log p * (2 * (y / p)) ≤ 2 * Real.log y := by
        have e : Real.log p * (2 * (y / p)) = 2 * y * (Real.log p / p) := by ring
        rw [e]
        calc 2 * y * (Real.log p / p) ≤ 2 * y * (Real.log y / y) := by gcongr
          _ = 2 * Real.log y := by field_simp
      linarith
  · have h0 : sP (cN y) N p = 0 := by
      unfold sP
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_filter] at hn
      obtain ⟨_, hpp, hmin⟩ := hn
      exact absurd (hmin ▸ Nat.minFac_prime hpp.ne_one) hp
    rw [h0]
    positivity

theorem sP_cN_le_log_div (y : ℝ) (hy : 0 ≤ y) (N p : ℕ) (hp : p.Prime) :
    sP (cN y) N p ≤ 2 * y * Real.log p / p := by
  calc sP (cN y) N p ≤ Real.log p * ∑ i ∈ Icc 1 N, min 1 (y / (p : ℝ) ^ i) :=
          primePowerSum_le_log_mul_sum_min hy N hp
    _ ≤ Real.log p * (2 * (y / p)) :=
          mul_le_mul_of_nonneg_left (sum_min_le_div hy N hp)
            (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    _ = _ := by ring

/-- Mertens' bound gives an upper bound for the mass of the truncated coefficients. -/
theorem sum_cN_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y Z : ℝ, 0 ≤ y → 2 ≤ Z →
      ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n ≤ C * y * Real.log Z := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ chebyshevConstant / Real.log 2 := div_nonneg chebyshevConstant_pos.le hlog2.le
  refine ⟨1 + chebyshevConstant / Real.log 2, add_pos_of_pos_of_nonneg one_pos hC, fun y Z hy hZ => ?_⟩
  have hZ0 : 0 < Z := by linarith
  have hfloor : 1 ≤ ⌊Z⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hlog : Real.log (⌊Z⌋₊ : ℝ) ≤ Real.log Z :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊Z⌋₊ from hfloor)) (Nat.floor_le hZ0.le)
  have hM := (abs_le.mp (RHTower.Mertens.mertens_first ⌊Z⌋₊ hfloor)).2
  have hconstant : chebyshevConstant ≤ (chebyshevConstant / Real.log 2) * Real.log Z := by
    calc chebyshevConstant = chebyshevConstant / Real.log 2 * Real.log 2 :=
            (div_mul_cancel₀ _ hlog2.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hZ) hC
  calc ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n
      ≤ ∑ n ∈ Icc 1 ⌊Z⌋₊, y * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        unfold cN
        calc ArithmeticFunction.vonMangoldt n * min 1 (y / n)
            ≤ ArithmeticFunction.vonMangoldt n * (y / n) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) ArithmeticFunction.vonMangoldt_nonneg
          _ = y * (ArithmeticFunction.vonMangoldt n / n) := by ring
    _ = y * ∑ n ∈ Icc 1 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
          (Finset.mul_sum _ _ _).symm
    _ ≤ y * ((1 + chebyshevConstant / Real.log 2) * Real.log Z) := by
        refine mul_le_mul_of_nonneg_left ?_ hy
        change (∑ n ∈ Icc 1 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
          Real.log (⌊Z⌋₊ : ℝ) ≤ chebyshevConstant at hM
        linarith
    _ = _ := by ring

end QH
