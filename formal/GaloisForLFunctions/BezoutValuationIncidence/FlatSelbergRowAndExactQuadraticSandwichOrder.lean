import GaloisForLFunctions.BezoutValuationIncidence.QuadraticOrderWindowDirichletAndDissipation
import GaloisForLFunctions.RHTower.PMRamanujanPeriodDiagonal
import GaloisForLFunctions.RHTower.FareySawtoothMeanSquare

/-!
# The flat Selberg row and the exact quadratic order of the window sandwich

At a common return `k = N!` every modulus divides `k`, so the response is `Σ_{q ≤ N} φ(q) Y(q)`:
each Ramanujan sum takes its maximal value `φ(q)`. The **flat Selberg row**, with `Y(q) = 1` for
`2 ≤ q ≤ N` and `Y(1) = 0`, therefore has mean zero, variance `Φ(N) - 1` and the spike
`s(N!) = Φ(N) - 1`, where `Φ(N) = Σ_{q ≤ N} φ(q)`. It attains the pointwise bound
`(s(k) - H)² ≤ (Φ(N) - 1) V` with equality, so `Φ(N) - 1` is the exact pointwise constant.

The one-point window at the spike forces every window sandwich constant to be at least
`Φ(N) - 2`. From `Σ_{k ≤ N} Φ(⌊N/k⌋) = N(N+1)/2` and `2Φ(y) ≤ y(y+1)` one gets
`Φ(N) ≥ N²/8 + N - (N/2) H_N`. With the admissible constant `2N² - 1`, the optimal window
sandwich constant lies between `N²/8 + N - (N/2) H_N - 2` and `2N² - 1`: it has exact order `N²`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The response at a common return -/

/-- At `N!` every Ramanujan sum is maximal: `s(N!) = Σ_{q ≤ N} φ(q) Y(q)`. -/
theorem sieveSeq_factorial_eq_sum_totient_mul (N : ℕ) (c : ℕ → ℝ) :
    sieveSeq N c N.factorial = ∑ q ∈ Icc 1 N, (q.totient : ℝ) * selbergMultiplesCoord N c q := by
  unfold sieveSeq selbergMultiplesCoord
  rw [filter_true_of_mem fun d hd => Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2]
  simp_rw [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hdiv : (Icc 1 N).filter (fun q => q ∣ d) = d.divisors := by
    ext q
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hqd⟩
      exact ⟨hqd, hd0.ne'⟩
    · rintro ⟨hqd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hqd hd0, (Nat.le_of_dvd hd0 hqd).trans (mem_Icc.mp hd).2⟩,
        hqd⟩
  rw [← sum_filter, hdiv, ← sum_mul, ← Nat.cast_sum, Nat.sum_totient]
  field_simp

/-! ## §2. The flat Selberg row -/

/-- The flat Selberg row: `Y(q) = 1` for `2 ≤ q ≤ N`, `Y(1) = 0`. -/
def flatSelbergRow (N : ℕ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (fun q => if 2 ≤ q then 1 else 0) N

theorem selbergMultiplesCoord_flatSelbergRow {N q : ℕ} (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (flatSelbergRow N) q = if 2 ≤ q then 1 else 0 :=
  RHTower.pmRamanujanResidueCoeff_multiples _ (mem_Icc.mp hq).1 (mem_Icc.mp hq).2

theorem finiteHarmonicSum_flatSelbergRow {N : ℕ} (hN : 1 ≤ N) :
    finiteHarmonicSum N (flatSelbergRow N) = 0 := by
  have h := selbergMultiplesCoord_flatSelbergRow (N := N) (mem_Icc.mpr ⟨le_rfl, hN⟩)
  simp only [selbergMultiplesCoord, one_dvd, filter_true] at h
  rw [finiteHarmonicSum, h]
  simp

theorem sum_Icc_two_totient {N : ℕ} (hN : 1 ≤ N) :
    ∑ q ∈ Icc 2 N, (q.totient : ℝ) = (cyclotomicIncidenceOrder N : ℝ) - 1 := by
  unfold cyclotomicIncidenceOrder
  rw [Icc_eq_cons_Ioc hN, sum_cons]
  have hIoc : Ioc 1 N = Icc 2 N := by
    ext e
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [hIoc]
  push_cast
  simp

theorem sieveVariance_flatSelbergRow {N : ℕ} (hN : 1 ≤ N) :
    sieveVariance N (flatSelbergRow N) = (cyclotomicIncidenceOrder N : ℝ) - 1 := by
  unfold sieveVariance
  rw [← sum_Icc_two_totient hN]
  refine sum_congr rfl fun q hq => ?_
  have hq' := mem_Icc.mp hq
  rw [selbergMultiplesCoord_flatSelbergRow (mem_Icc.mpr ⟨by omega, hq'.2⟩), if_pos hq'.1]
  ring

theorem sieveSeq_flatSelbergRow_factorial {N : ℕ} (hN : 1 ≤ N) :
    sieveSeq N (flatSelbergRow N) N.factorial = (cyclotomicIncidenceOrder N : ℝ) - 1 := by
  rw [sieveSeq_factorial_eq_sum_totient_mul, Icc_eq_cons_Ioc hN, sum_cons,
    selbergMultiplesCoord_flatSelbergRow (mem_Icc.mpr ⟨le_rfl, hN⟩), if_neg (by norm_num),
    mul_zero, zero_add, ← sum_Icc_two_totient hN]
  have hIoc : Ioc 1 N = Icc 2 N := by
    ext e
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [hIoc]
  refine sum_congr rfl fun q hq => ?_
  have hq' := mem_Icc.mp hq
  rw [selbergMultiplesCoord_flatSelbergRow (mem_Icc.mpr ⟨by omega, hq'.2⟩), if_pos hq'.1,
    mul_one]

/-- **The pointwise constant is exact.** The flat row attains `(s - H)² = (Φ(N) - 1) V`. -/
theorem flatSelbergRow_attains_pointwise_bound {N : ℕ} (hN : 1 ≤ N) :
    (sieveSeq N (flatSelbergRow N) N.factorial - finiteHarmonicSum N (flatSelbergRow N)) ^ 2 =
      ((cyclotomicIncidenceOrder N : ℝ) - 1) * sieveVariance N (flatSelbergRow N) := by
  rw [sieveSeq_flatSelbergRow_factorial hN, finiteHarmonicSum_flatSelbergRow hN,
    sieveVariance_flatSelbergRow hN]
  ring

/-! ## §3. The sandwich constant has exact order `N²` -/

theorem one_lt_cyclotomicIncidenceOrder {N : ℕ} (hN : 2 ≤ N) :
    (1 : ℝ) < cyclotomicIncidenceOrder N := by
  have h := sum_Icc_two_totient (N := N) (by omega)
  have h2 : (1 : ℝ) ≤ ∑ q ∈ Icc 2 N, (q.totient : ℝ) := by
    have hmem : 2 ∈ Icc 2 N := mem_Icc.mpr ⟨le_rfl, hN⟩
    calc (1 : ℝ) = ((2 : ℕ).totient : ℝ) := by norm_num
      _ ≤ _ := single_le_sum (fun q _ => Nat.cast_nonneg _) hmem
  linarith

/-- **Every window sandwich constant is at least `Φ(N) - 2`.** -/
theorem cyclotomicIncidenceOrder_sub_two_le_of_isWindowSandwichConstant {N : ℕ} (hN : 2 ≤ N)
    {S : ℝ} (hS : IsWindowSandwichConstant N S) :
    (cyclotomicIncidenceOrder N : ℝ) - 2 ≤ S := by
  have hN1 : 1 ≤ N := by omega
  have h := hS (N.factorial - 1) 1 (flatSelbergRow N) 0
  have hP : N.factorial - 1 + 1 = N.factorial := Nat.sub_add_cancel (Nat.factorial_pos N)
  rw [hP, Icc_self, sum_singleton, sub_zero, sieveSeq_flatSelbergRow_factorial hN1,
    finiteHarmonicSum_flatSelbergRow hN1, sieveVariance_flatSelbergRow hN1] at h
  have hΦ := one_lt_cyclotomicIncidenceOrder hN
  set x := (cyclotomicIncidenceOrder N : ℝ) - 1
  have hx : 0 < x := by linarith
  have h' : x ^ 2 - x ≤ S * x := by
    have := (abs_le.mp h).2
    simp only [Nat.cast_one, one_mul, zero_pow two_ne_zero, zero_add, sub_zero] at this
    linarith
  have : x - 1 ≤ S := by
    by_contra hlt
    push Not at hlt
    nlinarith
  linarith

theorem sum_Ioc_id_mul_two (N : ℕ) : (∑ m ∈ Ioc 0 N, m) * 2 = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N), add_mul, ih]
    ring

theorem sum_Ioc_one_div_sq_le (N : ℕ) : ∑ k ∈ Ioc 1 N, 1 / (k : ℝ) ^ 2 ≤ 3 / 4 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have : Ioc 1 N = ∅ := by
      ext k
      simp only [mem_Ioc, notMem_empty, iff_false]
      omega
    rw [this, sum_empty]
    norm_num
  · -- `1/k² ≤ 1/(k-1) - 1/k` for `k ≥ 3`
    have hsplit : Ioc 1 N = insert 2 (Ioc 2 N) := by
      ext k
      simp only [mem_Ioc, mem_insert]
      omega
    rw [hsplit, sum_insert (by simp)]
    have htel : ∀ M : ℕ, ∑ k ∈ Ioc 2 M, 1 / (k : ℝ) ^ 2 ≤ 1 / 2 := by
      intro M
      have hM : ∀ M : ℕ, 2 ≤ M → ∑ k ∈ Ioc 2 M, 1 / (k : ℝ) ^ 2 ≤ 1 / 2 - 1 / (M : ℝ) := by
        intro M hM
        induction M, hM using Nat.le_induction with
        | base => norm_num
        | succ M hM ih =>
          rw [sum_Ioc_succ_top (by omega)]
          have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
          have key : 1 / ((M : ℝ) + 1) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M : ℝ) + 1) := by
            rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
              (by positivity)]
            nlinarith
          push_cast
          linarith
      rcases Nat.lt_or_ge M 2 with hM2 | hM2
      · have : Ioc 2 M = ∅ := by
          ext k
          simp only [mem_Ioc, notMem_empty, iff_false]
          omega
        rw [this, sum_empty]
        norm_num
      · have := hM M hM2
        have : (0 : ℝ) ≤ 1 / M := by positivity
        linarith
    have := htel N
    have h4 : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 1 / 4 := by norm_num
    linarith

/-- **Quadratic lower bound for the totient sum.** `Φ(N) ≥ N²/8 + N - (N/2) H_N`. -/
theorem cyclotomicIncidenceOrder_ge (N : ℕ) :
    (N : ℝ) ^ 2 / 8 + N - (N : ℝ) / 2 * (harmonic N : ℝ) ≤ cyclotomicIncidenceOrder N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cyclotomicIncidenceOrder]
  have hId := RHTower.sum_sum_totient_div_eq N
  have hΦ : ∀ y : ℕ, ∑ q ∈ Ioc 0 y, Nat.totient q = cyclotomicIncidenceOrder y := by
    intro y
    unfold cyclotomicIncidenceOrder
    congr 1
  simp_rw [hΦ] at hId
  have hgauss := sum_Ioc_id_mul_two N
  -- the `k = 1` term
  have hsplit : Ioc 0 N = insert 1 (Ioc 1 N) := by
    ext k
    simp only [mem_Ioc, mem_insert]
    omega
  have hId2 : (∑ k ∈ Ioc 0 N, cyclotomicIncidenceOrder (N / k)) * 2 = N * (N + 1) := by
    rw [hId]
    exact hgauss
  rw [hsplit, sum_insert (by simp), Nat.div_one] at hId2
  have hIdR : (cyclotomicIncidenceOrder N : ℝ) +
      ∑ k ∈ Ioc 1 N, (cyclotomicIncidenceOrder (N / k) : ℝ) = (N : ℝ) * (N + 1) / 2 := by
    have h1 : ((cyclotomicIncidenceOrder N + ∑ k ∈ Ioc 1 N, cyclotomicIncidenceOrder (N / k) : ℕ) :
        ℝ) * 2 = ((N * (N + 1) : ℕ) : ℝ) := by
      exact_mod_cast hId2
    push_cast at h1
    linarith
  -- each tail term is at most `(N/k)² / 2 + (N/k) / 2`
  have htail : ∑ k ∈ Ioc 1 N, (cyclotomicIncidenceOrder (N / k) : ℝ) ≤
      (N : ℝ) ^ 2 / 2 * ∑ k ∈ Ioc 1 N, 1 / (k : ℝ) ^ 2 +
        (N : ℝ) / 2 * ∑ k ∈ Ioc 1 N, 1 / (k : ℝ) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun k hk => ?_
    have hk0 : 0 < k := by have := (mem_Ioc.mp hk).1; omega
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have h2 : 2 * (cyclotomicIncidenceOrder (N / k) : ℝ) ≤ ((N / k : ℕ) : ℝ) * ((N / k : ℕ) + 1) := by
      exact_mod_cast two_mul_cyclotomicIncidenceOrder_le (N / k)
    have hq : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
    have hq0 : (0 : ℝ) ≤ ((N / k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hprod : ((N / k : ℕ) : ℝ) * ((N / k : ℕ) + 1) ≤ (N / k : ℝ) * (N / k + 1) := by
      nlinarith
    have hval : (N : ℝ) ^ 2 / 2 * (1 / (k : ℝ) ^ 2) + (N : ℝ) / 2 * (1 / (k : ℝ)) =
        (N / k : ℝ) * (N / k + 1) / 2 := by
      field_simp
    rw [hval]
    linarith
  have hsq := sum_Ioc_one_div_sq_le N
  have hharm : ∑ k ∈ Ioc 1 N, 1 / (k : ℝ) = (harmonic N : ℝ) - 1 := by
    rw [_root_.harmonic_eq_sum_Icc, Icc_eq_cons_Ioc (by omega : 1 ≤ N), sum_cons]
    push_cast
    ring_nf
  rw [hharm] at htail
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hsq hN0
  nlinarith

/-- **The optimal window sandwich constant has exact order `N²`.** `2N² - 1` is admissible, and
every admissible constant is at least `N²/8 + N - (N/2) H_N - 2`. -/
theorem windowSandwichConstant_exact_quadratic_order {N : ℕ} (hN : 2 ≤ N) :
    IsWindowSandwichConstant N (2 * (N : ℝ) ^ 2 - 1) ∧
      ∀ S : ℝ, IsWindowSandwichConstant N S →
        (N : ℝ) ^ 2 / 8 + N - (N : ℝ) / 2 * (harmonic N : ℝ) - 2 ≤ S :=
  ⟨isWindowSandwichConstant_two_mul_sq hN, fun _ hS => by
    have h1 := cyclotomicIncidenceOrder_sub_two_le_of_isWindowSandwichConstant hN hS
    have h2 := cyclotomicIncidenceOrder_ge N
    linarith⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
