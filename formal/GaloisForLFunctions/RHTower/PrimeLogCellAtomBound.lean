import GaloisForLFunctions.RHTower.PrimeSquareRootGapClustering
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldChebyshevErrorIncrement
import GaloisForLFunctions.RHTower.Sieve.MaynardLocalPrimePowerLeakage
import GaloisForLFunctions.HTGeometry.WindowRpowIntegral

/-!
# Actual prime-power mass in short consecutive-prime cells

Every von Mangoldt atom in `(p_n,p_{n+1}]` is retained, including the right
endpoint prime. Local proper-power leakage bounds its critical weight. When
the additive gap is at most `sqrt p_n`, the total weight is at most
`10 / log 2 * (log p_n)^2 / p_n^(1/4)`, which tends to zero.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace RHTower

def primeLogCellAtomMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (nthPrimeSubtype N : ℕ) (nthPrimeSubtype (N + 1) : ℕ),
    ArithmeticFunction.vonMangoldt n / Real.sqrt n

theorem primeLogCellAtomMass_nonneg (N : ℕ) : 0 ≤ primeLogCellAtomMass N := by
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)

theorem primeLogCellAtomMass_le_local_leakage (N : ℕ) :
    primeLogCellAtomMass N ≤
      (Real.log (nthPrimeSubtype (N + 1) : ℝ) +
        (Real.log (nthPrimeSubtype (N + 1) : ℝ) / Real.log 2) *
          (Real.sqrt (xiHeatCassiniOrderedPrimeGap N) + 1) *
            Real.log (nthPrimeSubtype (N + 1) : ℝ)) /
        Real.sqrt (nthPrimeSubtype N : ℝ) := by
  have hp := nthPrimeSubtype_pos N
  have hpn := (nthPrimeSubtype N).prop.two_le
  have hpq := nthPrimeSubtype_strictMono (Nat.lt_succ_self N)
  have hpg : (nthPrimeSubtype N : ℝ) ≤ (nthPrimeSubtype (N + 1) : ℝ) := by
    exact_mod_cast hpq.le
  have hgap : 1 ≤ (nthPrimeSubtype (N + 1) : ℝ) - (nthPrimeSubtype N : ℝ) := by
    have hn : (nthPrimeSubtype N : ℕ) + 1 ≤ (nthPrimeSubtype (N + 1) : ℕ) := hpq
    have hr : (nthPrimeSubtype N : ℝ) + 1 ≤ (nthPrimeSubtype (N + 1) : ℝ) := by
      exact_mod_cast hn
    linarith
  have hmass : Chebyshev.psi (nthPrimeSubtype (N + 1) : ℝ) -
      Chebyshev.psi (nthPrimeSubtype N : ℝ) =
      ∑ n ∈ Finset.Ioc (nthPrimeSubtype N : ℕ) (nthPrimeSubtype (N + 1) : ℕ),
        ArithmeticFunction.vonMangoldt n := by
    have hsplit := Finset.sum_Ioc_consecutive
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))
      (Nat.zero_le (nthPrimeSubtype N : ℕ)) hpq.le
    rw [Chebyshev.psi, Chebyshev.psi]
    simp only [Nat.floor_natCast]
    rw [← hsplit]
    ring
  have hle := Sieve.chebyshevPsi_window_le_theta_window_add_local_primePower
    (by exact_mod_cast hpn) hpg hgap
  rw [chebyshevTheta_nthPrime_succ_sub, hmass] at hle
  calc
    primeLogCellAtomMass N ≤
        (∑ n ∈ Finset.Ioc (nthPrimeSubtype N : ℕ) (nthPrimeSubtype (N + 1) : ℕ),
          ArithmeticFunction.vonMangoldt n) / Real.sqrt (nthPrimeSubtype N : ℝ) := by
      rw [primeLogCellAtomMass, Finset.sum_div]
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
        (Real.sqrt_pos.mpr hp) (Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le))
    _ ≤ _ := div_le_div_of_nonneg_right hle (Real.sqrt_nonneg _)

def primeLogCellAtomBudget (x : ℝ) : ℝ :=
  (10 / Real.log 2) * Real.log x ^ 2 / Real.sqrt (Real.sqrt x)

theorem primeLogCellAtomMass_le_budget (N : ℕ)
    (hgap : xiHeatCassiniOrderedPrimeGap N ≤ Real.sqrt (nthPrimeSubtype N : ℝ)) :
    primeLogCellAtomMass N ≤ primeLogCellAtomBudget (nthPrimeSubtype N : ℝ) := by
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  let L := Real.log p
  let t := Real.sqrt (Real.sqrt p)
  have hp2 : 2 ≤ p := by
    dsimp only [p]
    exact_mod_cast (nthPrimeSubtype N).prop.two_le
  have hp : 0 < p := by linarith
  have hq : 0 < q := nthPrimeSubtype_pos (N + 1)
  have hq2 : q ≤ 2 * p := by
    dsimp only [p, q]
    exact_mod_cast nthPrimeSubtype_succ_le_two_mul N
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hp2
  have hL0 : 0 ≤ L := hlog2.le.trans hL
  have ht1 : 1 ≤ t := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (by linarith))
  have ht : 0 < t := by linarith
  have htsq : t ^ 2 = Real.sqrt p := Real.sq_sqrt (Real.sqrt_nonneg p)
  have hlogq : Real.log q ≤ 2 * L := by
    have h := Real.log_le_log hq hq2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at h
    linarith
  have hlogq0 : 0 ≤ Real.log q := by
    apply Real.log_nonneg
    dsimp only [q]
    exact_mod_cast (nthPrimeSubtype (N + 1)).prop.one_lt.le
  have hs : Real.sqrt (xiHeatCassiniOrderedPrimeGap N) + 1 ≤ 2 * t := by
    have h := Real.sqrt_le_sqrt hgap
    change Real.sqrt (xiHeatCassiniOrderedPrimeGap N) ≤ t at h
    linarith
  have hprod : (Real.log q / Real.log 2) *
      (Real.sqrt (xiHeatCassiniOrderedPrimeGap N) + 1) * Real.log q ≤
        (2 * L / Real.log 2) * (2 * t) * (2 * L) :=
    mul_le_mul (mul_le_mul (div_le_div_of_nonneg_right hlogq hlog2.le) hs
      (by positivity) (by positivity)) hlogq hlogq0 (by positivity)
  have hfirst : 2 * L ≤ (2 / Real.log 2) * t * L ^ 2 := by
    have hLL : Real.log 2 * L ≤ L ^ 2 := by nlinarith
    have hpow := mul_le_mul_of_nonneg_right ht1 (sq_nonneg L)
    calc
      2 * L ≤ (2 * t * L ^ 2) / Real.log 2 :=
        (le_div_iff₀ hlog2).2 (by nlinarith only [hLL, hpow])
      _ = _ := by ring
  have hnum : Real.log q + (Real.log q / Real.log 2) *
      (Real.sqrt (xiHeatCassiniOrderedPrimeGap N) + 1) * Real.log q ≤
        (10 / Real.log 2) * t * L ^ 2 := by
    calc
      _ ≤ (2 / Real.log 2) * t * L ^ 2 +
          (2 * L / Real.log 2) * (2 * t) * (2 * L) :=
        add_le_add (hlogq.trans hfirst) hprod
      _ = _ := by ring
  calc
    primeLogCellAtomMass N ≤
        (Real.log q + (Real.log q / Real.log 2) *
          (Real.sqrt (xiHeatCassiniOrderedPrimeGap N) + 1) * Real.log q) / Real.sqrt p :=
      primeLogCellAtomMass_le_local_leakage N
    _ ≤ ((10 / Real.log 2) * t * L ^ 2) / Real.sqrt p :=
      div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg p)
    _ = primeLogCellAtomBudget p := by
      change _ = (10 / Real.log 2) * L ^ 2 / t
      rw [← htsq]
      field_simp

theorem tendsto_primeLogCellAtomBudget_zero :
    Tendsto primeLogCellAtomBudget atTop (nhds 0) := by
  have h := (HTGeometry.tendsto_logPow_div_rpow
    (by norm_num : (0 : ℝ) < 1 / 4) 2).const_mul (10 / Real.log 2)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  unfold primeLogCellAtomBudget
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num
  ring

/-- Cofinal cells have arbitrarily small normalized geometric and full atom budgets. -/
theorem exists_primeLogCell_small_budgets {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      xiHeatCassiniOrderedPrimeGap n / Real.sqrt (nthPrimeSubtype n : ℝ) < ε ∧
      primeLogCellAtomMass n < ε := by
  have hp : Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_primeLogCellAtomBudget_zero.comp hp).eventually (Iio_mem_nhds hε))
  obtain ⟨n, hn, hg⟩ := exists_nthPrime_gap_div_sqrt_lt (lt_min hε zero_lt_one) (max N M)
  have hg' : xiHeatCassiniOrderedPrimeGap n / Real.sqrt (nthPrimeSubtype n : ℝ) < min ε 1 := hg
  refine ⟨n, (le_max_left _ _).trans hn, hg'.trans_le (min_le_left _ _), ?_⟩
  have hgap : xiHeatCassiniOrderedPrimeGap n ≤ Real.sqrt (nthPrimeSubtype n : ℝ) := by
    have h := (div_lt_iff₀ (Real.sqrt_pos.mpr (nthPrimeSubtype_pos n))).mp
      (hg'.trans_le (min_le_right _ _))
    simpa only [one_mul] using h.le
  exact (primeLogCellAtomMass_le_budget n hgap).trans_lt
    (hM n ((le_max_right _ _).trans hn))

end RHTower
