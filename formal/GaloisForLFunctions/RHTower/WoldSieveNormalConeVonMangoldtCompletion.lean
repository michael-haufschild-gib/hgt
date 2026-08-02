import GaloisForLFunctions.RHTower.WoldSieveNormalConeVonMangoldt
import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.HTGeometry.FredholmDeterminantInfinite
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Order.Filter.AtTopBot.Finset

open scoped BigOperators

namespace RHTower

noncomputable section

private def woldSievePrimeFactor (p : ℕ) (h : ℝ) : ℝ :=
  1 - Real.exp (-h * Real.log p)

private theorem contDiff_woldSievePrimeFactor (p : ℕ) :
    ContDiff ℝ ⊤ (woldSievePrimeFactor p) := by
  unfold woldSievePrimeFactor
  fun_prop

private theorem contDiff_woldSieveNormalFactor (S : Finset ℕ) :
    ContDiff ℝ ⊤ (woldSieveNormalFactor S) := by
  unfold woldSieveNormalFactor
  fun_prop

private theorem woldSievePrimeFactor_zero (p : ℕ) :
    woldSievePrimeFactor p 0 = 0 := by
  simp [woldSievePrimeFactor]

private theorem iteratedDeriv_one_woldSievePrimeFactor_zero (p : ℕ) :
    iteratedDeriv 1 (woldSievePrimeFactor p) 0 = Real.log p := by
  rw [iteratedDeriv_succ, iteratedDeriv_zero]
  exact (hasDerivAt_woldSievePrimeFactor p).deriv

theorem iteratedDeriv_woldSieveNormalFactor_zero_of_lt_card
    (S : Finset ℕ) {j : ℕ} (hj : j < S.card) :
    iteratedDeriv j (woldSieveNormalFactor S) 0 = 0 := by
  classical
  induction S using Finset.induction_on generalizing j with
  | empty => simp at hj
  | @insert p S hp ih =>
      rw [Finset.card_insert_of_notMem hp] at hj
      have hfactor :
          woldSieveNormalFactor (insert p S) =
            woldSievePrimeFactor p * woldSieveNormalFactor S := by
        funext h
        simp [woldSieveNormalFactor, woldSievePrimeFactor, hp]
      rw [hfactor, iteratedDeriv_mul
        ((contDiff_woldSievePrimeFactor p).of_le le_top).contDiffAt
        ((contDiff_woldSieveNormalFactor S).of_le le_top).contDiffAt]
      apply Finset.sum_eq_zero
      intro i hi
      have hi_le : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      by_cases hi0 : i = 0
      · subst i
        simp [woldSievePrimeFactor_zero]
      · have hsub : j - i < S.card := by omega
        rw [ih hsub]
        ring

theorem iteratedDeriv_woldSieveNormalFactor_card (S : Finset ℕ) :
    iteratedDeriv S.card (woldSieveNormalFactor S) 0 =
      S.card.factorial * ∏ p ∈ S, Real.log p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [woldSieveNormalFactor]
  | @insert p S hp ih =>
      have hfactor :
          woldSieveNormalFactor (insert p S) =
            woldSievePrimeFactor p * woldSieveNormalFactor S := by
        funext h
        simp [woldSieveNormalFactor, woldSievePrimeFactor, hp]
      rw [Finset.card_insert_of_notMem hp, hfactor, iteratedDeriv_mul
        ((contDiff_woldSievePrimeFactor p).of_le le_top).contDiffAt
        ((contDiff_woldSieveNormalFactor S).of_le le_top).contDiffAt]
      rw [Finset.sum_eq_single 1]
      · have hsubeq : S.card + 1 - 1 = S.card := by omega
        rw [iteratedDeriv_one_woldSievePrimeFactor_zero, hsubeq, ih]
        simp only [Nat.choose_one_right]
        simp [Finset.prod_insert, hp, Nat.factorial_succ]
        ring
      · intro i hi hi1
        have hi_le : i ≤ S.card + 1 :=
          Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        by_cases hi0 : i = 0
        · subst i
          simp [woldSievePrimeFactor_zero]
        · have hsub : S.card + 1 - i < S.card := by omega
          rw [iteratedDeriv_woldSieveNormalFactor_zero_of_lt_card S hsub]
          ring
      · simp

theorem iteratedDeriv_woldIncidenceNormalFactor_zero_of_lt_omega
    (n : ℕ) {j : ℕ} (hj : j < n.primeFactors.card) :
    iteratedDeriv j (woldIncidenceNormalFactor n) 0 = 0 :=
  iteratedDeriv_woldSieveNormalFactor_zero_of_lt_card n.primeFactors hj

theorem iteratedDeriv_woldIncidenceNormalFactor_omega (n : ℕ) :
    iteratedDeriv n.primeFactors.card (woldIncidenceNormalFactor n) 0 =
      n.primeFactors.card.factorial *
        ∏ p ∈ n.primeFactors, Real.log p :=
  iteratedDeriv_woldSieveNormalFactor_card n.primeFactors

/-! ## Cofinal finite-prime coefficients -/

/-- Finite-prime incidence factor at coordinate `n`; only primes in `P`
which divide `n` act nontrivially. -/
def woldFiniteIncidenceNormalFactor (P : Finset ℕ) (n : ℕ) (h : ℝ) : ℝ :=
  woldSieveNormalFactor (P ∩ n.primeFactors) h

/-- First normal coefficient of the finite-prime Wold sieve at `n`. -/
def woldFiniteNormalCoefficient (P : Finset ℕ) (n : ℕ) : ℝ :=
  deriv (woldFiniteIncidenceNormalFactor P n) 0

theorem woldFiniteNormalCoefficient_eq_of_primeFactors_subset
    {P : Finset ℕ} {n : ℕ} (hsub : n.primeFactors ⊆ P) :
    woldFiniteNormalCoefficient P n = ArithmeticFunction.vonMangoldt n := by
  rw [woldFiniteNormalCoefficient]
  change deriv (woldSieveNormalFactor (P ∩ n.primeFactors)) 0 = _
  rw [Finset.inter_eq_right.mpr hsub]
  exact (hasDerivAt_woldIncidenceNormalFactor n).deriv

theorem tendsto_woldFiniteNormalCoefficient_atTop (n : ℕ) :
    Filter.Tendsto (fun P : Finset ℕ => woldFiniteNormalCoefficient P n)
      Filter.atTop (nhds (ArithmeticFunction.vonMangoldt n)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop n.primeFactors] with P hP
  exact (woldFiniteNormalCoefficient_eq_of_primeFactors_subset hP).symm

theorem woldFiniteNormalCoefficient_eq_log_of_incidence_eq_singleton
    {P : Finset ℕ} {n p : ℕ} (hinc : P ∩ n.primeFactors = {p}) :
    woldFiniteNormalCoefficient P n = Real.log p := by
  rw [woldFiniteNormalCoefficient]
  change deriv (woldSieveNormalFactor (P ∩ n.primeFactors)) 0 = _
  rw [hinc]
  exact (hasDerivAt_woldSieveNormalFactor_singleton p).deriv

theorem woldFiniteNormalCoefficient_eq_zero_of_card_ne_one
    {P : Finset ℕ} {n : ℕ} (hcard : (P ∩ n.primeFactors).card ≠ 1) :
    woldFiniteNormalCoefficient P n = 0 := by
  by_cases hnontrivial : (P ∩ n.primeFactors).Nontrivial
  · exact (hasDerivAt_woldSieveNormalFactor_of_nontrivial hnontrivial).deriv
  · have hle : (P ∩ n.primeFactors).card ≤ 1 := by
      exact Nat.le_of_not_gt fun hgt =>
        hnontrivial (Finset.one_lt_card.mp hgt)
    have hempty : P ∩ n.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [woldFiniteNormalCoefficient]
    change deriv (woldSieveNormalFactor (P ∩ n.primeFactors)) 0 = 0
    rw [hempty]
    change deriv (fun _ : ℝ => 1) 0 = 0
    exact (hasDerivAt_const (x := 0) (c := (1 : ℝ))).deriv

theorem woldFiniteNormalCoefficient_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ woldFiniteNormalCoefficient P n := by
  by_cases hcard : (P ∩ n.primeFactors).card = 1
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
    rw [woldFiniteNormalCoefficient_eq_log_of_incidence_eq_singleton hp]
    have hmem : p ∈ n.primeFactors := by
      rw [hp] at hcard
      have : p ∈ P ∩ n.primeFactors := by simp [hp]
      exact (Finset.mem_inter.mp this).2
    exact Real.log_nonneg (by
      have hpprime : p.Prime := (Nat.mem_primeFactors.mp hmem).1
      exact_mod_cast hpprime.one_lt.le)
  · rw [woldFiniteNormalCoefficient_eq_zero_of_card_ne_one hcard]

theorem woldFiniteNormalCoefficient_le_log
    (P : Finset ℕ) (n : ℕ) :
    woldFiniteNormalCoefficient P n ≤ Real.log n := by
  by_cases hcard : (P ∩ n.primeFactors).card = 1
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
    rw [woldFiniteNormalCoefficient_eq_log_of_incidence_eq_singleton hp]
    have hmemInter : p ∈ P ∩ n.primeFactors := by simp [hp]
    have hmem : p ∈ n.primeFactors := (Finset.mem_inter.mp hmemInter).2
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hmem).1
    have hpn : p ∣ n := (Nat.mem_primeFactors.mp hmem).2.1
    have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hmem).2.2
    have hpn_le : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
    exact Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < p by exact_mod_cast hpprime.pos)
      (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn0)
      (by exact_mod_cast hpn_le)
  · rw [woldFiniteNormalCoefficient_eq_zero_of_card_ne_one hcard]
    exact Real.log_natCast_nonneg n

theorem tendsto_woldRangeNormalCoefficient_atTop (n : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => woldFiniteNormalCoefficient (Finset.range N) n)
      Filter.atTop (nhds (ArithmeticFunction.vonMangoldt n)) :=
  (tendsto_woldFiniteNormalCoefficient_atTop n).comp
    Filter.tendsto_finset_range

/-! ## Reciprocal weighting and Hilbert--Schmidt realization -/

def woldFiniteWeightedCoefficient (N : ℕ) (sigma : ℝ) (n : ℕ) : ℝ :=
  woldFiniteNormalCoefficient (Finset.range N) n * (n : ℝ) ^ (-sigma)

def woldVonMangoldtWeightedCoefficient (sigma : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma)

private theorem summable_sq_weighted_of_le_log
    {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (halog : ∀ n, a n ≤ Real.log n)
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Summable (fun n : ℕ => ‖((a n * (n : ℝ) ^ (-sigma) : ℝ) : ℂ)‖ ^ 2) := by
  have hmajor :
      Summable (fun n : ℕ =>
        |Real.log n| ^ 2 * (n : ℝ) ^ (-(2 * sigma))) :=
    summable_abs_log_natCast_pow_mul_rpow_neg 2 (2 * sigma) (by linarith)
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hmajor
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : -sigma ≠ 0),
      Real.zero_rpow (by linarith : -(2 * sigma) ≠ 0)]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hpow0 : 0 ≤ (n : ℝ) ^ (-sigma) := Real.rpow_nonneg hnR.le _
    have haabs : |a n| = a n := abs_of_nonneg (ha0 n)
    have hloga : a n ≤ |Real.log n| :=
      (halog n).trans (le_abs_self (Real.log n))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, haabs,
      abs_of_nonneg hpow0, mul_pow]
    have hrpow :
        ((n : ℝ) ^ (-sigma)) ^ 2 = (n : ℝ) ^ (-(2 * sigma)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnR.le]
      congr 1
      ring
    rw [hrpow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (ha0 n) hloga 2)
      (Real.rpow_nonneg hnR.le _)

theorem summable_sq_woldFiniteWeightedCoefficient
    (N : ℕ) {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Summable (fun n : ℕ =>
      ‖(woldFiniteWeightedCoefficient N sigma n : ℂ)‖ ^ 2) := by
  exact summable_sq_weighted_of_le_log
    (woldFiniteNormalCoefficient_nonneg (Finset.range N))
    (woldFiniteNormalCoefficient_le_log (Finset.range N)) hsigma

theorem summable_sq_woldVonMangoldtWeightedCoefficient
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Summable (fun n : ℕ =>
      ‖(woldVonMangoldtWeightedCoefficient sigma n : ℂ)‖ ^ 2) := by
  exact summable_sq_weighted_of_le_log
    (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
    (fun _ => ArithmeticFunction.vonMangoldt_le_log) hsigma

def woldFiniteWeightedKernel (N : ℕ) (sigma : ℝ) : ℕ × ℕ → ℂ :=
  HilbertSchmidt.diagMul
    (fun n => (woldFiniteWeightedCoefficient N sigma n : ℂ))

def woldVonMangoldtWeightedKernel (sigma : ℝ) : ℕ × ℕ → ℂ :=
  HilbertSchmidt.diagMul
    (fun n => (woldVonMangoldtWeightedCoefficient sigma n : ℂ))

theorem woldFiniteWeightedKernel_isHS
    (N : ℕ) {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    HilbertSchmidt.IsHS (woldFiniteWeightedKernel N sigma) :=
  HilbertSchmidt.isHS_diagMul_infinite _
    (summable_sq_woldFiniteWeightedCoefficient N hsigma)

theorem woldVonMangoldtWeightedKernel_isHS
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    HilbertSchmidt.IsHS (woldVonMangoldtWeightedKernel sigma) :=
  HilbertSchmidt.isHS_diagMul_infinite _
    (summable_sq_woldVonMangoldtWeightedCoefficient hsigma)

def woldFiniteWeightedOperator
    (N : ℕ) (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    EllTwo →L[ℂ] EllTwo :=
  HilbertSchmidt.toOperator (woldFiniteWeightedKernel_isHS N hsigma)

def woldVonMangoldtWeightedOperator
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    EllTwo →L[ℂ] EllTwo :=
  HilbertSchmidt.toOperator (woldVonMangoldtWeightedKernel_isHS hsigma)

theorem woldFiniteWeightedOperator_basis
    (N : ℕ) {sigma : ℝ} (hsigma : 1 / 2 < sigma) (n : ℕ) :
    woldFiniteWeightedOperator N sigma hsigma
        (HilbertSchmidt.lpBasis ℕ n) =
      (woldFiniteWeightedCoefficient N sigma n : ℂ) •
        HilbertSchmidt.lpBasis ℕ n := by
  apply lp.ext
  funext m
  rw [woldFiniteWeightedOperator, HilbertSchmidt.lpBasis_apply,
    HilbertSchmidt.toOperator_single
      (woldFiniteWeightedKernel_isHS N hsigma)]
  change woldFiniteWeightedKernel N sigma (m, n) =
    (woldFiniteWeightedCoefficient N sigma n : ℂ) *
      (lp.single 2 n (1 : ℂ) : EllTwo) m
  by_cases hmn : m = n
  · subst m
    simp [woldFiniteWeightedKernel, HilbertSchmidt.diagMul]
  · simp [woldFiniteWeightedKernel, HilbertSchmidt.diagMul, hmn]

theorem woldVonMangoldtWeightedOperator_basis
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (n : ℕ) :
    woldVonMangoldtWeightedOperator sigma hsigma
        (HilbertSchmidt.lpBasis ℕ n) =
      (woldVonMangoldtWeightedCoefficient sigma n : ℂ) •
        HilbertSchmidt.lpBasis ℕ n := by
  apply lp.ext
  funext m
  rw [woldVonMangoldtWeightedOperator, HilbertSchmidt.lpBasis_apply,
    HilbertSchmidt.toOperator_single
      (woldVonMangoldtWeightedKernel_isHS hsigma)]
  change woldVonMangoldtWeightedKernel sigma (m, n) =
    (woldVonMangoldtWeightedCoefficient sigma n : ℂ) *
      (lp.single 2 n (1 : ℂ) : EllTwo) m
  by_cases hmn : m = n
  · subst m
    simp [woldVonMangoldtWeightedKernel, HilbertSchmidt.diagMul]
  · simp [woldVonMangoldtWeightedKernel, HilbertSchmidt.diagMul, hmn]

theorem woldVonMangoldtWeightedOperator_isHilbertSchmidt
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    (woldVonMangoldtWeightedOperator sigma hsigma).IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator
    (woldVonMangoldtWeightedKernel_isHS hsigma)

theorem woldVonMangoldtWeightedOperator_isCompact
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    IsCompactOperator (woldVonMangoldtWeightedOperator sigma hsigma) :=
  (woldVonMangoldtWeightedOperator_isHilbertSchmidt hsigma).isCompactOperator

def woldWeightedDifferenceEnergy
    (N : ℕ) (sigma : ℝ) (n : ℕ) : ℝ :=
  ((woldFiniteNormalCoefficient (Finset.range N) n -
      ArithmeticFunction.vonMangoldt n) * (n : ℝ) ^ (-sigma)) ^ 2

theorem tendsto_woldWeightedDifferenceEnergy_atTop
    (sigma : ℝ) (n : ℕ) :
    Filter.Tendsto (fun N => woldWeightedDifferenceEnergy N sigma n)
      Filter.atTop (nhds 0) := by
  have hdiff :
      Filter.Tendsto
        (fun N : ℕ => woldFiniteNormalCoefficient (Finset.range N) n -
          ArithmeticFunction.vonMangoldt n)
        Filter.atTop (nhds 0) := by
    have hconst :
        Filter.Tendsto
          (fun _ : ℕ => ArithmeticFunction.vonMangoldt n)
          Filter.atTop (nhds (ArithmeticFunction.vonMangoldt n)) :=
      tendsto_const_nhds
    simpa using (tendsto_woldRangeNormalCoefficient_atTop n).sub hconst
  have hmul := hdiff.mul_const ((n : ℝ) ^ (-sigma))
  simpa [woldWeightedDifferenceEnergy] using hmul.pow 2

private theorem woldWeightedDifferenceEnergy_le_majorant
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (N n : ℕ) :
    ‖woldWeightedDifferenceEnergy N sigma n‖ ≤
      4 * (|Real.log n| ^ 2 * (n : ℝ) ^ (-(2 * sigma))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [woldWeightedDifferenceEnergy,
      Real.zero_rpow (by linarith : -sigma ≠ 0),
      Real.zero_rpow (by linarith : -(2 * sigma) ≠ 0)]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    let a := woldFiniteNormalCoefficient (Finset.range N) n
    let b := ArithmeticFunction.vonMangoldt n
    have ha0 : 0 ≤ a := woldFiniteNormalCoefficient_nonneg _ _
    have hb0 : 0 ≤ b := ArithmeticFunction.vonMangoldt_nonneg
    have haL : a ≤ Real.log n := woldFiniteNormalCoefficient_le_log _ _
    have hbL : b ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have habs : |a - b| ≤ 2 * |Real.log n| := by
      calc
        |a - b| ≤ |a| + |b| := abs_sub a b
        _ = a + b := by rw [abs_of_nonneg ha0, abs_of_nonneg hb0]
        _ ≤ 2 * Real.log n := by linarith
        _ ≤ 2 * |Real.log n| := by gcongr; exact le_abs_self _
    have hpow0 : 0 ≤ (n : ℝ) ^ (-sigma) := Real.rpow_nonneg hnR.le _
    have hrpow :
        ((n : ℝ) ^ (-sigma)) ^ 2 = (n : ℝ) ^ (-(2 * sigma)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnR.le]
      congr 1
      ring
    change ‖((a - b) * (n : ℝ) ^ (-sigma)) ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow, hrpow]
    calc
      (a - b) ^ 2 * (n : ℝ) ^ (-(2 * sigma))
          = |a - b| ^ 2 * (n : ℝ) ^ (-(2 * sigma)) := by rw [sq_abs]
      _ ≤ (2 * |Real.log n|) ^ 2 * (n : ℝ) ^ (-(2 * sigma)) := by
        gcongr
      _ = 4 * (|Real.log n| ^ 2 * (n : ℝ) ^ (-(2 * sigma))) := by ring

theorem tendsto_tsum_woldWeightedDifferenceEnergy_atTop
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Filter.Tendsto
      (fun N => ∑' n, woldWeightedDifferenceEnergy N sigma n)
      Filter.atTop (nhds 0) := by
  have hmajor :
      Summable (fun n : ℕ =>
        4 * (|Real.log n| ^ 2 * (n : ℝ) ^ (-(2 * sigma)))) :=
    (summable_abs_log_natCast_pow_mul_rpow_neg 2 (2 * sigma)
      (by linarith)).mul_left 4
  simpa using tendsto_tsum_of_dominated_convergence
    hmajor (fun n => tendsto_woldWeightedDifferenceEnergy_atTop sigma n)
    (Filter.Eventually.of_forall fun N n =>
      woldWeightedDifferenceEnergy_le_majorant hsigma N n)

theorem hsNormSq_woldFiniteWeightedKernel_sub_eq
    (N : ℕ) (sigma : ℝ) :
    HilbertSchmidt.hsNormSq
        (woldFiniteWeightedKernel N sigma -
          woldVonMangoldtWeightedKernel sigma) =
      ∑' n, woldWeightedDifferenceEnergy N sigma n := by
  have hkernel :
      woldFiniteWeightedKernel N sigma -
          woldVonMangoldtWeightedKernel sigma =
        HilbertSchmidt.diagMul (fun n =>
          (((woldFiniteNormalCoefficient (Finset.range N) n -
              ArithmeticFunction.vonMangoldt n) *
            (n : ℝ) ^ (-sigma) : ℝ) : ℂ)) := by
    funext p
    rcases p with ⟨i, j⟩
    by_cases hij : i = j
    · subst j
      simp [woldFiniteWeightedKernel, woldVonMangoldtWeightedKernel,
        HilbertSchmidt.diagMul, woldFiniteWeightedCoefficient,
        woldVonMangoldtWeightedCoefficient]
      ring
    · simp [woldFiniteWeightedKernel, woldVonMangoldtWeightedKernel,
        HilbertSchmidt.diagMul, hij]
  rw [hkernel, HilbertSchmidt.hsNormSq_diagMul_infinite]
  apply tsum_congr
  intro n
  rw [woldWeightedDifferenceEnergy, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    mul_pow, sq_abs]
  ring

theorem tendsto_hsNormSq_woldFiniteWeightedKernel_sub_atTop
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Filter.Tendsto
      (fun N =>
        HilbertSchmidt.hsNormSq
          (woldFiniteWeightedKernel N sigma -
            woldVonMangoldtWeightedKernel sigma))
      Filter.atTop (nhds 0) := by
  simpa [hsNormSq_woldFiniteWeightedKernel_sub_eq] using
    tendsto_tsum_woldWeightedDifferenceEnergy_atTop hsigma

theorem tendsto_hsNorm_woldFiniteWeightedKernel_sub_atTop
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Filter.Tendsto
      (fun N =>
        HilbertSchmidt.hsNorm
          (woldFiniteWeightedKernel N sigma -
            woldVonMangoldtWeightedKernel sigma))
      Filter.atTop (nhds 0) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_hsNormSq_woldFiniteWeightedKernel_sub_atTop hsigma)
  change Filter.Tendsto
    (fun N => Real.sqrt
      (HilbertSchmidt.hsNormSq
        (woldFiniteWeightedKernel N sigma -
          woldVonMangoldtWeightedKernel sigma)))
    Filter.atTop (nhds (Real.sqrt 0)) at hsqrt
  simpa only [HilbertSchmidt.hsNorm, Real.sqrt_zero] using hsqrt

theorem woldWeightedKernelSub_isHS
    (N : ℕ) {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    HilbertSchmidt.IsHS
      (woldFiniteWeightedKernel N sigma -
        woldVonMangoldtWeightedKernel sigma) := by
  have hneg :
      HilbertSchmidt.IsHS (-woldVonMangoldtWeightedKernel sigma) := by
    have hsmul :=
      (woldVonMangoldtWeightedKernel_isHS hsigma).smul (-1)
    convert hsmul using 1
    ext p
    simp
  simpa only [sub_eq_add_neg] using
    (woldFiniteWeightedKernel_isHS N hsigma).add hneg

theorem woldFiniteWeightedOperator_sub_eq_toOperator
    (N : ℕ) {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    woldFiniteWeightedOperator N sigma hsigma -
        woldVonMangoldtWeightedOperator sigma hsigma =
      HilbertSchmidt.toOperator (woldWeightedKernelSub_isHS N hsigma) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  rw [sub_apply]
  change
    (∑' j, woldFiniteWeightedKernel N sigma (i, j) * f j) -
        (∑' j, woldVonMangoldtWeightedKernel sigma (i, j) * f j) =
      ∑' j,
        (woldFiniteWeightedKernel N sigma -
          woldVonMangoldtWeightedKernel sigma) (i, j) * f j
  rw [← Summable.tsum_sub
    (HilbertSchmidt.summable_row_mul
      (woldFiniteWeightedKernel_isHS N hsigma) f i)
    (HilbertSchmidt.summable_row_mul
      (woldVonMangoldtWeightedKernel_isHS hsigma) f i)]
  apply tsum_congr
  intro j
  simp [sub_mul]

theorem hsNormSq_woldFiniteWeightedOperator_sub_eq
    (N : ℕ) {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    ContinuousLinearMap.hsNormSq
        (woldFiniteWeightedOperator N sigma hsigma -
          woldVonMangoldtWeightedOperator sigma hsigma) =
      HilbertSchmidt.hsNormSq
        (woldFiniteWeightedKernel N sigma -
          woldVonMangoldtWeightedKernel sigma) := by
  rw [woldFiniteWeightedOperator_sub_eq_toOperator N hsigma,
    HilbertSchmidt.hsNormSq_toOperator]

theorem tendsto_hsNormSq_woldFiniteWeightedOperator_sub_atTop
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Filter.Tendsto
      (fun N =>
        ContinuousLinearMap.hsNormSq
          (woldFiniteWeightedOperator N sigma hsigma -
            woldVonMangoldtWeightedOperator sigma hsigma))
      Filter.atTop (nhds 0) := by
  simpa [hsNormSq_woldFiniteWeightedOperator_sub_eq] using
    tendsto_hsNormSq_woldFiniteWeightedKernel_sub_atTop hsigma

theorem tendsto_hsNorm_woldFiniteWeightedOperator_sub_atTop
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Filter.Tendsto
      (fun N =>
        ContinuousLinearMap.hsNorm
          (woldFiniteWeightedOperator N sigma hsigma -
            woldVonMangoldtWeightedOperator sigma hsigma))
      Filter.atTop (nhds 0) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_hsNormSq_woldFiniteWeightedOperator_sub_atTop hsigma)
  change Filter.Tendsto
    (fun N => Real.sqrt
      (ContinuousLinearMap.hsNormSq
        (woldFiniteWeightedOperator N sigma hsigma -
          woldVonMangoldtWeightedOperator sigma hsigma)))
    Filter.atTop (nhds (Real.sqrt 0)) at hsqrt
  simpa only [ContinuousLinearMap.hsNorm, Real.sqrt_zero] using hsqrt

/-! ## Sharp Hilbert--Schmidt wall -/

private theorem not_isHS_woldVonMangoldtWeightedKernel_of_le_half
    {sigma : ℝ} (hsigma : sigma ≤ 1 / 2) :
    ¬ HilbertSchmidt.IsHS (woldVonMangoldtWeightedKernel sigma) := by
  intro hHS
  change Summable
    (fun p : ℕ × ℕ =>
      ‖woldVonMangoldtWeightedKernel sigma p‖ ^ 2) at hHS
  have hdiag :
      Summable (fun n : ℕ =>
        ‖(woldVonMangoldtWeightedCoefficient sigma n : ℂ)‖ ^ 2) := by
    have hinj : Function.Injective (fun n : ℕ => (n, n)) :=
      fun a b h => (Prod.ext_iff.mp h).1
    exact (hHS.comp_injective hinj).congr fun n => by
      simp [woldVonMangoldtWeightedKernel, HilbertSchmidt.diagMul]
  have hprime :
      Summable (fun p : Nat.Primes =>
        ‖(woldVonMangoldtWeightedCoefficient sigma p : ℂ)‖ ^ 2) :=
    hdiag.comp_injective Subtype.val_injective
  have hprimeEnergy :
      Summable (fun p : Nat.Primes =>
        Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (-(2 * sigma))) := by
    apply hprime.congr
    intro p
    have hpR : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
    rw [woldVonMangoldtWeightedCoefficient,
      ArithmeticFunction.vonMangoldt_apply_prime p.prop,
      Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (Real.log_pos (by exact_mod_cast p.prop.one_lt)),
      abs_of_nonneg (Real.rpow_nonneg hpR.le _), mul_pow]
    have hrpow :
        ((p : ℝ) ^ (-sigma)) ^ 2 =
          (p : ℝ) ^ (-(2 * sigma)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hpR.le]
      congr 1
      ring
    rw [hrpow]
  have hscaled :
      Summable (fun p : Nat.Primes =>
        Real.log 2 ^ 2 * (1 / (p : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · intro p
      have hpone : (1 : ℝ) ≤ p := by
        exact_mod_cast p.prop.one_lt.le
      have hp2 : (2 : ℝ) ≤ p := by
        exact_mod_cast p.prop.two_le
      have hlog :
          Real.log 2 ≤ Real.log (p : ℝ) :=
        Real.strictMonoOn_log.monotoneOn
          (show (0 : ℝ) < 2 by norm_num)
          (show (0 : ℝ) < p by exact_mod_cast p.prop.pos) hp2
      have hrpow :
          1 / (p : ℝ) ≤ (p : ℝ) ^ (-(2 * sigma)) := by
        rw [one_div, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hpone (by linarith)
      exact mul_le_mul
        (pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) hlog 2)
        hrpow (by positivity) (by positivity)
    · exact hprimeEnergy
  have hharmonic :
      Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff
      (pow_ne_zero 2 (Real.log_pos one_lt_two).ne')).mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

theorem isHS_woldVonMangoldtWeightedKernel_iff (sigma : ℝ) :
    HilbertSchmidt.IsHS (woldVonMangoldtWeightedKernel sigma) ↔
      1 / 2 < sigma := by
  constructor
  · intro hHS
    exact lt_of_not_ge fun hsigma =>
      not_isHS_woldVonMangoldtWeightedKernel_of_le_half hsigma hHS
  · exact woldVonMangoldtWeightedKernel_isHS

theorem not_isHS_woldVonMangoldtCriticalKernel :
    ¬ HilbertSchmidt.IsHS
      (woldVonMangoldtWeightedKernel (1 / 2)) :=
  not_isHS_woldVonMangoldtWeightedKernel_of_le_half le_rfl

/-! ## Trace and Euler logarithmic derivative -/

def woldJetTraceCoefficient (sigma : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
    (s + (sigma : ℂ)) n

def woldJetTraceLeftCoefficient (sigma : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  (Real.sqrt ‖woldJetTraceCoefficient sigma s n‖ : ℝ)

def woldJetTraceRightCoefficient (sigma : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if woldJetTraceCoefficient sigma s n = 0 then 0
  else woldJetTraceCoefficient sigma s n /
    (Real.sqrt ‖woldJetTraceCoefficient sigma s n‖ : ℝ)

theorem woldJetTraceLeft_mul_right
    (sigma : ℝ) (s : ℂ) (n : ℕ) :
    woldJetTraceLeftCoefficient sigma s n *
        woldJetTraceRightCoefficient sigma s n =
      woldJetTraceCoefficient sigma s n := by
  rw [woldJetTraceLeftCoefficient, woldJetTraceRightCoefficient]
  by_cases hc : woldJetTraceCoefficient sigma s n = 0
  · simp [hc]
  · rw [if_neg hc]
    have hnorm : 0 < ‖woldJetTraceCoefficient sigma s n‖ :=
      norm_pos_iff.mpr hc
    have hsqrt :
        (Real.sqrt ‖woldJetTraceCoefficient sigma s n‖ : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hnorm).ne'
    field_simp

theorem summable_norm_woldJetTraceCoefficient
    {sigma : ℝ} {s : ℂ} (hs : 1 < s.re + sigma) :
    Summable (fun n => ‖woldJetTraceCoefficient sigma s n‖) := by
  have hLS : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (s + (sigma : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hs)
  exact (summable_norm_iff.mpr hLS).congr fun n => by
    rfl

theorem summable_sq_woldJetTraceLeftCoefficient
    {sigma : ℝ} {s : ℂ} (hs : 1 < s.re + sigma) :
    Summable (fun n =>
      ‖woldJetTraceLeftCoefficient sigma s n‖ ^ 2) := by
  apply (summable_norm_woldJetTraceCoefficient hs).congr
  intro n
  rw [woldJetTraceLeftCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _)]

theorem norm_sq_woldJetTraceRightCoefficient
    (sigma : ℝ) (s : ℂ) (n : ℕ) :
    ‖woldJetTraceRightCoefficient sigma s n‖ ^ 2 =
      ‖woldJetTraceCoefficient sigma s n‖ := by
  rw [woldJetTraceRightCoefficient]
  by_cases hc : woldJetTraceCoefficient sigma s n = 0
  · simp [hc]
  · rw [if_neg hc, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hnorm : 0 < ‖woldJetTraceCoefficient sigma s n‖ :=
      norm_pos_iff.mpr hc
    have hsqrt : Real.sqrt ‖woldJetTraceCoefficient sigma s n‖ ≠ 0 :=
      (Real.sqrt_pos.2 hnorm).ne'
    rw [div_pow, Real.sq_sqrt (norm_nonneg _)]
    field_simp

theorem summable_sq_woldJetTraceRightCoefficient
    {sigma : ℝ} {s : ℂ} (hs : 1 < s.re + sigma) :
    Summable (fun n =>
      ‖woldJetTraceRightCoefficient sigma s n‖ ^ 2) :=
  (summable_norm_woldJetTraceCoefficient hs).congr
    (fun n => (norm_sq_woldJetTraceRightCoefficient sigma s n).symm)

def woldJetTraceLeftKernel (sigma : ℝ) (s : ℂ) : ℕ × ℕ → ℂ :=
  HilbertSchmidt.diagMul (woldJetTraceLeftCoefficient sigma s)

def woldJetTraceRightKernel (sigma : ℝ) (s : ℂ) : ℕ × ℕ → ℂ :=
  HilbertSchmidt.diagMul (woldJetTraceRightCoefficient sigma s)

theorem woldJetTraceLeftKernel_isHS
    {sigma : ℝ} {s : ℂ} (hs : 1 < s.re + sigma) :
    HilbertSchmidt.IsHS (woldJetTraceLeftKernel sigma s) :=
  HilbertSchmidt.isHS_diagMul_infinite _
    (summable_sq_woldJetTraceLeftCoefficient hs)

theorem woldJetTraceRightKernel_isHS
    {sigma : ℝ} {s : ℂ} (hs : 1 < s.re + sigma) :
    HilbertSchmidt.IsHS (woldJetTraceRightKernel sigma s) :=
  HilbertSchmidt.isHS_diagMul_infinite _
    (summable_sq_woldJetTraceRightCoefficient hs)

def woldJetTraceOperator
    (sigma : ℝ) (s : ℂ) (hs : 1 < s.re + sigma) :
    EllTwo →L[ℂ] EllTwo :=
  HilbertSchmidt.toOperator (woldJetTraceLeftKernel_isHS hs) ∘L
    HilbertSchmidt.toOperator (woldJetTraceRightKernel_isHS hs)

theorem opTrace_woldJetTraceOperator_eq_tsum
    {sigma : ℝ} {s : ℂ} (hs : 1 < s.re + sigma) :
    ContinuousLinearMap.opTrace (woldJetTraceOperator sigma s hs) =
      ∑' n, woldJetTraceCoefficient sigma s n := by
  rw [woldJetTraceOperator,
    HilbertSchmidt.opTrace_toOperator_comp
      (woldJetTraceLeftKernel_isHS hs)
      (woldJetTraceRightKernel_isHS hs)]
  change
    (∑' n,
      HilbertSchmidt.hsComp
        (HilbertSchmidt.diagMul (woldJetTraceLeftCoefficient sigma s))
        (HilbertSchmidt.diagMul (woldJetTraceRightCoefficient sigma s))
        (n, n)) =
      ∑' n, woldJetTraceCoefficient sigma s n
  rw [HilbertSchmidt.hsComp_diagMul]
  apply tsum_congr
  intro n
  simp only [HilbertSchmidt.diagMul, if_pos]
  exact woldJetTraceLeft_mul_right sigma s n

theorem opTrace_woldJetTraceOperator_eq_zeta_logDeriv
    {sigma : ℝ} {s : ℂ} (hs : 1 < s.re + sigma) :
    ContinuousLinearMap.opTrace (woldJetTraceOperator sigma s hs) =
      -deriv riemannZeta (s + (sigma : ℂ)) /
        riemannZeta (s + (sigma : ℂ)) := by
  rw [opTrace_woldJetTraceOperator_eq_tsum hs]
  change
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (s + (sigma : ℂ)) =
      -deriv riemannZeta (s + (sigma : ℂ)) /
        riemannZeta (s + (sigma : ℂ))
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by
    simpa using hs)

end

end RHTower
