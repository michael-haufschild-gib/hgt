import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AffineShellErrorsHaveAUniformHarmonicBudget
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheActualUpwardSourceHasPolynomialHarmonicBounds

/-!
# Exact horizon decay of the upward prime residual

The logarithmic kernel error retains its inverse-horizon factor. Prime-index
boundary rows instead have a horizon-independent harmonic square budget.
Combining these with the actual affine-shell source keeps their distinct rates.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem quotient_lt_twice_floor {N n : ℕ} (hn : n ∈ Icc 1 N) :
    (N : ℝ) / n < 2 * ((N / n : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hy : (1 : ℝ) ≤ ((N / n : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_pos (mem_Icc.mp hn).2 (mem_Icc.mp hn).1
  have hf : (N : ℝ) / n < (N / n : ℕ) + 1 := by
    rw [div_lt_iff₀ hn0]
    have hmod := Nat.mod_lt N (mem_Icc.mp hn).1
    have hid := Nat.mod_add_div N n
    have hlt : N < (N / n + 1) * n := by nlinarith only [hmod, hid]
    exact_mod_cast hlt
  linarith only [hf, hy]

/-- Both prime-index cutoff changes have a fifth-power strip budget at every horizon. -/
theorem exists_linearizedUpwardCoefficient_boundary_uniform_harmonic_budget {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ (N : ℝ) → ∀ B : ℕ,
      (∑ n ∈ Icc 1 N,
        ((linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) /
          Real.sqrt n) ^ 2) ≤ K * ((B : ℝ) + 1) ^ 5 := by
  let D : ℝ := 32 * m.totient
  have hD : 0 < D := by
    have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
    dsimp only [D]
    positivity
  refine ⟨10 * D ^ 2, by positivity, ?_⟩
  intro N hN c hc hcN B
  let b : ℝ := (B : ℝ) + 1
  let R : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) /
      Real.sqrt n
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 1 ≤ b := by dsimp only [b]; have := Nat.cast_nonneg (α := ℝ) B; linarith only [this]
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hBb : (B : ℝ) ≤ b := by dsimp only [b]; linarith only
  have hglobal : ∀ n ∈ Icc 1 N, R n ^ 2 ≤ (D * b ^ 2) ^ 2 / n := by
    intro n hn
    have hsource := abs_linearizedUpwardCoefficient_sub_reciprocal_le hφ hsupp hM hc hm
      (mem_Icc.mp hn).1 hcN (B := B)
    have hmass := mul_le_mul_of_nonneg_left (primeIndexBoundaryMass_le_width B (N / n))
      (show 0 ≤ 4 * (B : ℝ) * m.totient by positivity)
    have hbprod := mul_le_mul_of_nonneg_right hBb hb0.le
    have hcoef : |linearizedUpwardCoefficient φ c B N m n -
        reciprocalUpwardCoefficient φ c B N m n| ≤ D * b ^ 2 := by
      have hsmall := mul_le_mul_of_nonneg_left hbprod
        (show 0 ≤ 8 * (m.totient : ℝ) by positivity)
      dsimp only [b, D] at *
      nlinarith only [hsource, hmass, hsmall, Nat.cast_nonneg (α := ℝ) m.totient]
    have hr : |R n| ≤ D * b ^ 2 / Real.sqrt n := by
      dsimp only [R]
      rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
      exact div_le_div_of_nonneg_right hcoef (Real.sqrt_nonneg _)
    have hsq := mul_self_le_mul_self (abs_nonneg _) hr
    simpa only [← sq, sq_abs, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)] using hsq
  have hgood : ∀ n ∈ Icc 1 N, 4 * b ≤ (N : ℝ) / n →
      R n ^ 2 ≤ 2 * (D * b ^ 2) ^ 2 / N := by
    intro n hn ht
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hy0 : (0 : ℝ) < (N / n : ℕ) := by
      exact_mod_cast Nat.div_pos (mem_Icc.mp hn).2 (mem_Icc.mp hn).1
    have hquot := quotient_lt_twice_floor hn
    have hYb : 2 * B + 2 ≤ N / n := by
      have h : 2 * b ≤ ((N / n : ℕ) : ℝ) := by linarith only [ht, hquot]
      dsimp only [b] at h
      exact_mod_cast h
    have hsource := abs_linearizedUpwardCoefficient_sub_reciprocal_le hφ hsupp hM hc hm
      (mem_Icc.mp hn).1 hcN (B := B)
    have hmass := mul_le_mul_of_nonneg_left (primeIndexBoundaryMass_le_sqrt hYb)
      (show 0 ≤ 4 * (B : ℝ) * m.totient by positivity)
    have hcoef : |linearizedUpwardCoefficient φ c B N m n -
        reciprocalUpwardCoefficient φ c B N m n| ≤ D * b ^ 2 / Real.sqrt (N / n : ℕ) := by
      calc
        _ ≤ 4 * (B : ℝ) * m.totient * (8 * b / Real.sqrt (N / n : ℕ)) := hsource.trans hmass
        _ = D * ((B : ℝ) * b) / Real.sqrt (N / n : ℕ) := by dsimp only [D]; ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by nlinarith only [mul_le_mul_of_nonneg_right hBb hb0.le]) hD.le)
          (Real.sqrt_nonneg _)
    have hr : |R n| ≤ (D * b ^ 2 / Real.sqrt (N / n : ℕ)) / Real.sqrt n := by
      dsimp only [R]
      rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
      exact div_le_div_of_nonneg_right hcoef (Real.sqrt_nonneg _)
    have hsq := mul_self_le_mul_self (abs_nonneg _) hr
    simp only [← sq, sq_abs, div_pow, Real.sq_sqrt (Nat.cast_nonneg n),
      Real.sq_sqrt (Nat.cast_nonneg (N / n))] at hsq
    have hNY : (N : ℝ) ≤ 2 * (((N / n : ℕ) : ℝ) * n) := by
      have h := (div_lt_iff₀ hn0).mp hquot
      nlinarith only [h]
    have hdiv : (D * b ^ 2) ^ 2 / ((N / n : ℕ) : ℝ) / n ≤
        2 * (D * b ^ 2) ^ 2 / N := by
      rw [div_div]
      apply (div_le_div_iff₀ (mul_pos hy0 hn0) hN0).mpr
      have h := mul_le_mul_of_nonneg_left hNY (sq_nonneg (D * b ^ 2))
      nlinarith only [h]
    exact hsq.trans hdiv
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      R n ^ 2 ≤ 2 * (D * b ^ 2) ^ 2 / N +
        if (N : ℝ) / n < 4 * b then (D * b ^ 2) ^ 2 / n else 0 := by
    by_cases ht : (N : ℝ) / n < 4 * b
    · rw [if_pos ht]
      exact (hglobal n hn).trans (le_add_of_nonneg_left (by positivity))
    · rw [if_neg ht, add_zero]
      exact hgood n hn (le_of_not_gt ht)
  have htail := HTGeometry.harmonic_quotient_tail_le hN
    (show 1 ≤ 4 * b by linarith only [hb])
  have hlog : 1 + Real.log (2 * (4 * b)) ≤ 8 * b := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 2 * (4 * b) by positivity)
    linarith only [h]
  have hsum : (∑ n ∈ Icc 1 N, R n ^ 2) ≤
      2 * (D * b ^ 2) ^ 2 + (D * b ^ 2) ^ 2 * (8 * b) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, (2 * (D * b ^ 2) ^ 2 / N +
          if (N : ℝ) / n < 4 * b then (D * b ^ 2) ^ 2 / n else 0) := sum_le_sum hpoint
      _ = 2 * (D * b ^ 2) ^ 2 + (D * b ^ 2) ^ 2 *
          ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < 4 * b), 1 / (n : ℝ) := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          ← sum_filter, mul_sum]
        congr 1
        · field_simp
        · exact sum_congr rfl fun n _ => by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (htail.trans hlog) (sq_nonneg _))
  have h45 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (by norm_num : 4 ≤ 5))
    (show 0 ≤ 2 * D ^ 2 by positivity)
  change _ ≤ (10 * D ^ 2) * b ^ 5
  nlinarith only [hsum, h45]

private theorem mertensSum_add_le_log_multiple {N B : ℕ} (hN : 1 ≤ N)
    (hL : 1 ≤ Real.log (N : ℝ)) (hBN : B ≤ N) :
    mertensSum (N + B) ≤ (Real.log 4 + 6) * Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNB : 1 ≤ N + B := by omega
  have hrow := row_le (by omega : 0 < (1 : ℕ)) hNB
  simp only [Nat.div_one, Nat.cast_one, Real.log_one, add_zero] at hrow
  have hlog : Real.log ((N + B : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have hsum : ((N + B : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast (show N + B ≤ 2 * N by omega)
    have h := Real.log_le_log (by exact_mod_cast hNB : (0 : ℝ) < (N + B : ℕ)) hsum
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at h
    have htwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    linarith only [h, htwo, hL]
  have hcost : 0 ≤ Real.log (4 : ℝ) + 4 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith only [h]
  have hscale := mul_le_mul_of_nonneg_left hL hcost
  nlinarith only [hrow, hlog, hscale]

/-- The logarithmic kernel replacement retains its squared inverse-horizon decay. -/
theorem exists_logarithmicUpwardCoefficient_horizon_harmonic_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log (N : ℝ) →
      ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 → ∀ B : ℕ, B ≤ N →
      2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) →
      (∑ n ∈ Icc 1 N,
        ((logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) /
          Real.sqrt n) ^ 2) / Real.log N ≤
        K * c ^ 4 * ((B : ℝ) + 1) ^ 6 * (Real.log (N : ℝ) / N) ^ 2 := by
  obtain ⟨D, hD, hsource⟩ := exists_logarithmicUpwardCoefficient_polynomial_bound hφ hsupp hM m
  let E := D * (Real.log 4 + 6)
  refine ⟨2 * E ^ 2, by positivity, ?_⟩
  intro N hN hL c hc hw B hBN hlarge
  let a := E * c ^ 2 * ((B : ℝ) + 1) ^ 3 * (Real.log N / N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have ha : ∀ n : ℕ, 1 ≤ n →
      |logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n| ≤ a := by
    intro n hn
    refine (hsource c hc B N hN hw hlarge n hn).trans ?_
    calc
      _ ≤ D * c ^ 2 * ((B : ℝ) + 1) ^ 3 * ((Real.log 4 + 6) * Real.log N) / N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mertensSum_add_le_log_multiple hN hL hBN) (by positivity)) hN0.le
      _ = _ := by dsimp only [a, E]; ring
  have hsum : (∑ n ∈ Icc 1 N,
      ((logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) /
        Real.sqrt n) ^ 2) ≤ a ^ 2 * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, a ^ 2 / (n : ℝ) := by
        apply sum_le_sum
        intro n hn
        have hsq := mul_self_le_mul_self (abs_nonneg _) (ha n (mem_Icc.mp hn).1)
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        simpa only [← sq, sq_abs] using hsq
      _ = _ := by
        rw [← _root_.RHTower.Sieve.sum_Icc_one_div_eq_harmonic, mul_sum]
        exact sum_congr rfl fun n _ => by ring
  have hH : (harmonic N : ℝ) / Real.log N ≤ 2 := by
    apply (div_le_iff₀ hL0).mpr
    linarith only [harmonic_le_one_add_log N, hL]
  calc
    _ ≤ (a ^ 2 * (harmonic N : ℝ)) / Real.log N := div_le_div_of_nonneg_right hsum hL0.le
    _ = a ^ 2 * ((harmonic N : ℝ) / Real.log N) := by ring
    _ ≤ a ^ 2 * 2 := mul_le_mul_of_nonneg_left hH (sq_nonneg _)
    _ = _ := by dsimp only [a]; ring

/-- The actual upward source retains its harmonic and inverse-horizon decay rates. -/
theorem exists_actualUpwardRowError_horizon_harmonic_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log (N : ℝ) →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) / Real.log N ≤
          K * (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_logarithmicUpwardCoefficient_horizon_harmonic_bound hφ hsupp hM m
  obtain ⟨Cb, hCb, hb⟩ := exists_linearizedUpwardCoefficient_boundary_uniform_harmonic_budget hφ hsupp hM hm
  obtain ⟨Cd, hCd, hd⟩ := exists_shiftedReciprocalUpwardRowError_uniform_harmonic_budget hm hφ hsupp hM
  let d : ℝ := Real.exp 1 + 2
  let A := Ca * d ^ 6
  let B₀ := Cb * d ^ 5 + Cd
  have hdpos : 0 < d := by dsimp only [d]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  let K := 3 * (A + B₀) + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro N hN hlog c hc1 hlarge
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  let B := linearPrimeStrip c
  have hBc : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; nlinarith only [hBc, hc1]
  have hc2 : c ≤ c ^ 2 := by nlinarith only [hc1]
  have hexp := Real.exp_pos 1
  have hwidth : c / N ≤ 1 := by
    apply (div_le_one hN0).mpr
    have hcoef : 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [hlarge, hc2, h]
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hwidth
  have hBN : B ≤ N := by
    have hcoef : Real.exp 1 + 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ Real.exp 1 + 1 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    have h : (B : ℝ) ≤ N := by nlinarith only [hBc, h1, h2, hlarge]
    exact_mod_cast h
  have hkernel : 2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) := by
    have hcoef : 2 * (Real.exp 1 + 3) * (Real.exp 1 + 1) ≤
        4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hBc
      (show 0 ≤ 2 * ((Real.exp 1 + 3) * c) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h1, h2, hlarge]
  have hB : ⌈c⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_left
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.le
    have hce : c ≤ c * Real.exp 1 := by simpa only [mul_one] using h
    exact hce.trans (Nat.le_ceil _)
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let r : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  have ha' : (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N ≤
      A * c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 := by
    refine (ha N hN hlog c hc1 hwidth B hBN hkernel).trans ?_
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hpow := pow_le_pow_left₀ (show 0 ≤ (B : ℝ) + 1 by positivity) hB1 6
    have h := mul_le_mul_of_nonneg_left hpow (show 0 ≤ Ca * c ^ 4 by positivity)
    exact h.trans_eq (by dsimp only [A]; ring)
  have hb' : (∑ n ∈ Icc 1 N, b n ^ 2) / Real.log N ≤
      (Cb * d ^ 5) * c ^ 5 / Real.log N := by
    apply div_le_div_of_nonneg_right _ hL0.le
    refine (hb N hN c hc hcN B).trans ?_
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB1 5) hCb.le
    exact h.trans_eq (by ring)
  have hrraw : (∑ n ∈ Icc 1 N, r n ^ 2) ≤ Cd * c ^ 5 := by
    have hid : shellCorrectionOfShift φ c m id = shellCorrection φ c m := rfl
    have hrow (n : ℕ) (hn : 1 ≤ n) :
        r n = (shiftedReciprocalUpwardRowError φ c id N m n +
          shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
      dsimp only [r]
      rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc hB N m n hn]
      dsimp only [shiftedReciprocalUpwardRowError]
      rw [hid, shellCorrectionOfShift_reflected hm]
      ring
    have hsum : (∑ n ∈ Icc 1 N, r n ^ 2) ≤
        ∑ n ∈ Icc 1 N, (shiftedReciprocalUpwardRowError φ c id N m n ^ 2 +
          shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n ^ 2) / 2 := by
      apply sum_le_sum
      intro n hn
      rw [hrow n (mem_Icc.mp hn).1]
      nlinarith only [sq_nonneg (shiftedReciprocalUpwardRowError φ c id N m n -
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n)]
    rw [← sum_div, sum_add_distrib] at hsum
    linarith only [hsum, hd N hN c hc1 id, hd N hN c hc1 (reflectedAffineShift m)]
  have hr' := div_le_div_of_nonneg_right hrraw hL0.le
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) : actualUpwardRowError φ c N m n = a n + b n + r n := by
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < n)).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt n := by
      apply (eq_div_iff hs).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width
        hsupp hc hn hwidth m
    rw [actualUpwardRowError, hu]
    dsimp only [a, b, r]
    ring
  have hsum : (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) ≤
      ∑ n ∈ Icc 1 N, 3 * (a n ^ 2 + b n ^ 2 + r n ^ 2) := by
    apply sum_le_sum
    intro n hn
    rw [hrow n hn]
    nlinarith only [sq_nonneg (a n - b n), sq_nonneg (a n - r n), sq_nonneg (b n - r n)]
  have hfinal := div_le_div_of_nonneg_right hsum hL0.le
  rw [← mul_sum, sum_add_distrib, sum_add_distrib, mul_div_assoc, add_div, add_div] at hfinal
  have hrate₁ : 0 ≤ c ^ 5 / Real.log N := by positivity
  have hrate₂ : 0 ≤ c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 := by positivity
  have hmain := hfinal.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add ha' hb') hr') (by norm_num : (0 : ℝ) ≤ 3))
  have hid : 3 * (A * c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
      Cb * d ^ 5 * c ^ 5 / Real.log N + Cd * c ^ 5 / Real.log N) =
      3 * A * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) +
        3 * B₀ * (c ^ 5 / Real.log N) := by dsimp only [B₀]; ring
  rw [hid] at hmain
  have hAK : 3 * A ≤ K := by dsimp only [K]; linarith only [hB₀]
  have hBK : 3 * B₀ ≤ K := by dsimp only [K]; linarith only [hA]
  calc
    _ ≤ 3 * A * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) +
        3 * B₀ * (c ^ 5 / Real.log N) := hmain
    _ ≤ K * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) + K * (c ^ 5 / Real.log N) :=
      add_le_add (mul_le_mul_of_nonneg_right hAK hrate₂) (mul_le_mul_of_nonneg_right hBK hrate₁)
    _ = _ := by ring

/-- The actual upward vector has the same two horizon decay rates. -/
theorem exists_normalizedUpwardPrimeResidual_horizon_harmonic_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log (N : ℝ) →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖normalizedUpwardPrimeResidual φ c N m‖ ^ 2 ≤
          K * (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  simpa only [normalizedUpwardPrimeResidual_norm_sq] using
    exists_actualUpwardRowError_horizon_harmonic_bound hφ hsupp hM hm

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_linearizedUpwardCoefficient_boundary_uniform_harmonic_budget
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_logarithmicUpwardCoefficient_horizon_harmonic_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_actualUpwardRowError_horizon_harmonic_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_normalizedUpwardPrimeResidual_horizon_harmonic_bound
