import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingConductorShellsHaveUniformHarmonicBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UpwardPrimeErrorsRetainTheirHorizonDecay

/-!
# Uniform conductor bounds for literal upward rows

Keep the totient factor explicit through logarithmic-kernel linearization,
both finite cutoff changes, and the signed reciprocal-shell comparison.
The complete upward residual has one constant on every logarithmic
conductor range, with separate boundary, kernel and harmonic-source rates.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem logarithmicUpwardCoefficient_error_of_uniform_kernel {φ : ℝ → ℝ}
    (hM : 0 < ∫ u, φ u ^ 2) (c : ℝ) {B N m n : ℕ} (hN1 : 1 ≤ N) (hn : 1 ≤ n)
    {C : ℝ} (hC : 0 ≤ C)
    (hker : ∀ T j : ℕ, 1 ≤ T → 1 ≤ j → T ≠ j → |(j : ℝ) - T| ≤ B →
      |Real.sqrt T / Real.sqrt j *
          shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log T)) -
        shellAutocorr φ ((N : ℝ) / c * (((j : ℝ) - T) / T))| ≤ C / N) :
    |logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n| ≤
      (2 * (B : ℝ) * m.totient * C / (∫ u, φ u ^ 2)) * mertensSum (N + B) / N := by
  let D := 2 * (B : ℝ) * m.totient * C / (∫ u, φ u ^ 2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpoint (k : ℕ) (hk : k ∈ Icc 1 (N + B)) (h : ℕ) (hh : h ∈ Icc 1 B) :
      |logarithmicUpwardOffset φ c N m n k h - linearizedUpwardOffset φ c N m n k h| ≤
        2 * m.totient * C / N := by
    have hk1 := (mem_Icc.mp hk).1
    have hh1 := (mem_Icc.mp hh).1
    have hhB := (mem_Icc.mp hh).2
    have hT : 1 ≤ k * n := Nat.mul_pos hk1 hn
    have hgap : |((k * n + h : ℕ) : ℝ) - (k * n : ℕ)| ≤ B := by
      simp only [Nat.cast_add, add_sub_cancel_left, abs_of_nonneg (show (0 : ℝ) ≤ h from Nat.cast_nonneg h)]
      exact_mod_cast hhB
    have hpker : |logarithmicUpwardKernel φ c N (k * n) (k * n + h) -
        shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ)))| ≤ C / N := by
      have h := hker (k * n) (k * n + h) hT (by omega) (by omega) hgap
      simpa only [logarithmicUpwardKernel, Nat.cast_add, add_sub_cancel_left] using h
    have hnp : 0 ≤ (m.totient : ℝ) * (C / N) := by positivity
    have hp : |(if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) *
          logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0) -
        (if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) else 0) *
          shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ)))| ≤
        (m.totient : ℝ) * (C / N) := by
      by_cases hcut : k * n + h ≤ N
      · rw [if_pos hcut, if_pos hcut, ← mul_sub, abs_mul]
        exact mul_le_mul
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m (k * n + h))
          hpker (abs_nonneg _) (Nat.cast_nonneg _)
      · simpa only [if_neg hcut, zero_mul, sub_zero, abs_zero] using hnp
    have hm : |(if h < k * n ∧ k * n - h ≤ N then ramanujanLagCoefficient m (k * n - h) *
          logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0) -
        (if h < k * n ∧ k * n - h ≤ N then ramanujanLagCoefficient m (k * n - h) else 0) *
          shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ)))| ≤
        (m.totient : ℝ) * (C / N) := by
      by_cases hcut : h < k * n ∧ k * n - h ≤ N
      · have hgap' : |((k * n - h : ℕ) : ℝ) - (k * n : ℕ)| ≤ B := by
          rw [Nat.cast_sub hcut.1.le, sub_sub_cancel_left, abs_neg,
            abs_of_nonneg (show (0 : ℝ) ≤ h from Nat.cast_nonneg h)]
          exact_mod_cast hhB
        have hkerm := hker (k * n) (k * n - h) hT (by omega) (by omega) hgap'
        have heq : (N : ℝ) / c * ((((k * n - h : ℕ) : ℝ) - (k * n : ℕ)) / (k * n : ℕ)) =
            -((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ))) := by
          rw [Nat.cast_sub hcut.1.le]
          ring
        rw [heq, shellAutocorr_neg] at hkerm
        rw [if_pos hcut, if_pos hcut, ← mul_sub, abs_mul]
        exact mul_le_mul
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m (k * n - h))
          hkerm (abs_nonneg _) (Nat.cast_nonneg _)
      · simpa only [if_neg hcut, zero_mul, sub_zero, abs_zero] using hnp
    dsimp only [logarithmicUpwardOffset, linearizedUpwardOffset]
    rw [add_mul, add_sub_add_comm]
    exact (abs_add_le _ _).trans ((add_le_add hp hm).trans_eq (by ring))
  unfold logarithmicUpwardCoefficient linearizedUpwardCoefficient
  rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hM)]
  calc
    _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
        |(ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, logarithmicUpwardOffset φ c N m n k h -
          (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
        (ArithmeticFunction.vonMangoldt k : ℝ) / k * ((B : ℝ) * (2 * m.totient * C / N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro k hk
      rw [← mul_sub, ← sum_sub_distrib, abs_mul,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h := (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun h hh => hpoint k hk h hh)
      simpa only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] using h
    _ = D * mertensSum (N + B) / N := by
      rw [← sum_mul]
      dsimp only [D, mertensSum]
      ring

/-- The literal logarithmic-kernel error has a common constant before its totient factor. -/
theorem exists_logarithmicUpwardCoefficient_uniform_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, ∀ c : ℝ, 1 ≤ c →
      ∀ B N : ℕ, 1 ≤ N → c / N ≤ 1 →
      2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) → ∀ n : ℕ, 1 ≤ n →
        |logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n| ≤
          D * (m.totient : ℝ) * c ^ 2 * ((B : ℝ) + 1) ^ 3 * mertensSum (N + B) / N := by
  obtain ⟨C, hC, hbound⟩ := exists_logPrimeKernel_polynomial_bound hφ hsupp
  let D := 2 * C / (∫ u, φ u ^ 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro m c hc B N hN hw hlarge n hn
  have hker := hbound c hc B N hN hw hlarge
  have herr := logarithmicUpwardCoefficient_error_of_uniform_kernel hM c (m := m) hN hn
    (show 0 ≤ C * c ^ 2 * ((B : ℝ) + 1) ^ 2 by positivity) hker
  have hcoef : 2 * (B : ℝ) * m.totient * (C * c ^ 2 * ((B : ℝ) + 1) ^ 2) / (∫ u, φ u ^ 2) ≤
      D * (m.totient : ℝ) * c ^ 2 * ((B : ℝ) + 1) ^ 3 := by
    calc
      _ = (D * (m.totient : ℝ) * c ^ 2 * ((B : ℝ) + 1) ^ 2) * (B : ℝ) := by
        dsimp only [D]; ring
      _ ≤ (D * (m.totient : ℝ) * c ^ 2 * ((B : ℝ) + 1) ^ 2) * ((B : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hmert : 0 ≤ mertensSum (N + B) :=
    sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
  exact herr.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hmert) (Nat.cast_nonneg N))

#print axioms exists_logarithmicUpwardCoefficient_uniform_conductor_bound


private theorem uniform_quotient_lt_twice_floor {N n : ℕ} (hn : n ∈ Icc 1 N) :
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

/-- Both literal cutoff changes have an explicit totient-squared budget. -/
theorem linearizedUpwardCoefficient_boundary_uniform_conductor_budget {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 1 ≤ m) :
    ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ (N : ℝ) → ∀ B : ℕ,
      (∑ n ∈ Icc 1 N,
        ((linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) /
          Real.sqrt n) ^ 2) ≤ (10 * (32 * (m.totient : ℝ)) ^ 2) * ((B : ℝ) + 1) ^ 5 := by
  let D : ℝ := 32 * m.totient
  have hD : 0 < D := by
    have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
    dsimp only [D]
    positivity
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
    have hquot := uniform_quotient_lt_twice_floor hn
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

private theorem uniform_mertensSum_add_le_log_multiple {N B : ℕ} (hN : 1 ≤ N)
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

/-- Inverse-horizon kernel decay is uniform before the conductor factor. -/
theorem exists_logarithmicUpward_uniform_conductor_harmonic_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log (N : ℝ) →
      ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 → ∀ B : ℕ, B ≤ N →
      2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) →
      (∑ n ∈ Icc 1 N,
        ((logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) /
          Real.sqrt n) ^ 2) / Real.log N ≤
        K * (m.totient : ℝ) ^ 2 * c ^ 4 * ((B : ℝ) + 1) ^ 6 * (Real.log (N : ℝ) / N) ^ 2 := by
  obtain ⟨D, hD, hsource⟩ := exists_logarithmicUpwardCoefficient_uniform_conductor_bound hφ hsupp hM
  let E := D * (Real.log 4 + 6)
  refine ⟨2 * E ^ 2, by positivity, ?_⟩
  intro m N hN hL c hc hw B hBN hlarge
  let a := E * (m.totient : ℝ) * c ^ 2 * ((B : ℝ) + 1) ^ 3 * (Real.log N / N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have ha : ∀ n : ℕ, 1 ≤ n →
      |logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n| ≤ a := by
    intro n hn
    refine (hsource m c hc B N hN hw hlarge n hn).trans ?_
    calc
      _ ≤ D * (m.totient : ℝ) * c ^ 2 * ((B : ℝ) + 1) ^ 3 * ((Real.log 4 + 6) * Real.log N) / N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (uniform_mertensSum_add_le_log_multiple hN hL hBN) (by positivity)) hN0.le
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

#print axioms linearizedUpwardCoefficient_boundary_uniform_conductor_budget
#print axioms exists_logarithmicUpward_uniform_conductor_harmonic_bound

/-- Every logarithmic conductor family shares the actual upward-source bound,
including both prime-index cutoffs and the logarithmic kernel. -/
theorem exists_actualUpward_uniform_conductor_harmonic_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) / Real.log N ≤
          K * (m.totient : ℝ) ^ 2 *
            (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
              c ^ 3 / Real.sqrt (Real.log N)) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_logarithmicUpward_uniform_conductor_harmonic_bound hφ hsupp hM
  obtain ⟨Cs, hCs, hs⟩ := exists_conductor_uniform_reciprocalUpward_harmonic_bound hφ hsupp hM
  let d : ℝ := Real.exp 1 + 2
  let Ca' := Ca * d ^ 6
  let Cb' := (10 * (32 : ℝ) ^ 2) * d ^ 5
  have hd : 0 < d := by dsimp only [d]; positivity
  have hCa' : 0 ≤ Ca' := by dsimp only [Ca']; positivity
  have hCb' : 0 ≤ Cb' := by dsimp only [Cb']; positivity
  let K := 3 * (Ca' + Cb' + Cs)
  refine ⟨K, by dsimp only [K]; positivity, fun A hA => ?_⟩
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hs A hA, eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1]
    with N hsource hN hlog
  intro m hm hmN c hc hlarge
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hlog
  let B := linearPrimeStrip c
  have hBc : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; nlinarith only [hBc, hc]
  have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
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
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc0.le
    have hce : c ≤ c * Real.exp 1 := by simpa only [mul_one] using h
    exact hce.trans (Nat.le_ceil _)
  let R := c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
    c ^ 3 / Real.sqrt (Real.log N)
  have hR1 : c ^ 5 / Real.log N ≤ R := by
    dsimp only [R]
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ c ^ 10 * (Real.log (N : ℝ) / N) ^ 2)).trans
      (le_add_of_nonneg_right (by positivity))
  have hR2 : c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 ≤ R := by
    dsimp only [R]
    have h1 : 0 ≤ c ^ 5 / Real.log N := by positivity
    have h3 : 0 ≤ c ^ 3 / Real.sqrt (Real.log N) := by positivity
    linarith only [h1, h3]
  have hR3 : c ^ 3 / Real.sqrt (Real.log N) ≤ R := by
    dsimp only [R]
    exact le_add_of_nonneg_left (by positivity)
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let r : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  have ha' : (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N ≤ Ca' * (m.totient : ℝ) ^ 2 * R := by
    have hp := pow_le_pow_left₀ (show 0 ≤ (B : ℝ) + 1 by positivity) hB1 6
    have hb := (ha m N hN hlog c hc hwidth B hBN hkernel).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (show 0 ≤ Ca * (m.totient : ℝ) ^ 2 * c ^ 4 by positivity))
        (sq_nonneg (Real.log (N : ℝ) / N)))
    have hb' : (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N ≤
        Ca' * (m.totient : ℝ) ^ 2 * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) :=
      hb.trans_eq (by dsimp only [Ca']; ring)
    exact hb'.trans (mul_le_mul_of_nonneg_left hR2 (by positivity))
  have hb' : (∑ n ∈ Icc 1 N, b n ^ 2) / Real.log N ≤ Cb' * (m.totient : ℝ) ^ 2 * R := by
    have hb := linearizedUpwardCoefficient_boundary_uniform_conductor_budget hφ hsupp hM hm
      N hN c hc0 hcN B
    have hp := pow_le_pow_left₀ (show 0 ≤ (B : ℝ) + 1 by positivity) hB1 5
    have hb₀ := hb.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    have hb₁ : (∑ n ∈ Icc 1 N, b n ^ 2) / Real.log N ≤
        Cb' * (m.totient : ℝ) ^ 2 * (c ^ 5 / Real.log N) := by
      exact (div_le_div_of_nonneg_right hb₀ hL0.le).trans_eq (by dsimp only [Cb']; ring)
    exact hb₁.trans (mul_le_mul_of_nonneg_left hR1 (by positivity))
  have hr' : (∑ n ∈ Icc 1 N, r n ^ 2) / Real.log N ≤ Cs * (m.totient : ℝ) ^ 2 * R := by
    have hb := hsource m hm hmN c hc B hB
    exact hb.trans (by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hR3 (by positivity))
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) : actualUpwardRowError φ c N m n = a n + b n + r n := by
    have hsqrt : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < n)).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt n := by
      apply (eq_div_iff hsqrt).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width
        hsupp hc0 hn hwidth m
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
  exact hfinal.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha' hb') hr')
    (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by dsimp only [K, R]; ring))

/-- The norm of the literal upward residual is uniform over logarithmic conductor families. -/
theorem exists_normalizedUpward_uniform_conductor_harmonic_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖normalizedUpwardPrimeResidual φ c N m‖ ^ 2 ≤ K * (m.totient : ℝ) ^ 2 *
          (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
            c ^ 3 / Real.sqrt (Real.log N)) := by
  simpa only [normalizedUpwardPrimeResidual_norm_sq] using
    exists_actualUpward_uniform_conductor_harmonic_bound hφ hsupp hM

#print axioms exists_actualUpward_uniform_conductor_harmonic_bound
#print axioms exists_normalizedUpward_uniform_conductor_harmonic_bound

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
