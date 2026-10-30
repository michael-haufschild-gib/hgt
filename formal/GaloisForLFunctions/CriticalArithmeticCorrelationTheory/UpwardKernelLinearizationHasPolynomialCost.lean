import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmallWidthKeepsPrimeGeometryPolynomial
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsRealizeTheCompletedShellCorrection

/-!
# Polynomial cost of upward logarithmic-kernel replacement

Small physical width confines active logarithmic and reciprocal kernels to
indices of size at least `N/((e+3)c)`. Taylor linearization and the square-root
Jacobian then cost `O(c²(B+1)²/N)` on a strip of width `B`. Summation retains
all prime powers and both cutoffs. Bounded Mertens finite part and harmonic
summation give the normalized squared bound `O(c⁴(B+1)⁶/√(log N))`.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem one_le_abs_nat_gap {T j : ℕ} (hne : T ≠ j) :
    (1 : ℝ) ≤ |(j : ℝ) - T| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hstep : (T : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr h
    rw [abs_of_nonneg (by linarith only [hstep])]
    linarith only [hstep]
  · have hstep : (j : ℝ) + 1 ≤ T := by exact_mod_cast Nat.succ_le_iff.mpr h
    rw [abs_of_nonpos (by linarith only [hstep])]
    linarith only [hstep]

/-- Logarithmic linearization costs a polynomial in overlap and integer strip width. -/
theorem exists_logPrimeKernel_polynomial_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ B N : ℕ, 1 ≤ N → c / N ≤ 1 →
      2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) → ∀ T j : ℕ,
      1 ≤ T → 1 ≤ j → T ≠ j → |(j : ℝ) - T| ≤ B →
      |Real.sqrt T / Real.sqrt j *
          shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log T)) -
        shellAutocorr φ ((N : ℝ) / c * (((j : ℝ) - T) / T))| ≤
          C * c ^ 2 * ((B : ℝ) + 1) ^ 2 / N := by
  obtain ⟨L, hL⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  let a : ℝ := Real.exp 1 + 3
  let C : ℝ := 4 * (L : ℝ) * a ^ 2 + a * (∫ u, φ u ^ 2)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hM0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro c hc1 B N hN1 hw hlarge T j hT hj hne hgap
  have hc : 0 < c := zero_lt_one.trans_le hc1
  let A := a * c
  have hA : 0 ≤ A := mul_nonneg ha hc.le
  have hca : c * Real.exp 1 ≤ A := by dsimp only [A, a]; nlinarith only [hc]
  have h2ca : 2 * c ≤ A := by
    have hexp := Real.exp_pos 1
    dsimp only [A, a]
    nlinarith only [hexp, hc]
  have hcA : c ≤ A := (by linarith only [hc] : c ≤ 2 * c).trans h2ca
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlargec : 2 * c * (B : ℝ) ≤ N :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcA (by norm_num))
      (Nat.cast_nonneg B)).trans hlarge
  have hconst : (4 * (L : ℝ) * A ^ 2 * (B : ℝ) ^ 2 / c +
      A * B * (∫ u, φ u ^ 2)) / N ≤ C * c ^ 2 * ((B : ℝ) + 1) ^ 2 / N := by
    apply div_le_div_of_nonneg_right _ hN0.le
    have hdiv := div_le_self (show 0 ≤ 4 * (L : ℝ) * A ^ 2 * (B : ℝ) ^ 2 by positivity) hc1
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have hB2 : (B : ℝ) ^ 2 ≤ ((B : ℝ) + 1) ^ 2 := by nlinarith only [hB0]
    have hB1 : (B : ℝ) ≤ ((B : ℝ) + 1) ^ 2 := by nlinarith only [hB0, sq_nonneg (B : ℝ)]
    have hc2 : c ≤ c ^ 2 := by nlinarith only [hc1]
    have hfirst : 4 * (L : ℝ) * A ^ 2 * (B : ℝ) ^ 2 / c ≤
        4 * (L : ℝ) * a ^ 2 * c ^ 2 * ((B : ℝ) + 1) ^ 2 := by
      refine hdiv.trans ?_
      dsimp only [A]
      rw [mul_pow]
      have h := mul_le_mul_of_nonneg_left hB2
        (show 0 ≤ 4 * (L : ℝ) * (a ^ 2 * c ^ 2) by positivity)
      simpa only [mul_assoc] using h
    have hsecond : A * B * (∫ u, φ u ^ 2) ≤
        (a * (∫ u, φ u ^ 2)) * c ^ 2 * ((B : ℝ) + 1) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul hc2 hB1 hB0 (sq_nonneg c)) (mul_nonneg ha hM0)
      dsimp only [A]
      nlinarith only [h]
    calc
      _ ≤ 4 * (L : ℝ) * a ^ 2 * c ^ 2 * ((B : ℝ) + 1) ^ 2 +
          (a * (∫ u, φ u ^ 2)) * c ^ 2 * ((B : ℝ) + 1) ^ 2 := add_le_add hfirst hsecond
      _ = _ := by dsimp only [C]; ring
  by_cases hact : shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log T)) = 0
  · by_cases hlin : shellAutocorr φ ((N : ℝ) / c * (((j : ℝ) - T) / T)) = 0
    · rw [hact, hlin, mul_zero, sub_self, abs_zero]
      exact div_nonneg (mul_nonneg (mul_nonneg hC (sq_nonneg c)) (sq_nonneg _)) hN0.le
    · have hsmall : |(N : ℝ) / c * (((j : ℝ) - T) / T)| < 1 := by
        by_contra h
        exact hlin (shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (le_of_not_gt h))
      rw [abs_mul, abs_of_pos (div_pos hN0 hc), abs_div, abs_of_pos hT0] at hsmall
      have hsep := one_le_abs_nat_gap hne
      have hfrac : (N : ℝ) / c * (1 / T) < 1 :=
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsep hT0.le)
          (div_pos hN0 hc).le).trans_lt hsmall
      have hNT : (N : ℝ) ≤ c * T := by
        have h := (div_lt_one (mul_pos hc hT0)).mp
          (show (N : ℝ) / (c * T) < 1 by convert hfrac using 1; ring)
        exact h.le
      have hTj : (T : ℝ) ≤ j + B := by linarith only [(abs_le.mp hgap).1]
      have hNj : (N : ℝ) ≤ 2 * c * j := by
        have hmul := mul_le_mul_of_nonneg_left hTj hc.le
        linarith only [hNT, hmul, hlargec]
      exact (abs_sqrt_log_kernel_sub_linear_le hL
        (fun t => abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) t)
        hc hN0 hA (Nat.cast_nonneg B) hT0 hj0 hgap
        (hNT.trans (mul_le_mul_of_nonneg_right hcA hT0.le))
        (hNj.trans (mul_le_mul_of_nonneg_right h2ca hj0.le)) hlarge).trans hconst
  · have hsmall : |(N : ℝ) / c * (Real.log j - Real.log T)| < 1 := by
      by_contra h
      exact hact (shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (le_of_not_gt h))
    have hlog : |Real.log j - Real.log T| ≤ c / N := by
      rw [abs_mul, abs_of_pos (div_pos hN0 hc)] at hsmall
      have h := (lt_div_iff₀ (div_pos hN0 hc)).mpr
        (show |Real.log j - Real.log T| * ((N : ℝ) / c) < 1 by simpa only [mul_comm] using hsmall)
      have heq : 1 / ((N : ℝ) / c) = c / N := by field_simp
      rw [heq] at h
      exact h.le
    obtain ⟨hNT, hNj⟩ := logWindow_integer_separation_small_width hc hN1 hT hj hne hlog hw
    exact (abs_sqrt_log_kernel_sub_linear_le hL
      (fun t => abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) t)
      hc hN0 hA (Nat.cast_nonneg B) hT0 hj0 hgap
      (hNT.trans (mul_le_mul_of_nonneg_right hca hT0.le))
      (hNj.trans (mul_le_mul_of_nonneg_right hca hj0.le)) hlarge).trans hconst

private theorem logarithmicUpwardCoefficient_error_of_kernel_bound {φ : ℝ → ℝ}
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

/-- Summing the literal logarithmic-kernel errors retains polynomial overlap and strip costs. -/
theorem exists_logarithmicUpwardCoefficient_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ c : ℝ, 1 ≤ c → ∀ B N : ℕ, 1 ≤ N → c / N ≤ 1 →
      2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) → ∀ n : ℕ, 1 ≤ n →
      |logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n| ≤
        D * c ^ 2 * ((B : ℝ) + 1) ^ 3 * mertensSum (N + B) / N := by
  obtain ⟨C, hC, hbound⟩ := exists_logPrimeKernel_polynomial_bound hφ hsupp
  let D := 2 * m.totient * C / (∫ u, φ u ^ 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro c hc B N hN hw hlarge n hn
  have hker := hbound c hc B N hN hw hlarge
  have herr := logarithmicUpwardCoefficient_error_of_kernel_bound hM c (m := m) hN hn
    (show 0 ≤ C * c ^ 2 * ((B : ℝ) + 1) ^ 2 by positivity) hker
  have hcoef : 2 * (B : ℝ) * m.totient * (C * c ^ 2 * ((B : ℝ) + 1) ^ 2) / (∫ u, φ u ^ 2) ≤
      D * c ^ 2 * ((B : ℝ) + 1) ^ 3 := by
    calc
      _ = (D * c ^ 2 * ((B : ℝ) + 1) ^ 2) * (B : ℝ) := by dsimp only [D]; ring
      _ ≤ (D * c ^ 2 * ((B : ℝ) + 1) ^ 2) * ((B : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hmert : 0 ≤ mertensSum (N + B) :=
    sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
  exact herr.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hmert) (Nat.cast_nonneg N))

private theorem exists_mertensSum_add_le_log_multiple :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ N B : ℕ, 1 ≤ N → 1 ≤ Real.log (N : ℝ) → B ≤ N →
      mertensSum (N + B) ≤ (J + 2) * Real.log N := by
  obtain ⟨J, hJ⟩ := tendsto_mertensSum_sub_log.abs.bddAbove_range
  have hJ0 : 0 ≤ J := (abs_nonneg _).trans (hJ ⟨0, rfl⟩)
  refine ⟨J, hJ0, ?_⟩
  intro N B hN hL hBN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNB0 : (0 : ℝ) < (N + B : ℕ) := by exact_mod_cast (show 0 < N + B by omega)
  have hlog : Real.log ((N + B : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have hsum : ((N + B : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast (show N + B ≤ 2 * N by omega)
    have h := Real.log_le_log hNB0 hsum
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at h
    have htwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    linarith only [h, htwo, hL]
  have herr := (abs_le.mp (hJ ⟨N + B, rfl⟩)).2
  have hmul := mul_le_mul_of_nonneg_left hL hJ0
  linarith only [herr, hlog, hmul]

private theorem log_div_self_sq_le_sqrt_log {N : ℕ} (hN : 1 ≤ N)
    (hL : 1 ≤ Real.log (N : ℝ)) :
    (Real.log (N : ℝ) / N) ^ 2 ≤ 4 / Real.sqrt (Real.log N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hlog : Real.log (N : ℝ) ≤ 2 * Real.sqrt N := by
    have h := _root_.RHTower.WeilAbscissa.log_div_sqrt_le hN1
    have hh : Real.log (N : ℝ) / Real.sqrt N ≤ 2 := by simpa only [div_eq_mul_inv] using h
    exact (div_le_iff₀ hsN).mp hh
  have hlog2 : Real.log (N : ℝ) ^ 2 ≤ 4 * N := by
    have h := pow_le_pow_left₀ hL0.le hlog 2
    rw [mul_pow, Real.sq_sqrt hN0.le] at h
    norm_num at h ⊢
    exact h
  have hs : Real.sqrt (Real.log N) ≤ N := by
    have hb := Real.log_le_sub_one_of_pos hN0
    have hsq := Real.sq_sqrt hL0.le
    nlinarith only [hb, hsq, hN1, Real.sqrt_nonneg (Real.log N)]
  calc
    _ = Real.log (N : ℝ) ^ 2 / (N : ℝ) ^ 2 := div_pow _ _ 2
    _ ≤ (4 * N) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right hlog2 (sq_nonneg _)
    _ = 4 / (N : ℝ) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hsL hs

/-- The full logarithmic-kernel replacement has a polynomial harmonic norm estimate. -/
theorem exists_logarithmicUpwardCoefficient_polynomial_harmonic_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log (N : ℝ) →
      ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 → ∀ B : ℕ, B ≤ N →
      2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) →
      (∑ n ∈ Icc 1 N,
        ((logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) /
          Real.sqrt n) ^ 2) / Real.log N ≤
        K * c ^ 4 * ((B : ℝ) + 1) ^ 6 / Real.sqrt (Real.log N) := by
  obtain ⟨D, hD, hsource⟩ := exists_logarithmicUpwardCoefficient_polynomial_bound hφ hsupp hM m
  obtain ⟨J, hJ, hmert⟩ := exists_mertensSum_add_le_log_multiple
  let E := D * (J + 2)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨8 * E ^ 2, by positivity, ?_⟩
  intro N hN hL c hc hw B hBN hlarge
  let a := E * c ^ 2 * ((B : ℝ) + 1) ^ 3 * (Real.log N / N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have ha : ∀ n : ℕ, 1 ≤ n →
      |logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n| ≤ a := by
    intro n hn
    refine (hsource c hc B N hN hw hlarge n hn).trans ?_
    calc
      _ ≤ D * c ^ 2 * ((B : ℝ) + 1) ^ 3 * ((J + 2) * Real.log N) / N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hmert N B hN hL hBN) (by positivity)) hN0.le
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
    _ = (2 * E ^ 2 * c ^ 4 * ((B : ℝ) + 1) ^ 6) * (Real.log (N : ℝ) / N) ^ 2 := by
      dsimp only [a]
      ring
    _ ≤ (2 * E ^ 2 * c ^ 4 * ((B : ℝ) + 1) ^ 6) * (4 / Real.sqrt (Real.log N)) :=
      mul_le_mul_of_nonneg_left (log_div_self_sq_le_sqrt_log hN hL) (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_logPrimeKernel_polynomial_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_logarithmicUpwardCoefficient_polynomial_bound

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_logarithmicUpwardCoefficient_polynomial_harmonic_bound
