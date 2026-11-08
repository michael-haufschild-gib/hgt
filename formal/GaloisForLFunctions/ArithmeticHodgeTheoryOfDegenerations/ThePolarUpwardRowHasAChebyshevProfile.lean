import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation

/-!
# The polar upward row has a Chebyshev profile

The affine shell mean is uniform on every fixed terminal fraction of the horizon.
Summing over the finitely many prime multipliers leaves a bounded row error.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The reciprocal polar upward row equals its finite Mangoldt mean up to a uniformly bounded
error on every fixed terminal fraction of the horizon. -/
theorem exists_abs_reciprocalUpward_one_sub_mean_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ} {N n : ℕ}, 1 ≤ c → 1 ≤ N →
      n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N →
      |reciprocalUpwardCoefficient tiltedUnitSpline c (linearPrimeStrip c) N 1 n -
        ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
          (c * n / N) * (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ))| ≤ C := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  obtain ⟨K, hK⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hKL : ∀ x y : ℝ, |shellAutocorr tiltedUnitSpline x - shellAutocorr tiltedUnitSpline y| ≤
      (K : ℝ) * |x - y| := fun x y => by
    simpa only [Real.dist_eq] using hK.dist_le_mul x y
  let D : ℝ := 4 * (K : ℝ) / ((∫ u, tiltedUnitSpline u ^ 2) * δ)
  refine ⟨(⌊1 / δ⌋₊ : ℝ) * D, by dsimp only [D]; positivity, ?_⟩
  intro c N n hc hN hn
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
  have hnN : n ≤ N := (mem_Ioc.mp hn).2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn_gt : δ * N < n := (Nat.lt_floor_add_one (δ * N)).trans_le
    (by exact_mod_cast Nat.succ_le_of_lt (mem_Ioc.mp hn).1)
  have hB : ⌈c⌉₊ ≤ linearPrimeStrip c := by
    apply Nat.ceil_le.mpr
    have he := mul_le_mul_of_nonneg_left (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) hc0.le
    exact (by simpa only [mul_one] using he : c ≤ c * Real.exp 1).trans (Nat.le_ceil _)
  have hceil : (⌈c⌉₊ : ℝ) ≤ 2 * c := by
    have hh := (Nat.ceil_lt_add_one hc0.le).le
    linarith only [hh, hc]
  rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc0 hB N 1 n hn1,
    affinePrimeShellCorrection_symm_eq_sum_upwardShellModel hφ hsupp hc0 (by norm_num)
      (mem_Icc.mpr ⟨hn1, hnN⟩)]
  let a : ℝ := (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)
  have hmean : a * (c * n / N) * (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ)) =
      ∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, ((ArithmeticFunction.vonMangoldt k : ℝ) / k) * (a * (c * (k * n : ℕ) / N)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by have := (mem_Icc.mp hk).1; omega)
    push_cast
    field_simp [hk0]
  change |(∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊,
      ((ArithmeticFunction.vonMangoldt k : ℝ) / k) * upwardShellModel tiltedUnitSpline c N 1 ⌈c⌉₊ (k * n)) -
      a * (c * n / N) * (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ))| ≤ _
  rw [hmean, ← sum_sub_distrib]
  have hterm : ∀ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊,
      |((ArithmeticFunction.vonMangoldt k : ℝ) / k) * upwardShellModel tiltedUnitSpline c N 1 ⌈c⌉₊ (k * n) -
        ((ArithmeticFunction.vonMangoldt k : ℝ) / k) * (a * (c * (k * n : ℕ) / N))| ≤ ((ArithmeticFunction.vonMangoldt k : ℝ) / k) * D := by
    intro k hk
    have hk1 := (mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hknN : k * n ≤ N := by
      have hf := (Nat.le_floor_iff (by positivity : 0 ≤ (N : ℝ) / n)).mp (mem_Icc.mp hk).2
      have hh := (le_div_iff₀ hn0).mp hf
      exact_mod_cast hh
    have hkn1 : 1 ≤ k * n := Nat.mul_pos hk1 hn1
    have hkn : δ * N ≤ (k * n : ℕ) := by
      have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ k by exact_mod_cast hk1) hn0.le
      push_cast
      linarith only [hh, hn_gt]
    have hcp : δ * c ≤ c * (k * n : ℕ) / N := by
      apply (le_div_iff₀ hN0).mpr
      have hh := mul_le_mul_of_nonneg_left hkn hc0.le
      nlinarith only [hh]
    have hb := abs_upwardShellModel_one_sub_mean_le hφ hsupp hM hc0
      (NNReal.coe_nonneg K) hKL hkn1 hknN (Nat.le_ceil c)
    have herr : 2 * (K : ℝ) * ⌈c⌉₊ /
        ((∫ u, tiltedUnitSpline u ^ 2) * (c * (k * n : ℕ) / N)) ≤ D := by
      have hnum := mul_le_mul_of_nonneg_left hceil (show 0 ≤ 2 * (K : ℝ) by positivity)
      have hden := mul_le_mul_of_nonneg_left hcp hM.le
      calc
        _ ≤ (2 * (K : ℝ) * (2 * c)) / ((∫ u, tiltedUnitSpline u ^ 2) * (δ * c)) :=
          (div_le_div_of_nonneg_right hnum (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
        _ = D := by dsimp only [D]; field_simp [hc0.ne', hM.ne', hδ.ne']; ring
    rw [← mul_sub, abs_mul, abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hk0.le)]
    exact mul_le_mul_of_nonneg_left (hb.trans herr)
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hk0.le)
  have hcut : ⌊(N : ℝ) / n⌋₊ ≤ ⌊1 / δ⌋₊ :=
    Nat.floor_mono ((div_le_div_iff₀ hn0 hδ).mpr (by linarith only [hn_gt]))
  have hsum : (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) / k) ≤ ⌊1 / δ⌋₊ := by
    calc
      _ ≤ ∑ _k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (1 : ℝ) := by
        apply sum_le_sum
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
        rw [div_le_one hk0]
        linarith [ArithmeticFunction.vonMangoldt_le_log (n := k), Real.log_le_sub_one_of_pos hk0]
      _ = (⌊(N : ℝ) / n⌋₊ : ℝ) := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
      _ ≤ ⌊1 / δ⌋₊ := by exact_mod_cast hcut
  calc
    _ ≤ ∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, ((ArithmeticFunction.vonMangoldt k : ℝ) / k) * D :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) / k) * D := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by dsimp only [D]; positivity)

/-- The finite Mangoldt profile of the polar upward row. -/
def polarUpwardMeanVector (c : ℝ) (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
    (((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
      (c * idx.1 / N) * (∑ k ∈ Icc 1 ⌊(N : ℝ) / idx.1⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ))) /
      (Real.sqrt idx.1 * Real.sqrt (Real.log N)))

/-- The full polar upward row converges in the normalized top-window square norm to its
sampled finite Mangoldt profile. -/
theorem tendsto_topWindow_upward_polar_mean
    {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (upwardPrimeVector tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector 1 N) -
          polarUpwardMeanVector (c N) N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hrow⟩ := exists_abs_reciprocalUpward_one_sub_mean_le hδ
  have hlin := tendsto_topWindow_upward_linearization (m := 1) (by norm_num) hδ hc hR hcrit
  simp only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, inv_one, one_smul] at hlin
  let v : (N : ℕ) → EuclideanSpace ℝ (PrimeHorizonIndex N) := fun N =>
    WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
      reciprocalUpwardCoefficient tiltedUnitSpline (c N) (linearPrimeStrip (c N)) N 1 idx.1 /
        (Real.sqrt idx.1 * Real.sqrt (Real.log N)))
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hinv : Tendsto (fun N : ℕ => (C ^ 2 / δ) * (1 / c N ^ 2)) atTop (𝓝 0) := by
    have hh : Tendsto (fun N : ℕ => 1 / c N ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hcinf)
    simpa only [mul_zero] using hh.const_mul (C ^ 2 / δ)
  have hmodel : Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N (v N - polarUpwardMeanVector (c N) N)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N =>
      mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
        (topWindowResidualMass_nonneg δ N _)) ?_ hinv
    filter_upwards [eventually_ge_atTop 1,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
      with N hN hL
    change 0 < Real.log (N : ℝ) at hL
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        primeHorizonExtension (v N - polarUpwardMeanVector (c N) N) n ^ 2 ≤
          (C ^ 2 / Real.log N) * (1 / (n : ℝ)) := by
      intro n hn
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn).2⟩⟩
      have hext : primeHorizonExtension (v N - polarUpwardMeanVector (c N) N) n =
          (reciprocalUpwardCoefficient tiltedUnitSpline (c N) (linearPrimeStrip (c N)) N 1 n -
            ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
              (c N * n / N) * (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ))) /
                (Real.sqrt n * Real.sqrt (Real.log N)) := by
        change primeHorizonExtension (v N - polarUpwardMeanVector (c N) N) idx.1 = _
        rw [primeHorizonExtension_coe]
        change (reciprocalUpwardCoefficient tiltedUnitSpline (c N) (linearPrimeStrip (c N)) N 1 n /
            (Real.sqrt n * Real.sqrt (Real.log N))) -
          ((((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
            (c N * n / N) *
              (∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ))) /
            (Real.sqrt n * Real.sqrt (Real.log N))) = _
        exact (sub_div _ _ _).symm
      have hs := pow_le_pow_left₀ (abs_nonneg _) (hrow (hc N) hN hn) 2
      rw [sq_abs] at hs
      rw [hext, div_pow, mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hL.le]
      exact (div_le_div_of_nonneg_right hs (by positivity)).trans_eq (by ring)
    have hm : topWindowResidualMass δ N (v N - polarUpwardMeanVector (c N) N) ≤
        C ^ 2 / (δ * Real.log N) := by
      unfold topWindowResidualMass
      calc
        _ ≤ (C ^ 2 / Real.log N) * ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, 1 / (n : ℝ) :=
          (sum_le_sum hpt).trans_eq (mul_sum _ _ _).symm
        _ ≤ (C ^ 2 / Real.log N) * (1 / δ) :=
          mul_le_mul_of_nonneg_left (sum_topWindow_inv_le hδ hN) (by positivity)
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
      (by field_simp [hc0.ne', hL.ne', hδ.ne'])
  have hlim := (hlin.const_mul 2).add (hmodel.const_mul 2)
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) (Eventually.of_forall fun N => ?_) hlim
  have heq : upwardPrimeVector tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector 1 N) -
      polarUpwardMeanVector (c N) N =
      (upwardPrimeVector tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector 1 N) - v N) +
        (v N - polarUpwardMeanVector (c N) N) := by abel
  rw [heq]
  exact (mul_le_mul_of_nonneg_left (topWindowResidualMass_add_le δ N _ _)
    (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))).trans_eq (by dsimp only [v]; ring)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
