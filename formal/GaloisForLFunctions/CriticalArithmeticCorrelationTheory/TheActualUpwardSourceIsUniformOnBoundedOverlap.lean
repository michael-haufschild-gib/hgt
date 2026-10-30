import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsRealizeTheCompletedShellCorrection
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheBoundedOverlapShellErrorsVanishUniformlyInNorm

/-!
# The actual upward source is uniform on bounded overlap

One finite offset range controls every logarithmic prime-power kernel for `1 ≤ c ≤ K`.
The common geometric error and prime-index boundary mass vanish in harmonic norm. The uniform
signed affine-shell law supplies the remaining reciprocal source, so the literal infinite upward
residual has one smallness horizon over the entire bounded overlap interval.
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

/-- Common logarithmic kernel bound for every overlap in a bounded interval. -/
theorem exists_logPrimeKernel_uniform_overlap_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {K : ℝ} (hK : 1 ≤ K) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ T j : ℕ,
      1 ≤ T → 1 ≤ j → T ≠ j → |(j : ℝ) - T| ≤ B →
      |Real.sqrt T / Real.sqrt j *
          shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log T)) -
        shellAutocorr φ ((N : ℝ) / c * (((j : ℝ) - T) / T))| ≤ C / N := by
  obtain ⟨L, hL⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  let A := K * Real.exp K + 2 * K + 1
  let C := 4 * (L : ℝ) * A ^ 2 * (B : ℝ) ^ 2 + A * B * (∫ u, φ u ^ 2)
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hM0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, max 1 ⌈2 * A * B⌉₊, ?_⟩
  intro N hN c hc1 hcK T j hT hj hne hgap
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hce : c * Real.exp c ≤ K * Real.exp K :=
    mul_le_mul hcK (Real.exp_le_exp.mpr hcK) (Real.exp_pos c).le hK0.le
  have hca : c * Real.exp c ≤ A := by dsimp only [A]; linarith only [hce, hK0]
  have h2ca : 2 * c ≤ A := by
    have hKe := mul_pos hK0 (Real.exp_pos K)
    dsimp only [A]
    linarith only [hcK, hKe]
  have hcA : c ≤ A := (by linarith only [hc] : c ≤ 2 * c).trans h2ca
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlarge : 2 * A * (B : ℝ) ≤ N := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hN)
  have hlargec : 2 * c * (B : ℝ) ≤ N :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcA (by norm_num))
      (Nat.cast_nonneg B)).trans hlarge
  have hconst : (4 * (L : ℝ) * A ^ 2 * (B : ℝ) ^ 2 / c +
      A * B * (∫ u, φ u ^ 2)) / N ≤ C / N := by
    apply div_le_div_of_nonneg_right _ hN0.le
    have hdiv := div_le_self (show 0 ≤ 4 * (L : ℝ) * A ^ 2 * (B : ℝ) ^ 2 by positivity) hc1
    dsimp only [C]
    linarith only [hdiv]
  by_cases hact : shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log T)) = 0
  · by_cases hlin : shellAutocorr φ ((N : ℝ) / c * (((j : ℝ) - T) / T)) = 0
    · rw [hact, hlin, mul_zero, sub_self, abs_zero]
      exact div_nonneg hC hN0.le
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
    obtain ⟨hNT, hNj⟩ := logWindow_integer_separation hc hN1 hT hj hne hlog
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

/-- One finite-source geometric error bound covers every overlap and every smaller offset strip. -/
theorem exists_logarithmicUpwardCoefficient_uniform_overlap_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) (B₀ m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ B : ℕ, B ≤ B₀ → ∀ n : ℕ, 1 ≤ n →
      |logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n| ≤
        D * mertensSum (N + B₀) / N := by
  obtain ⟨C, hC, N₀, hker⟩ := exists_logPrimeKernel_uniform_overlap_bound hφ hsupp hK B₀
  let D := 2 * (B₀ : ℝ) * m.totient * C / (∫ u, φ u ^ 2)
  refine ⟨D, by dsimp only [D]; positivity, max 1 N₀, ?_⟩
  intro N hN c hc1 hcK B hB n hn
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNN : N₀ ≤ N := (le_max_right _ _).trans hN
  have hBreal : (B : ℝ) ≤ B₀ := by exact_mod_cast hB
  have hpoint := logarithmicUpwardCoefficient_error_of_kernel_bound hM c (m := m) hN1 hn hC
    (fun T j hT hj hne hgap => hker N hNN c hc1 hcK T j hT hj hne (hgap.trans hBreal))
  have hD : 2 * (B : ℝ) * m.totient * C / (∫ u, φ u ^ 2) ≤ D := by
    apply div_le_div_of_nonneg_right _ hM.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBreal zero_le_two)
        (Nat.cast_nonneg _)) hC
  have hmert0 : 0 ≤ mertensSum (N + B) := by
    unfold mertensSum
    exact sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
  have hmert : mertensSum (N + B) ≤ mertensSum (N + B₀) := by
    unfold mertensSum
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.add_le_add_left hB N))
      (fun k _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
  exact hpoint.trans (div_le_div_of_nonneg_right
    (mul_le_mul hD hmert hmert0 (by dsimp only [D]; positivity)) (Nat.cast_nonneg N))

private theorem tendsto_mertensSum_add_div_self (B : ℕ) :
    Tendsto (fun N : ℕ => mertensSum (N + B) / N) atTop (𝓝 0) := by
  have hadd : Tendsto (fun N : ℕ => N + B) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have herr := (tendsto_mertensSum_sub_log.comp hadd).div_atTop
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlogReal : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlog := hlogReal.comp (tendsto_natCast_atTop_atTop.comp hadd)
  have hratio : Tendsto (fun N : ℕ => ((N + B : ℕ) : ℝ) / N) atTop (𝓝 1) := by
    have hz : Tendsto (fun N : ℕ => (B : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (B : ℝ)
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hz
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [Nat.cast_add, add_div, div_self hN0]
  have hlim := herr.add (hlog.mul hratio)
  simp only [zero_mul, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNB0 : ((N + B : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show N + B ≠ 0 by omega)
  dsimp only [Function.comp_apply]
  field_simp
  ring

/-- The geometric error has one vanishing harmonic norm bound over bounded overlaps and strips. -/
theorem eventually_logarithmicUpwardCoefficient_error_sq_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) (B₀ m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ B : ℕ, B ≤ B₀ →
      (∑ n ∈ Icc 1 N,
        ((logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) /
          Real.sqrt n) ^ 2) / Real.log N ≤ ε := by
  obtain ⟨D, hD, N₀, hbound⟩ := exists_logarithmicUpwardCoefficient_uniform_overlap_bound hφ hsupp hM hK B₀ m
  let a : ℕ → ℝ := fun N => D * mertensSum (N + B₀) / N
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, mul_div_assoc, mul_zero] using (tendsto_mertensSum_add_div_self B₀).const_mul D
  have hlim := (ha.pow 2).mul GaloisForLFunctions.tendsto_harmonic_div_log
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hlim
  filter_upwards [eventually_ge_atTop N₀, hlim.eventually (ge_mem_nhds hε)] with N hN hsmall
  intro c hc1 hcK B hB
  have hsum : (∑ n ∈ Icc 1 N,
      ((logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) /
        Real.sqrt n) ^ 2) ≤ a N ^ 2 * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, a N ^ 2 / (n : ℝ) := by
        apply sum_le_sum
        intro n hn
        have hb := hbound N hN c hc1 hcK B hB n (mem_Icc.mp hn).1
        have hsq := mul_self_le_mul_self (abs_nonneg _) hb
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        simpa only [← sq, sq_abs] using hsq
      _ = a N ^ 2 * (harmonic N : ℝ) := by
        rw [← RHTower.Sieve.sum_Icc_one_div_eq_harmonic, mul_sum]
        exact sum_congr rfl fun n _ => by ring
  have hfinal := div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)
  exact hfinal.trans (by simpa only [mul_div_assoc] using hsmall)

/-- Enlarging the prime-index boundary strip can only increase its nonnegative source mass. -/
theorem primeIndexBoundaryMass_mono {B B₀ : ℕ} (hB : B ≤ B₀) (Y : ℕ) :
    primeIndexBoundaryMass B Y ≤ primeIndexBoundaryMass B₀ Y := by
  apply sum_le_sum_of_subset_of_nonneg
  · exact Icc_subset_Icc (by omega) (by omega)
  · intro k _ _
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)

/-- Both actual horizon cutoffs have one vanishing boundary norm over bounded overlap. -/
theorem eventually_linearizedUpwardCoefficient_boundary_sq_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (B₀ : ℕ) {m : ℕ} (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ B : ℕ, B ≤ B₀ →
      (∑ n ∈ Icc 1 N,
        ((linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) /
          Real.sqrt n) ^ 2) / Real.log N ≤ ε := by
  let f : ℕ → ℝ := fun Y => 4 * B₀ * m.totient * primeIndexBoundaryMass B₀ Y
  have hf0 (Y : ℕ) : 0 ≤ f Y := by
    have hmass : 0 ≤ primeIndexBoundaryMass B₀ Y :=
      sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
    dsimp only [f]
    positivity
  let R : ℕ → ℕ → ℝ := fun N n => f (N / n) / Real.sqrt n
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [f, mul_zero] using (tendsto_primeIndexBoundaryMass B₀).const_mul (4 * B₀ * m.totient : ℝ)
  have hlim := HTGeometry.tendsto_harmonicQuotient_square_error hf R
    (fun N n _ => by
      dsimp only [R]
      rw [abs_div, abs_of_nonneg (hf0 _), abs_of_nonneg (Real.sqrt_nonneg n)])
  filter_upwards [eventually_ge_atTop ⌈K⌉₊, hlim.eventually (ge_mem_nhds hε)] with N hN hsmall
  intro c hc1 hcK B hB
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hNc : c ≤ (N : ℝ) := hcK.trans ((Nat.le_ceil _).trans (by exact_mod_cast hN))
  have hsum : (∑ n ∈ Icc 1 N,
      ((linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) /
        Real.sqrt n) ^ 2) ≤ ∑ n ∈ Icc 1 N, R N n ^ 2 := by
    apply sum_le_sum
    intro n hn
    have hmass : 0 ≤ primeIndexBoundaryMass B (N / n) :=
      sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
    have hcoef : (4 : ℝ) * B * m.totient ≤ 4 * B₀ * m.totient :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hB) (by norm_num)) (Nat.cast_nonneg _)
    have hrow : |(linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) /
        Real.sqrt n| ≤ R N n := by
      rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg n)
      exact (abs_linearizedUpwardCoefficient_sub_reciprocal_le hφ hsupp hM hc hm (mem_Icc.mp hn).1 hNc).trans
        (mul_le_mul hcoef (primeIndexBoundaryMass_mono hB (N / n)) hmass (by positivity))
    have hsq := mul_self_le_mul_self (abs_nonneg _) hrow
    simpa only [← sq, sq_abs] using hsq
  exact (div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)).trans hsmall

/-- The symmetric reciprocal source has its signed shell mean uniformly on bounded overlap. -/
theorem eventually_reciprocalUpwardCoefficient_shell_sq_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ B : ℕ, ⌈c⌉₊ ≤ B →
      (∑ n ∈ Icc 1 N,
        ((reciprocalUpwardCoefficient φ c B N m n -
          ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) / Real.log N ≤ ε := by
  filter_upwards [eventually_shiftedReciprocalUpwardRowError_sq_uniform_overlap hm hφ hsupp hM hK hε]
    with N hN
  intro c hc1 hcK B hB
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hid : shellCorrectionOfShift φ c m id = shellCorrection φ c m := rfl
  have hrow (n : ℕ) (hn : 1 ≤ n) :
      (reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n =
      (shiftedReciprocalUpwardRowError φ c id N m n +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
    rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc hB N m n hn]
    dsimp only [shiftedReciprocalUpwardRowError]
    rw [hid, shellCorrectionOfShift_reflected hm]
    ring
  have hsum : (∑ n ∈ Icc 1 N,
      ((reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) ≤
      ∑ n ∈ Icc 1 N, (shiftedReciprocalUpwardRowError φ c id N m n ^ 2 +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n ^ 2) / 2 := by
    apply sum_le_sum
    intro n hn
    rw [hrow n (mem_Icc.mp hn).1]
    nlinarith only [sq_nonneg (shiftedReciprocalUpwardRowError φ c id N m n -
      shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n)]
  have hfinal := div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)
  rw [← sum_div, sum_add_distrib] at hfinal
  have hp := hN c hc1 hcK id
  have hn := hN c hc1 hcK (reflectedAffineShift m)
  have havg : ((∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c id N m n ^ 2) +
      ∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n ^ 2) /
      2 / Real.log N ≤ ε := by
    rw [div_right_comm, add_div]
    linarith only [hp, hn]
  exact hfinal.trans havg

/-- The literal infinite upward action realizes its shell correction uniformly on bounded overlap. -/
theorem eventually_actualUpwardRowError_sq_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) / Real.log N ≤ ε := by
  have hε9 : 0 < ε / 9 := div_pos hε (by norm_num)
  filter_upwards [eventually_logarithmicUpwardCoefficient_error_sq_uniform_overlap hφ hsupp hM hK
      (exteriorPrimeStrip K) m hε9,
    eventually_linearizedUpwardCoefficient_boundary_sq_uniform_overlap hφ hsupp hM
      (exteriorPrimeStrip K) hm hε9,
    eventually_reciprocalUpwardCoefficient_shell_sq_uniform_overlap hφ hsupp hM hK hm hε9]
    with N ha hb hd
  intro c hc1 hcK
  have hc : 0 < c := zero_lt_one.trans_le hc1
  let B := exteriorPrimeStrip c
  have hBmax : B ≤ exteriorPrimeStrip K := by
    apply Nat.ceil_mono
    exact mul_le_mul hcK (Real.exp_le_exp.mpr hcK) (Real.exp_pos c).le
      (zero_lt_one.trans_le hK).le
  have hB : ⌈c⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have he : c ≤ c * Real.exp c := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr hc.le) hc.le
    exact he.trans (Nat.le_ceil _)
  let a : ℕ → ℕ → ℝ := fun N n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℕ → ℝ := fun N n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let d : ℕ → ℕ → ℝ := fun N n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  have hrow (N n : ℕ) (hn : n ∈ Icc 1 N) :
      actualUpwardRowError φ c N m n = a N n + b N n + d N n := by
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < n)).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt n := by
      apply (eq_div_iff hs).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient hsupp hc hn m
    rw [actualUpwardRowError, hu]
    dsimp only [a, b, d]
    ring
  have hsum : (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) ≤
      ∑ n ∈ Icc 1 N, 3 * (a N n ^ 2 + b N n ^ 2 + d N n ^ 2) := by
    apply sum_le_sum
    intro n hn
    rw [hrow N n hn]
    nlinarith only [sq_nonneg (a N n - b N n), sq_nonneg (a N n - d N n),
      sq_nonneg (b N n - d N n)]
  have hfinal := div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)
  rw [← mul_sum, sum_add_distrib, sum_add_distrib] at hfinal
  have hbound : 3 * ((∑ n ∈ Icc 1 N, a N n ^ 2) + (∑ n ∈ Icc 1 N, b N n ^ 2) +
      ∑ n ∈ Icc 1 N, d N n ^ 2) / Real.log N ≤ ε := by
    rw [mul_div_assoc, add_div, add_div]
    have ha' := ha c hc1 hcK B hBmax
    have hb' := hb c hc1 hcK B hBmax
    have hd' := hd c hc1 hcK B hB
    change (∑ n ∈ Icc 1 N, a N n ^ 2) / Real.log N ≤ ε / 9 at ha'
    change (∑ n ∈ Icc 1 N, b N n ^ 2) / Real.log N ≤ ε / 9 at hb'
    change (∑ n ∈ Icc 1 N, d N n ^ 2) / Real.log N ≤ ε / 9 at hd'
    linarith only [ha', hb', hd']
  exact hfinal.trans hbound

/-- The normalized actual prime-source error has one horizon for all bounded overlaps. -/
theorem eventually_normalizedUpwardPrimeResidual_norm_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ‖normalizedUpwardPrimeResidual φ c N m‖ ≤ ε := by
  filter_upwards [eventually_actualUpwardRowError_sq_uniform_overlap hφ hsupp hM hK hm
    (sq_pos_of_pos hε)] with N hN
  intro c hc1 hcK
  have h := hN c hc1 hcK
  rw [← normalizedUpwardPrimeResidual_norm_sq] at h
  nlinarith only [h, hε, norm_nonneg (normalizedUpwardPrimeResidual φ c N m)]

/-- The explicit tilted spline has a uniform actual upward source law on every bounded overlap interval. -/
theorem eventually_tiltedUnitSpline_normalizedUpwardPrimeResidual_norm_uniform_overlap
    {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ‖normalizedUpwardPrimeResidual tiltedUnitSpline c N m‖ ≤ ε :=
  eventually_normalizedUpwardPrimeResidual_norm_uniform_overlap contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hK hm hε

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_logPrimeKernel_uniform_overlap_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_normalizedUpwardPrimeResidual_norm_uniform_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_normalizedUpwardPrimeResidual_norm_uniform_overlap
