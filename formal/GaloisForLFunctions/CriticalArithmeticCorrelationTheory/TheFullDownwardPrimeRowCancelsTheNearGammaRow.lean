import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGammaAndDownwardPrimeRowsCancel
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNonRatioPrimeRowsSplitIntoDownwardAndUpward
import GaloisForLFunctions.RHTower.ZetaNotchRampMainTerm

/-!
# The full downward prime row cancels the near Gamma row

Exterior products `ℓ=kj>N` contributing at width `c/N` lie in a fixed
integer strip around the horizon. Only a bounded number of rows and
products survive. Their truncated Mangoldt divisor mass is at most
`log ℓ`, while the square-root profile makes each product uniformly bounded.

Exact regrouping identifies this finite boundary sum with the infinite
downward prime action minus its interior part. Its squared row norm is
bounded independently of the horizon. After logarithmic normalization,
near Gamma therefore cancels the full downward action, including every
exterior product and prime power.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The largest possible product at horizon `N` and width `c/N`. -/
def exteriorPrimeCutoff (c : ℝ) (N : ℕ) : ℕ := ⌈(N : ℝ) * Real.exp (c / N)⌉₊
/-- A fixed integer width containing every exterior product and its receiving row. -/
def exteriorPrimeStrip (c : ℝ) : ℕ := ⌈c * Real.exp c⌉₊

/-- The product cutoff exceeds the horizon by at most a fixed number of integers. -/
theorem exteriorPrimeCutoff_bounds {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    N ≤ exteriorPrimeCutoff c N ∧ exteriorPrimeCutoff c N ≤ N + exteriorPrimeStrip c := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : 0 ≤ c / N := (div_pos hc hN0).le
  have hNc : (N : ℝ) * Real.exp (c / N) ≤ N + c * Real.exp c := by
    calc
      _ = N + N * (Real.exp (c / N) - 1) := by ring
      _ ≤ N + N * (c / N * Real.exp (c / N)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (show Real.exp (c / N) - 1 ≤ c / N * Real.exp (c / N) from exp_sub_one_le_mul_exp) hN0.le)
      _ = N + c * Real.exp (c / N) := by field_simp
      _ ≤ N + c * Real.exp c := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (div_le_self hc.le hN1)) hc.le)
  constructor
  · have h : (N : ℝ) ≤ (exteriorPrimeCutoff c N : ℝ) :=
      (le_mul_of_one_le_right hN0.le (Real.one_le_exp_iff.mpr hw)).trans (Nat.le_ceil _)
    exact_mod_cast h
  · apply Nat.ceil_le.mpr
    have hB : c * Real.exp c ≤ (exteriorPrimeStrip c : ℝ) := Nat.le_ceil _
    refine hNc.trans ?_
    rw [Nat.cast_add]
    exact add_le_add le_rfl hB

/-- A near product beyond the horizon can reach only the fixed boundary strip. -/
theorem exterior_prime_near_boundary {c : ℝ} (hc : 0 < c) {N n ℓ : ℕ}
    (hn : n ∈ Icc 1 N) (hℓ : N < ℓ)
    (hlog : |Real.log ℓ - Real.log n| ≤ c / N) :
    N - exteriorPrimeStrip c ≤ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le N) hℓ
  have hN0 : (0 : ℝ) < N := hn0.trans_le hnN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hgap := abs_sub_le_of_abs_log_le hℓ0 hn0 hlog
  have hB : |(ℓ : ℝ) - n| ≤ c * Real.exp c := by
    calc
      _ ≤ n * (Real.exp (c / N) - 1) := hgap
      _ ≤ n * (c / N * Real.exp (c / N)) :=
        mul_le_mul_of_nonneg_left exp_sub_one_le_mul_exp hn0.le
      _ ≤ N * (c / N * Real.exp (c / N)) :=
        mul_le_mul_of_nonneg_right hnN (by positivity)
      _ = c * Real.exp (c / N) := by field_simp
      _ ≤ c * Real.exp c := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (div_le_self hc.le hN1)) hc.le
  have hB' := (le_abs_self ((ℓ : ℝ) - n)).trans (hB.trans (Nat.le_ceil _))
  change (ℓ : ℝ) - n ≤ (exteriorPrimeStrip c : ℝ) at hB'
  have hnat : ℓ ≤ n + exteriorPrimeStrip c := by
    have h : (ℓ : ℝ) ≤ n + (exteriorPrimeStrip c : ℝ) := by linarith only [hB']
    exact_mod_cast h
  omega

/-- The exact Mangoldt divisor convolution, retaining only quotients inside the horizon. -/
def horizonRamanujanMangoldt (m N ℓ : ℕ) : ℝ :=
  ∑ d ∈ ℓ.divisors.filter (fun d => ℓ / d ≤ N),
    (ArithmeticFunction.vonMangoldt d : ℝ) * ramanujanLagCoefficient m (ℓ / d)

/-- The full Mangoldt divisor identity controls every signed truncated conductor reading. -/
theorem abs_horizonRamanujanMangoldt_le (m N ℓ : ℕ) :
    |horizonRamanujanMangoldt m N ℓ| ≤ (m.totient : ℝ) * Real.log ℓ := by
  unfold horizonRamanujanMangoldt
  calc
    _ ≤ ∑ d ∈ ℓ.divisors.filter (fun d => ℓ / d ≤ N),
        |(ArithmeticFunction.vonMangoldt d : ℝ) * ramanujanLagCoefficient m (ℓ / d)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ ℓ.divisors.filter (fun d => ℓ / d ≤ N),
        (m.totient : ℝ) * (ArithmeticFunction.vonMangoldt d : ℝ) := by
      apply sum_le_sum
      intro d _
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, mul_comm (m.totient : ℝ)]
      exact mul_le_mul_of_nonneg_left
        (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m (ℓ / d))
        ArithmeticFunction.vonMangoldt_nonneg
    _ = (m.totient : ℝ) * horizonDivisorMangoldt N ℓ := by rw [horizonDivisorMangoldt, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (horizonDivisorMangoldt_le_log N ℓ) (Nat.cast_nonneg _)

/-- The normalized exterior row grouped by the product of prime power and input index. -/
def regroupedExteriorDownwardPrimeRow (g : ℝ → ℝ) (c : ℝ) (N m n : ℕ) : ℝ :=
  ∑ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
    horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
      (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))

/-- Bounded product count and `log ℓ/√ℓ≤2` give a uniform row bound. -/
theorem abs_regroupedExteriorDownwardPrimeRow_le {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hG : 0 < ∫ u, g u ^ 2) (m n : ℕ) :
    |regroupedExteriorDownwardPrimeRow g c N m n| ≤
      2 * m.totient * exteriorPrimeStrip c := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  have hterm : ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
      |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
        (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| ≤ 2 * m.totient := by
    intro ℓ hℓ
    have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hN.trans (mem_Ioc.mp hℓ).1.le
    have hℓ0 : (0 : ℝ) < ℓ := zero_lt_one.trans_le hℓ1
    have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
    have hcorr : |bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)| ≤ 1 := by
      rw [abs_div, abs_of_pos hG, div_le_one hG]
      exact abs_bumpCorr_le hg hgc _
    have hjet : |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ| ≤ 2 * m.totient := by
      rw [abs_div, abs_of_pos hs]
      calc
        _ ≤ (m.totient : ℝ) * Real.log ℓ / Real.sqrt ℓ :=
          div_le_div_of_nonneg_right (abs_horizonRamanujanMangoldt_le m N ℓ) hs.le
        _ = (m.totient : ℝ) * (Real.log ℓ * (Real.sqrt ℓ)⁻¹) := by ring
        _ ≤ (m.totient : ℝ) * 2 := mul_le_mul_of_nonneg_left
          (_root_.RHTower.WeilAbscissa.log_div_sqrt_le hℓ1) (Nat.cast_nonneg _)
        _ = _ := by ring
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hjet hcorr (abs_nonneg _) (by positivity)
  have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ exteriorPrimeStrip c := by
    have hbound := (exteriorPrimeCutoff_bounds hc hN).2
    rw [Nat.card_Ioc]
    exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ exteriorPrimeStrip c by omega)
  unfold regroupedExteriorDownwardPrimeRow
  calc
    _ ≤ ∑ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
        |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
          (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ℓ ∈ Ioc N (exteriorPrimeCutoff c N), 2 * (m.totient : ℝ) := sum_le_sum hterm
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 2 * (m.totient : ℝ))

/-- Rows outside the fixed boundary strip receive no exterior prime product. -/
theorem regroupedExteriorDownwardPrimeRow_eq_zero {g : ℝ → ℝ}
    {c : ℝ} (hc : 0 < c) {N n : ℕ} (hn : n ∈ Icc 1 N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hout : n < N - exteriorPrimeStrip c) (m : ℕ) :
    regroupedExteriorDownwardPrimeRow g c N m n = 0 := by
  unfold regroupedExteriorDownwardPrimeRow
  apply sum_eq_zero
  intro ℓ hℓ
  have hgap : c / N < |Real.log ℓ - Real.log n| := by
    by_contra h
    exact (not_lt_of_ge (exterior_prime_near_boundary hc hn (mem_Ioc.mp hℓ).1
      (le_of_not_gt h))) hout
  rw [bumpCorr_eq_zero hgsupp hgap, zero_div, mul_zero]

/-- The exterior action has uniformly bounded squared row mass. -/
theorem sum_regroupedExteriorDownwardPrimeRow_sq_le {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hG : 0 < ∫ u, g u ^ 2) (m : ℕ) :
    (∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow g c N m n ^ 2) ≤
      ((exteriorPrimeStrip c : ℝ) + 1) * (2 * m.totient * exteriorPrimeStrip c) ^ 2 := by
  let S := (Icc 1 N).filter (fun n => N - exteriorPrimeStrip c ≤ n)
  have hsub : S ⊆ Icc 1 N := filter_subset _ _
  have hrestrict : (∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow g c N m n ^ 2) =
      ∑ n ∈ S, regroupedExteriorDownwardPrimeRow g c N m n ^ 2 := by
    symm
    apply sum_subset hsub
    intro n hn hnS
    have hout : n < N - exteriorPrimeStrip c := by
      exact lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
    rw [regroupedExteriorDownwardPrimeRow_eq_zero hc hn hgsupp hout m, zero_pow (by decide)]
  have hcard : (S.card : ℝ) ≤ (exteriorPrimeStrip c : ℝ) + 1 := by
    have hcontain : S ⊆ Icc (N - exteriorPrimeStrip c) N := fun n hn =>
      mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
    have hnat : S.card ≤ exteriorPrimeStrip c + 1 := by
      have h := card_le_card hcontain
      rw [Nat.card_Icc] at h
      omega
    exact_mod_cast hnat
  rw [hrestrict]
  calc
    _ ≤ ∑ _n ∈ S, (2 * (m.totient : ℝ) * exteriorPrimeStrip c) ^ 2 := by
      apply sum_le_sum
      intro n _
      have hb := abs_regroupedExteriorDownwardPrimeRow_le hg hc hN hgsupp hG m n
      have h := mul_self_le_mul_self (abs_nonneg _) hb
      simpa only [← sq, sq_abs] using h
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

/-- Product regrouping preserves an arbitrary signed quotient weight and its horizon cutoff. -/
private theorem sum_weighted_prime_products {N L : ℕ} (hNL : N ≤ L) (u F : ℕ → ℝ)
    (hF : ∀ ℓ, L < ℓ → F ℓ = 0) :
    (∑ k ∈ range (L + 1), ∑ j ∈ Icc 1 N,
      (ArithmeticFunction.vonMangoldt k : ℝ) * u j * F (k * j)) =
      ∑ ℓ ∈ Icc 1 L, (∑ d ∈ ℓ.divisors.filter (fun d => ℓ / d ≤ N),
        (ArithmeticFunction.vonMangoldt d : ℝ) * u (ℓ / d)) * F ℓ := by
  let f : ℕ → ℕ → ℝ := fun k ℓ =>
    if ℓ / k ≤ N then (ArithmeticFunction.vonMangoldt k : ℝ) * u (ℓ / k) * F ℓ else 0
  have hsub : Icc 1 N ⊆ Icc 1 L := Icc_subset_Icc le_rfl hNL
  have hinner (k : ℕ) (hk : k ∈ Icc 1 L) :
      (∑ j ∈ Icc 1 L, if k * j ≤ L then f k (k * j) else 0) =
        ∑ j ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt k : ℝ) * u j * F (k * j) := by
    have hk0 : 0 < k := (mem_Icc.mp hk).1
    calc
      _ = ∑ j ∈ Icc 1 N, if k * j ≤ L then f k (k * j) else 0 := by
        symm
        apply sum_subset hsub
        intro j hj hjN
        have hnot : ¬ j ≤ N := fun hjn => hjN (mem_Icc.mpr ⟨(mem_Icc.mp hj).1, hjn⟩)
        by_cases hprod : k * j ≤ L
        · simp only [if_pos hprod, f, Nat.mul_div_cancel_left j hk0, if_neg hnot]
        · exact if_neg hprod
      _ = _ := by
        apply sum_congr rfl
        intro j hj
        by_cases hprod : k * j ≤ L
        · simp only [if_pos hprod, f, Nat.mul_div_cancel_left j hk0, if_pos (mem_Icc.mp hj).2]
        · simp only [if_neg hprod, hF (k * j) (lt_of_not_ge hprod), mul_zero]
  have hzero : (∑ k ∈ range (L + 1), ∑ j ∈ Icc 1 N,
      (ArithmeticFunction.vonMangoldt k : ℝ) * u j * F (k * j)) =
      ∑ k ∈ Icc 1 L, ∑ j ∈ Icc 1 N,
        (ArithmeticFunction.vonMangoldt k : ℝ) * u j * F (k * j) := by
    symm
    apply sum_subset (fun k hk => mem_range.mpr (by have := (mem_Icc.mp hk).2; omega))
    intro k hk hk'
    have hk0 : k = 0 := by
      have hkL := mem_range.mp hk
      by_contra h
      exact hk' (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h, by omega⟩)
    simp [hk0]
  rw [hzero]
  calc
    _ = ∑ k ∈ Icc 1 L, ∑ j ∈ Icc 1 L, if k * j ≤ L then f k (k * j) else 0 :=
      sum_congr rfl fun k hk => (hinner k hk).symm
    _ = ∑ ℓ ∈ Icc 1 L, ∑ d ∈ ℓ.divisors, f d ℓ :=
      _root_.RHTower.CriticalGibbs.sum_mulPairs_eq_sum_divisors L f
    _ = _ := by
      apply sum_congr rfl
      intro ℓ _
      rw [sum_mul, sum_filter]

/-- Autocorrelation support removes every product above the exact exponential cutoff. -/
private theorem normalized_downward_kernel_vanishes {g : ℝ → ℝ} {c : ℝ}
    {N n : ℕ} (hn : n ∈ Icc 1 N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0) {ℓ : ℕ}
    (hℓ : exteriorPrimeCutoff c N < ℓ) :
    (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) /
      Real.sqrt ℓ / (∫ u, g u ^ 2) = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := hn0.trans_le hnN
  have hℓR : (exteriorPrimeCutoff c N : ℝ) < ℓ := by exact_mod_cast hℓ
  have hlt : (n : ℝ) * Real.exp (c / N) < ℓ :=
    ((mul_le_mul_of_nonneg_right hnN (Real.exp_pos _).le).trans (Nat.le_ceil _)).trans_lt hℓR
  have hlog := Real.log_lt_log (mul_pos hn0 (Real.exp_pos _)) hlt
  rw [Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hgap : c / N < |Real.log ℓ - Real.log n| :=
    (by linarith only [hlog] : c / N < Real.log ℓ - Real.log n).trans_le (le_abs_self _)
  rw [bumpCorr_eq_zero hgsupp hgap]
  simp only [ite_self, zero_div]

/-- The literal infinite downward row is the finite horizon-restricted divisor convolution. -/
theorem downwardRamanujanRow_eq_divisors {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0) (m : ℕ) :
    downwardPrimeRow g N (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
        (∫ u, g u ^ 2) =
      ∑ ℓ ∈ Icc 1 (exteriorPrimeCutoff c N),
        (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) / (∫ u, g u ^ 2) *
          horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ := by
  let H : ℕ → ℝ := fun ℓ =>
    (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) /
      Real.sqrt ℓ / (∫ u, g u ^ 2)
  have hH : ∀ ℓ, exteriorPrimeCutoff c N < ℓ → H ℓ = 0 := fun ℓ hℓ =>
    normalized_downward_kernel_vanishes hn hgsupp hℓ
  have hterm (k j : ℕ) (hj : 1 ≤ j) :
      _root_.RHTower.vonMangoldtAtom k * (ramanujanLagCoefficient m j / Real.sqrt j) *
        (if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) /
          (∫ u, g u ^ 2) =
        (ArithmeticFunction.vonMangoldt k : ℝ) * ramanujanLagCoefficient m j * H (k * j) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst k
      simp [_root_.RHTower.vonMangoldtAtom]
    · have hkernel : (if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) =
          if k * j = n then 0 else bumpCorr g (Real.log (k * j : ℕ) - Real.log n) := by
        simp only [eq_comm (a := n)]
        split_ifs
        · rfl
        · congr 1
          rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hk.ne') (by exact_mod_cast (by omega : j ≠ 0))]
          ring
      have hp := vonMangoldtAtom_mul_poleVector k j hj
      change _root_.RHTower.vonMangoldtAtom k * (1 / Real.sqrt j) =
        (ArithmeticFunction.vonMangoldt k : ℝ) * (1 / Real.sqrt (k * j : ℕ)) at hp
      have hfactor : _root_.RHTower.vonMangoldtAtom k * (ramanujanLagCoefficient m j / Real.sqrt j) =
          (ArithmeticFunction.vonMangoldt k : ℝ) * ramanujanLagCoefficient m j / Real.sqrt (k * j : ℕ) := by
        calc
          _ = ramanujanLagCoefficient m j * (_root_.RHTower.vonMangoldtAtom k * (1 / Real.sqrt j)) := by ring
          _ = _ := by rw [hp]; ring
      rw [hkernel, hfactor]
      dsimp only [H]
      ring
  -- The prime-power square-root weight becomes the square-root weight of its product.
  have hsource : downwardPrimeRow g N (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
        (∫ u, g u ^ 2) =
      ∑' k : ℕ, ∑ j ∈ Icc 1 N,
        (ArithmeticFunction.vonMangoldt k : ℝ) * ramanujanLagCoefficient m j * H (k * j) := by
    rw [downwardPrimeRow, ← tsum_div_const]
    apply tsum_congr
    intro k
    rw [mul_sum, sum_div]
    exact sum_congr rfl fun j hj => by
      simpa only [mul_assoc] using hterm k j (mem_Icc.mp hj).1
  have hfinite : (∑' k : ℕ, ∑ j ∈ Icc 1 N,
        (ArithmeticFunction.vonMangoldt k : ℝ) * ramanujanLagCoefficient m j * H (k * j)) =
      ∑ k ∈ range (exteriorPrimeCutoff c N + 1), ∑ j ∈ Icc 1 N,
        (ArithmeticFunction.vonMangoldt k : ℝ) * ramanujanLagCoefficient m j * H (k * j) := by
    apply tsum_eq_sum
    intro k hk
    apply sum_eq_zero
    intro j hj
    have hkL : exteriorPrimeCutoff c N < k := by simpa only [mem_range, not_lt, Nat.succ_le_iff] using hk
    have hprod : exteriorPrimeCutoff c N < k * j :=
      hkL.trans_le (Nat.le_mul_of_pos_right k (mem_Icc.mp hj).1)
    rw [hH (k * j) hprod, mul_zero]
  rw [hsource, hfinite, sum_weighted_prime_products
    (exteriorPrimeCutoff_bounds hc ((mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2)).1
    (ramanujanLagCoefficient m) H hH]
  apply sum_congr rfl
  intro ℓ _
  dsimp only [H, horizonRamanujanMangoldt]
  ring

/-- Interior products retain every divisor in their Mangoldt convolution. -/
theorem horizonRamanujanMangoldt_of_le {N ℓ : ℕ} (hℓ : ℓ ≤ N) (m : ℕ) :
    horizonRamanujanMangoldt m N ℓ = ∑ d ∈ ℓ.divisors,
      (ArithmeticFunction.vonMangoldt d : ℝ) * ramanujanLagCoefficient m (ℓ / d) := by
  rw [horizonRamanujanMangoldt,
    filter_true_of_mem (fun d _ => (Nat.div_le_self ℓ d).trans hℓ)]

/-- The full downward source minus its interior part is exactly the exterior product row. -/
theorem downwardRamanujanRow_sub_interior_eq {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0) (m : ℕ) :
    downwardPrimeRow g N (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
        (∫ u, g u ^ 2) - interiorDownwardPrimeRow g N m n =
      regroupedExteriorDownwardPrimeRow g c N m n := by
  let F : ℕ → ℝ := fun ℓ =>
    (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) / (∫ u, g u ^ 2) *
      horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ
  have hNL := (exteriorPrimeCutoff_bounds hc ((mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2)).1
  have hsub : Icc 1 N ⊆ Icc 1 (exteriorPrimeCutoff c N) := Icc_subset_Icc le_rfl hNL
  have hdiff : Icc 1 (exteriorPrimeCutoff c N) \ Icc 1 N = Ioc N (exteriorPrimeCutoff c N) := by
    apply Finset.ext
    intro ℓ
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  -- Interior products have the full divisor convolution; the remaining products are exterior.
  have hsplit := sum_sdiff (f := F) hsub
  rw [hdiff] at hsplit
  have hinside : (∑ ℓ ∈ Icc 1 N, F ℓ) = interiorDownwardPrimeRow g N m n := by
    rw [interiorDownwardPrimeRow_eq_divisors]
    exact sum_congr rfl fun ℓ hℓ => by
      dsimp only [F]
      rw [horizonRamanujanMangoldt_of_le (mem_Icc.mp hℓ).2]
  have houtside : (∑ ℓ ∈ Ioc N (exteriorPrimeCutoff c N), F ℓ) =
      regroupedExteriorDownwardPrimeRow g c N m n := by
    unfold regroupedExteriorDownwardPrimeRow
    apply sum_congr rfl
    intro ℓ hℓ
    have hne : ℓ ≠ n := by have := (mem_Ioc.mp hℓ).1; have := (mem_Icc.mp hn).2; omega
    dsimp only [F]
    rw [if_neg hne]
    ring
  rw [downwardRamanujanRow_eq_divisors hc hn hgsupp m]
  change (∑ ℓ ∈ Icc 1 (exteriorPrimeCutoff c N), F ℓ) - interiorDownwardPrimeRow g N m n = _
  rw [← hsplit, hinside, houtside]
  ring

/-- The actual normalized downward action with its interior products removed. -/
def actualExteriorDownwardRow (g : ℝ → ℝ) (N m n : ℕ) : ℝ :=
  downwardPrimeRow g N (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
    (∫ u, g u ^ 2) - interiorDownwardPrimeRow g N m n

/-- The boundary estimate holds for the literal infinite prime-power source. -/
theorem sum_actualExteriorDownwardRow_sq_le {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hG : 0 < ∫ u, g u ^ 2) (m : ℕ) :
    (∑ n ∈ Icc 1 N, actualExteriorDownwardRow g N m n ^ 2) ≤
      ((exteriorPrimeStrip c : ℝ) + 1) * (2 * m.totient * exteriorPrimeStrip c) ^ 2 := by
  have heq : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow g N m n ^ 2) =
      ∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow g c N m n ^ 2 := by
    exact sum_congr rfl fun n hn => congrArg (fun t : ℝ => t ^ 2)
      (downwardRamanujanRow_sub_interior_eq hc hn hgsupp m)
  rw [heq]
  exact sum_regroupedExteriorDownwardPrimeRow_sq_le hg hc hN hgsupp hG m

/-- Exterior downward products have negligible squared mass at logarithmic scale. -/
theorem tendsto_actualExteriorDownwardRow_sq_div_log {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) /
        Real.log N) atTop (𝓝 0) := by
  let C := ((exteriorPrimeStrip c : ℝ) + 1) * (2 * m.totient * exteriorPrimeStrip c) ^ 2
  have hlim : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Real.log_natCast_nonneg N)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  exact div_le_div_of_nonneg_right
    (sum_actualExteriorDownwardRow_sq_le hg.continuous hc hN hgsupp hG m)
    (Real.log_natCast_nonneg N)

/-- Exterior source rows acting on the logarithmically normalized conductor profile. -/
def normalizedExteriorDownwardVector (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => actualExteriorDownwardRow (atomDilate φ (c / N)) N m n /
    Real.sqrt (Real.log N))

/-- Euclidean squared norm is the actual row mass divided by `log N`. -/
theorem normalizedExteriorDownwardVector_norm_sq (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2 =
      (∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) /
        Real.log N := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ n : PrimeHorizonIndex N,
    (actualExteriorDownwardRow (atomDilate φ (c / N)) N m n / Real.sqrt (Real.log N)) ^ 2) = _
  simp only [div_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← sum_div]
  congr 1
  exact sum_coe_sort (Icc 1 N)
    (fun n => actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2)

/-- The actual exterior downward action vanishes in normalized coefficient norm. -/
theorem tendsto_normalizedExteriorDownwardVector_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Tendsto (fun N : ℕ => ‖normalizedExteriorDownwardVector φ c N m‖) atTop (𝓝 0) := by
  have h := (tendsto_actualExteriorDownwardRow_sq_div_log hφ hsupp hM hc m).sqrt
  simpa only [← normalizedExteriorDownwardVector_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using h

/-- Near Gamma minus the full infinite downward action on the conductor profile. -/
def normalizedFullNearGammaDownwardVector (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n =>
    ((∑ j ∈ nearRowIndices c N n,
      atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) *
        ramanujanLagCoefficient m j / Real.sqrt j) -
      downwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2)) / Real.sqrt (Real.log N))

/-- Interior cancellation and the exterior boundary remainder give the exact full source difference. -/
theorem normalizedFullNearGammaDownwardVector_eq_sub {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) (N m : ℕ) :
    normalizedFullNearGammaDownwardVector φ c N m =
      normalizedNearGammaDownwardVector φ c N m - normalizedExteriorDownwardVector φ c N m := by
  ext n
  have hN : 1 ≤ N := (mem_Icc.mp n.property).1.trans (mem_Icc.mp n.property).2
  change ((∑ j ∈ nearRowIndices c N n,
      atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) *
        ramanujanLagCoefficient m j / Real.sqrt j) -
      downwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2)) / Real.sqrt (Real.log N) =
    nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N) -
      actualExteriorDownwardRow (atomDilate φ (c / N)) N m n / Real.sqrt (Real.log N)
  rw [nearGammaDownwardRow_eq_actual_difference hφ hsupp hc hN m n]
  dsimp only [actualExteriorDownwardRow]
  ring

/-- Near Gamma cancels the entire downward prime action at every fixed overlap. -/
theorem tendsto_normalizedFullNearGammaDownwardVector_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Tendsto (fun N : ℕ => ‖normalizedFullNearGammaDownwardVector φ c N m‖) atTop (𝓝 0) := by
  have hlim := (tendsto_normalizedNearGammaDownwardVector_norm hφ hsupp hM hc m).add
    (tendsto_normalizedExteriorDownwardVector_norm hφ hsupp hM hc m)
  simp only [zero_add] at hlim
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim
  rw [normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc]
  exact norm_sub_le _ _

/-- The explicit boosted spline satisfies full signed downward cancellation. -/
theorem tendsto_tiltedUnitSpline_fullNearGammaDownward_norm {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Tendsto (fun N : ℕ => ‖normalizedFullNearGammaDownwardVector tiltedUnitSpline c N m‖)
      atTop (𝓝 0) :=
  tendsto_normalizedFullNearGammaDownwardVector_norm contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc m

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory


#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_tiltedUnitSpline_fullNearGammaDownward_norm

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.downwardRamanujanRow_eq_divisors
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_actualExteriorDownwardRow_sq_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_normalizedExteriorDownwardVector_norm
