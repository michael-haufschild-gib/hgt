import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsAwayFromTheHorizonHaveNoExteriorPrimes
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowErrorChannelsDisappear

/-!
# Exterior downward sources vanish against bounded terminal receivers

The source is confined to a strip of linear overlap width. Its row
bound, the strip cardinality and the terminal square-root weight give
an error of order `c / sqrt(N)` after overlap normalization. No gap
between the terminal support and the horizon is required.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis

/-- A bounded terminal receiver pays the actual exterior strip with a square-root horizon gain. -/
theorem abs_terminal_exteriorDownward_pairing_div_overlap_le
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B : ℝ} (hF : ∀ x, |F x| ≤ B) {c : ℝ} (hc : 1 ≤ c)
    {N : ℕ} (hN : 1 ≤ N) (hw : c / N ≤ 1)
    (hstrip : 2 * linearPrimeStrip c + 1 ≤ N) (m : ℕ) :
    |(∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n *
      actualExteriorDownwardRow (atomDilate φ (c / N)) N m n) / c| ≤
      (4 * B * m.totient * (Real.exp 1 + 1) * (Real.exp 1 + 2)) * c / Real.sqrt N := by
  let D := linearPrimeStrip c
  let g := atomDilate φ (c / N)
  let S := Icc (N - D) N
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 0 ≤ B := (abs_nonneg (F 0)).trans (hF 0)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  obtain ⟨hg, hgsupp, _⟩ := atomDilate_facts hφ hsupp (div_pos hc0 hN0)
  have hG : 0 < ∫ u, g u ^ 2 := by
    dsimp only [g]
    rw [integral_atomDilate_sq (div_pos hc0 hN0)]
    exact mul_pos (div_pos hc0 hN0) hM
  have hDN : D ≤ N := by dsimp only [D]; omega
  have hsub : S ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by dsimp only [D] at hlo; omega, hhi⟩
  have hcard : S.card = D + 1 := by
    dsimp only [S]
    rw [Nat.card_Icc]
    omega
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) :
      actualExteriorDownwardRow g N m n = regroupedExteriorDownwardPrimeRow g c N m n := by
    rw [actualExteriorDownwardRow]
    exact downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m
  have hsum : (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n *
        actualExteriorDownwardRow g N m n) =
      ∑ n ∈ S, F ((n : ℝ) / N) / Real.sqrt n * actualExteriorDownwardRow g N m n := by
    symm
    apply sum_subset hsub
    intro n hn hnS
    have hfar : n < N - D := by
      have hnhi := (mem_Icc.mp hn).2
      have hnot : ¬ (N - D ≤ n ∧ n ≤ N) := by simpa only [S, mem_Icc] using hnS
      omega
    rw [hrow n hn, regroupedExteriorDownwardPrimeRow_eq_zero_small_width
      hc0 hn hgsupp hw hfar m, mul_zero]
  have hpoint : ∀ n ∈ S,
      |F ((n : ℝ) / N) / Real.sqrt n * actualExteriorDownwardRow g N m n| ≤
        (2 * B / Real.sqrt N) * (2 * m.totient * D) := by
    intro n hn
    have hnN := hsub hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnN).1
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hhalf : N ≤ 2 * n := by have := (mem_Icc.mp hn).1; dsimp only [D] at this; omega
    have hhalfR : (N : ℝ) ≤ 2 * n := by exact_mod_cast hhalf
    have hsqrt : Real.sqrt N ≤ 2 * Real.sqrt n := by
      have hsqN := Real.sq_sqrt hN0.le
      have hsqn := Real.sq_sqrt hn0.le
      nlinarith only [hsqN, hsqn, hhalfR, Real.sqrt_nonneg (N : ℝ), Real.sqrt_nonneg (n : ℝ)]
    have hweight : |F ((n : ℝ) / N) / Real.sqrt n| ≤ 2 * B / Real.sqrt N := by
      rw [abs_div, abs_of_pos hsn]
      apply (div_le_div_of_nonneg_right (hF _) hsn.le).trans
      apply (div_le_div_iff₀ hsn hsN).mpr
      nlinarith only [hsqrt, hB]
    have hr := abs_regroupedExteriorDownwardPrimeRow_le_small_width hg.continuous
      hc0 hN hgsupp hG hw m n
    rw [abs_mul, hrow n hnN]
    exact mul_le_mul hweight hr (abs_nonneg _) (by positivity)
  have hD : (D : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc
  have hD1 : (D : ℝ) + 1 ≤ (Real.exp 1 + 2) * c := by linarith only [hD, hc]
  have hraw : |∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n *
      actualExteriorDownwardRow g N m n| ≤
      (4 * B * m.totient * (Real.exp 1 + 1) * (Real.exp 1 + 2)) * c ^ 2 / Real.sqrt N := by
    rw [hsum]
    calc
      _ ≤ ∑ n ∈ S, |F ((n : ℝ) / N) / Real.sqrt n * actualExteriorDownwardRow g N m n| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ S, (2 * B / Real.sqrt N) * (2 * m.totient * D) := sum_le_sum hpoint
      _ = (4 * B * m.totient / Real.sqrt N) * (((D : ℝ) + 1) * D) := by
        rw [sum_const, hcard, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (4 * B * m.totient / Real.sqrt N) *
          (((Real.exp 1 + 2) * c) * ((Real.exp 1 + 1) * c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hD1 hD (Nat.cast_nonneg D) (by positivity))
          (by positivity)
      _ = _ := by ring
  rw [abs_div, abs_of_pos hc0]
  exact (div_le_div_of_nonneg_right hraw hc0.le).trans_eq (by field_simp [hc0.ne']; ring)

/-- Every bounded terminal receiver has zero exterior downward limit at critical scale. -/
theorem tendsto_terminal_exteriorDownward_pairing
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B : ℝ} (hF : ∀ x, |F x| ≤ B) (m : ℕ)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n *
        actualExteriorDownwardRow (atomDilate φ (c N / N)) N m n) / c N)
      atTop (𝓝 0) := by
  have hcN := criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hc2N := criticalCurve_pow_log_div_natCast hc hR hcrit 2 0
  simp only [pow_one, pow_zero, mul_one] at hcN
  simp only [pow_zero, mul_one] at hc2N
  have ht : Tendsto (fun N : ℕ => c N / Real.sqrt N) atTop (𝓝 0) := by
    have hh := hc2N.sqrt
    simp only [Real.sqrt_zero] at hh
    apply hh.congr
    intro N
    rw [Real.sqrt_div (sq_nonneg (c N)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (zero_le_one.trans (hc N))]
  have hstrip := hcN.const_mul (4 * (Real.exp 1 + 1))
  simp only [mul_zero] at hstrip
  have hlim := ht.const_mul (4 * B * m.totient * (Real.exp 1 + 1) * (Real.exp 1 + 2))
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 2,
    hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hstrip.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with N hN hw hstripN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsmall : 4 * (Real.exp 1 + 1) * c N ≤ N := by
    apply (div_le_one hN0).mp
    simpa only [mul_div_assoc] using hstripN.le
  have hD := linearPrimeStrip_le (hc N)
  have h4D : 4 * linearPrimeStrip (c N) ≤ N := by
    have hh : (4 : ℝ) * linearPrimeStrip (c N) ≤ N := by linarith only [hD, hsmall]
    exact_mod_cast hh
  rw [Real.norm_eq_abs]
  exact (abs_terminal_exteriorDownward_pairing_div_overlap_le hφ hsupp hM hF
    (hc N) hN1 hw.le (by omega) m).trans_eq (by ring)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_exteriorDownward_pairing
