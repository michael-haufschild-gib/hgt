import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPolePairingsHaveTheirLiteralChannels
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPoleGammaAndCenterHaveOneConstant

/-!
# The literal divisor jet in a terminal conductor pairing

The downward divisor convolution separates into the Gamma remainder,
the two near logarithms and the periodic divisor jet. The full center
has the same conductor normalization, so its receiving charge can be
paired with that jet before taking a limit.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The exact divisor identity retains the jet for every conductor. -/
theorem nearGammaDownwardCoefficient_eq_terminal_channels {φ : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c) {N j : ℕ} (hN : 1 ≤ N) (hj : 1 ≤ j) (m n : ℕ) :
    nearGammaDownwardCoefficient φ c N m n j =
      ramanujanLagCoefficient m j *
        (nearArchimedeanRemainder φ (c / N) n j -
          Real.log c * (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) /
            ∫ u, φ u ^ 2) -
          Real.log ((j : ℝ) / N) *
            (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2)) +
      ramanujanLogDivisorJet m j *
        (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  rw [nearGammaDownwardCoefficient,
    sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m (by omega : 0 < j)]
  unfold nearArchimedeanRemainder
  rw [one_div, inv_div, Real.log_div hN0.ne' hc.ne', Real.log_div hj0.ne' hN0.ne']
  ring

private theorem terminal_log_gap_pos_iff {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    0 < |Real.log j - Real.log n| ↔ j ≠ n := by
  constructor
  · intro h hne
    subst j
    simpa only [sub_self, abs_zero, lt_self_iff_false] using h
  · intro hne
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    apply abs_pos.mpr
    apply sub_ne_zero.mpr
    rcases lt_or_gt_of_ne hne with h | h
    · exact (Real.log_lt_log hj0 (by exact_mod_cast h)).ne
    · exact (Real.log_lt_log hn0 (by exact_mod_cast h)).ne'

/-- A terminal receiver reads all four downward channels with their original signs. -/
theorem sum_terminal_nearGammaDownwardRow_eq {φ F : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n * nearGammaDownwardRow φ c N m n) =
      gapMatrixPair (nearArchimedeanRemainder φ (c / N)) 0 2 (c / N) N
        (fun n => F ((n : ℝ) / N)) (ramanujanLagCoefficient m) -
      Real.log c * endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
        F 0 2 (c / N) N (fun _ => 1) (ramanujanLagCoefficient m) -
      endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
        F 0 2 (c / N) N (fun _ => 1)
        (fun j => ramanujanLagCoefficient m j * Real.log ((j : ℝ) / N)) +
      endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
        F 0 2 (c / N) N (fun _ => 1) (ramanujanLogDivisorJet m) := by
  unfold gapMatrixPair endpointNearPairSum nearGammaDownwardRow nearRowIndices
  rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  rw [sum_filter, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  have hgap : (j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * c / N) ↔
      (0 * (c / N) < |Real.log j - Real.log n| ∧
        |Real.log j - Real.log n| ≤ 2 * (c / N)) := by
    rw [zero_mul, terminal_log_gap_pos_iff (mem_Icc.mp hn).1 (mem_Icc.mp hj).1,
      mul_div_assoc]
  simp only [hgap]
  by_cases he : 0 * (c / N) < |Real.log j - Real.log n| ∧
      |Real.log j - Real.log n| ≤ 2 * (c / N)
  · simp only [if_pos he, mul_one]
    rw [nearGammaDownwardCoefficient_eq_terminal_channels hc hN (mem_Icc.mp hj).1]
    ring
  · simp only [if_neg he, mul_zero, sub_zero, add_zero]

/-- The full center and divisor jet use the same square-root totient normalization. -/
theorem sqrt_log_mul_terminal_fullCenter_conductor_pair {N m : ℕ}
    (hm : 0 < m) (hL : 0 < Real.log N) (α : ℝ) (u : ℕ → ℝ) :
    Real.sqrt (Real.log N) *
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N),
        horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ =
      ((α / N) * ∑ n ∈ Icc 1 N, u n / Real.sqrt n *
        ∑ j ∈ Icc 1 N,
          (arithmeticPoleKernel n j - archimedeanCenterKernel n j) *
            (ramanujanLagCoefficient m j / Real.sqrt j)) / Real.sqrt (m.totient : ℝ) := by
  have hp := sqrt_log_mul_terminal_kernel_pair hm hL
    (fun n j => α / N * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) u
  change Real.sqrt (Real.log N) *
    ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N),
      horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ = _ at hp
  rw [hp]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [mul_sum, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- Gamma and near-center channels, with the divisor jet kept separate. -/
def terminalConductorGammaCenterPair (φ h : ℝ → ℝ) (c : ℝ) (N m : ℕ) : ℝ :=
  (gapMatrixPair (nearArchimedeanRemainder φ (c / N)) 0 2 (c / N) N
      (fun n => logProfile h ((n : ℝ) / N)) (ramanujanLagCoefficient m) -
    farCrossPair φ (c / N) N (fun n => logProfile h ((n : ℝ) / N))
      (ramanujanLagCoefficient m)) / c +
  ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
    (nearCenterPair c N (fun n => logProfile h ((n : ℝ) / N))
      (ramanujanLagCoefficient m) / N) -
  Real.log c * (endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
    (logProfile h) 0 2 (c / N) N (fun _ => 1) (ramanujanLagCoefficient m) / c) -
  endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
    (logProfile h) 0 2 (c / N) N (fun _ => 1)
    (fun j => ramanujanLagCoefficient m j * Real.log ((j : ℝ) / N)) / c

/-- For a nonpolar conductor the signed Gamma and near-center remainder has zero terminal mean. -/
theorem tendsto_terminalConductorGammaCenterPair_nonpolar
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m : ℕ} (hm : 2 ≤ m)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0))
    (he : Tendsto (fun N : ℕ => c N * Real.log (c N) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => terminalConductorGammaCenterPair φ h (c N) N m)
      atTop (𝓝 0) := by
  have hm0 : 0 < m := by omega
  have hm1 : m ≠ 1 := by omega
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  obtain ⟨BF, _, hBF, _⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨LF, hLF⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |logProfile h x - logProfile h y| ≤ ((LF : ℝ) * Real.exp (2 * A)) * |x - y| :=
    fun x _ y _ => abs_logProfile_sub_le hh hsupp hA hBF hLF x y
  let B : ℝ := 1 + ∑ d ∈ m.divisors, (d : ℝ)
  have huB : ∀ n : ℕ, |(1 : ℝ)| ≤ B := by
    intro n
    simp only [abs_one]
    exact le_add_of_nonneg_right (by positivity)
  have hvB : ∀ n, |ramanujanLagCoefficient m n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le m n).trans (le_add_of_nonneg_left zero_le_one)
  have hg := tendsto_weighted_nearArchimedean_sub_farCross_pair_div_overlap
    hφ hφsupp hM (fun x => abs_logProfile_le hBF x)
    (by positivity : 0 ≤ (LF : ℝ) * Real.exp (2 * A)) hFL
    (q := m) (u := fun _ => 1) (v := ramanujanLagCoefficient m) hm0
    (by intros; rfl) (by
      intro n
      simpa only [Nat.mul_one] using ramanujanLagCoefficient_add_mul m n 1)
    huB hvB hc0 hcinf hcN
  have hmean : periodicMean (fun _ => (1 : ℝ)) m = 1 := by
    simp only [periodicMean, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast hm0.ne')
  have hnonpolar : periodicMean (ramanujanLagCoefficient m) m = 0 := by
    simp only [periodicMean_ramanujan_of_dvd hm0 hm0 (dvd_refl m), if_neg hm1]
  simp only [hmean, hnonpolar, mul_zero, zero_mul, mul_one] at hg
  have hone : ramanujanLagCoefficient 1 = fun _ => (1 : ℝ) :=
    funext ramanujanLagCoefficient_one
  have hn := tendsto_terminal_joint_nearCenter_finite_part hφ hφsupp hM hh hA hsupp
    (m := m) (l := 1) hm0 one_pos hc hcinf he
  have hl := tendsto_terminal_nearLogRow hφ hφsupp hM hh hA hsupp
    (m := m) (l := 1) hm0 one_pos hc0 hcinf hcN
  simp only [hone, hm1, false_and, if_false, mul_zero, mul_one] at hn hl
  have ht := (hg.add hn).sub hl
  simp only [zero_add, sub_zero] at ht
  exact ht.congr fun N => by unfold terminalConductorGammaCenterPair; ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.sum_terminal_nearGammaDownwardRow_eq
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.sqrt_log_mul_terminal_fullCenter_conductor_pair
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminalConductorGammaCenterPair_nonpolar
