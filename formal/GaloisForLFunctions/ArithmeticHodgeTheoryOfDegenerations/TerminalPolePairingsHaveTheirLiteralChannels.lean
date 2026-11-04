import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheGrowingGammaCenterResidueIsSupportedAtThePole
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWeightsReadEitherEndOfANearPair
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.WindowConductorCoordinatesVanishUniformly

/-!
# Literal channels in a conductor–terminal pairing

One normalized conductor contributes one factor `sqrt(log N)`.
Removing it gives exact finite sums. At conductor one, the full
Mangoldt divisor convolution separates the Gamma remainder and both
near logarithms before any limiting argument.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A terminal pairing with one normalized conductor has its exact square-root logarithmic
normalization. -/
theorem sqrt_log_mul_terminal_kernel_pair {N m : ℕ} (hm : 0 < m)
    (hL : 0 < Real.log N) (A : ℕ → ℕ → ℝ) (u : ℕ → ℝ) :
    Real.sqrt (Real.log N) *
      ⟪Matrix.toEuclideanLin (fun n j : PrimeHorizonIndex N => A n j)
        (normalizedRamanujanHorizonVector m N),
        horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ =
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        u n * ramanujanLagCoefficient m j * A n j / (Real.sqrt n * Real.sqrt j)) /
          Real.sqrt (m.totient : ℝ) := by
  have hs : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  rw [normalizedRamanujanHorizonVector, map_smul, real_inner_smul_left,
    ← mul_assoc, mul_inv_cancel₀ hs, one_mul, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, u n / Real.sqrt n *
    ∑ j : PrimeHorizonIndex N, A n j * ramanujanPoleProfile m j) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => u n / Real.sqrt n *
    ∑ j : PrimeHorizonIndex N, A n j * ramanujanPoleProfile m j), sum_div]
  apply sum_congr rfl
  intro n hn
  rw [sum_coe_sort (Icc 1 N) (fun j => A n j * ramanujanPoleProfile m j), mul_sum, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [ramanujanPoleProfile_eq hm]
  ring

/-- A row divided by `sqrt(log N)` pairs with a terminal profile as its literal single sum. -/
theorem sqrt_log_mul_terminal_row_pair {N : ℕ} (hL : 0 < Real.log N)
    (u r : ℕ → ℝ) :
    Real.sqrt (Real.log N) *
      ⟪WithLp.toLp 2 (fun n : PrimeHorizonIndex N => r n / Real.sqrt (Real.log N)),
        horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ =
      ∑ n ∈ Icc 1 N, u n / Real.sqrt n * r n := by
  have hs : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change Real.sqrt (Real.log N) *
    (∑ n : PrimeHorizonIndex N, u n / Real.sqrt n * (r n / Real.sqrt (Real.log N))) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => u n / Real.sqrt n *
    (r n / Real.sqrt (Real.log N))), mul_sum]
  exact sum_congr rfl fun n _ => by field_simp [hs] <;> ring

/-- The complete separated cross channel is its literal terminal far-pair sum. -/
theorem sqrt_log_mul_terminal_separatedCross_pair {φ : ℝ → ℝ} {c : ℝ} {N m : ℕ}
    (hm : 0 < m) (hL : 0 < Real.log N) (u : ℕ → ℝ) :
    Real.sqrt (Real.log N) *
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N),
        horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ =
      farCrossPair φ (c / N) N u (ramanujanLagCoefficient m) /
        Real.sqrt (m.totient : ℝ) := by
  let A : ℕ → ℕ → ℝ := fun n j =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0
  have hp := sqrt_log_mul_terminal_kernel_pair hm hL A u
  change Real.sqrt (Real.log N) *
    ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N),
      horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ = _ at hp
  rw [hp]
  dsimp only [A]
  unfold farCrossPair
  congr 1
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro j hj
  split_ifs <;> ring

/-- The near-center vector retains exactly its terminal pole-gauged pair sum. -/
theorem sqrt_log_mul_terminal_nearCenter_pair {φ : ℝ → ℝ} {c : ℝ} {N m : ℕ}
    (hm : 0 < m) (hL : 0 < Real.log N) (u : ℕ → ℝ) :
    Real.sqrt (Real.log N) * ⟪nearCenterVector φ c N m,
      horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ =
      completeWeilPoleShift φ c / N *
        nearCenterPair c N u (ramanujanLagCoefficient m) / Real.sqrt (m.totient : ℝ) := by
  rw [nearCenterVector, sqrt_log_mul_terminal_row_pair hL u
    (fun n => ∑ j ∈ nearRowIndices c N n,
      completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
        normalizedRamanujanMode m j / Real.sqrt j)]
  unfold nearCenterPair
  rw [mul_sum, sum_div]
  apply sum_congr rfl
  intro n hn
  rw [mul_sum, mul_sum, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [normalizedRamanujanMode_eq_coefficient hm]
  ring

private theorem terminal_abs_log_gap_pos_iff {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
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

/-- At conductor one, the exact downward divisor convolution separates the two near logarithms. -/
theorem nearGammaDownwardCoefficient_one_eq {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N j : ℕ} (hN : 1 ≤ N) (hj : 1 ≤ j) (n : ℕ) :
    nearGammaDownwardCoefficient φ c N 1 n j =
      nearArchimedeanRemainder φ (c / N) n j -
        Real.log c * (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) /
          ∫ u, φ u ^ 2) -
        Real.log ((j : ℝ) / N) *
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hd := sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet 1 (by omega : 0 < j)
  have hz : ramanujanLogDivisorJet 1 j = 0 := by simp [ramanujanLogDivisorJet]
  rw [ramanujanLagCoefficient_one, hz, mul_one, sub_zero] at hd
  rw [nearGammaDownwardCoefficient, ramanujanLagCoefficient_one, hd, mul_one]
  unfold nearArchimedeanRemainder
  rw [one_div, inv_div, Real.log_div hN0.ne' hc.ne', Real.log_div hj0.ne' hN0.ne']
  ring

/-- The actual polar near row is the Gamma remainder minus the logarithmic Gram and terminal-log
row, with no asymptotic replacement. -/
theorem sum_terminal_nearGammaDownwardRow_one_eq {φ F : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n * nearGammaDownwardRow φ c N 1 n) =
      gapMatrixPair (nearArchimedeanRemainder φ (c / N)) 0 2 (c / N) N
        (fun n => F ((n : ℝ) / N)) (fun _ => 1) -
      Real.log c * endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
        F 0 2 (c / N) N (fun _ => 1) (fun _ => 1) -
      endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
        F 0 2 (c / N) N (fun _ => 1) (fun j => Real.log ((j : ℝ) / N)) := by
  unfold gapMatrixPair endpointNearPairSum nearGammaDownwardRow nearRowIndices
  rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  rw [sum_filter, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  have hgap : (j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * c / N) ↔
      (0 * (c / N) < |Real.log j - Real.log n| ∧
        |Real.log j - Real.log n| ≤ 2 * (c / N)) := by
    rw [zero_mul, terminal_abs_log_gap_pos_iff (mem_Icc.mp hn).1 (mem_Icc.mp hj).1,
      mul_div_assoc]
  simp only [hgap]
  by_cases he : 0 * (c / N) < |Real.log j - Real.log n| ∧
      |Real.log j - Real.log n| ≤ 2 * (c / N)
  · simp only [if_pos he, mul_one]
    rw [nearGammaDownwardCoefficient_one_eq hc hN (mem_Icc.mp hj).1]
    ring
  · simp only [if_neg he, mul_zero, sub_zero]

/-- Logarithmic horizon weights are the terminal profile in the linear coordinate. -/
theorem horizonProfileVector_horizonWeights_eq_terminal (h : ℝ → ℝ) {N : ℕ}
    (hN : 1 ≤ N) :
    horizonProfileVector (horizonWeights h N) N =
      horizonProfileVector (fun n => logProfile h ((n : ℝ) / N) / Real.sqrt n) N := by
  ext n
  have hn0 : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (mem_Icc.mp n.property).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  change h (Real.log (n : ℕ) - Real.log N) / Real.sqrt (n : ℕ) =
    logProfile h (((n : ℕ) : ℝ) / N) / Real.sqrt (n : ℕ)
  rw [logProfile, if_pos (div_pos hn0 hN0), Real.log_div hn0.ne' hN0.ne']

/-- The full polar center pairing is exactly the weighted double-kernel sum. -/
theorem sqrt_log_mul_terminal_fullCenter_pair {N : ℕ} (hL : 0 < Real.log N)
    (α : ℝ) (u : ℕ → ℝ) :
    Real.sqrt (Real.log N) *
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector 1 N),
        horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ =
      (α / N) * ∑ n ∈ Icc 1 N, u n / Real.sqrt n *
        ∑ j ∈ Icc 1 N,
          (arithmeticPoleKernel n j - archimedeanCenterKernel n j) / Real.sqrt j := by
  have hp := sqrt_log_mul_terminal_kernel_pair (m := 1) one_pos hL
    (fun n j => α / N * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) u
  change Real.sqrt (Real.log N) *
    ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector 1 N),
      horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ = _ at hp
  rw [hp]
  simp only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one,
    ramanujanLagCoefficient_one, mul_one]
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [mul_sum, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- The actual upward source retains its literal single-row terminal pairing. -/
theorem sqrt_log_mul_terminal_upward_pair {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N m : ℕ} (hN : 2 ≤ N) (hm : 0 < m) (u : ℕ → ℝ) :
    Real.sqrt (Real.log N) *
      ⟪upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N),
        horizonProfileVector (fun n => u n / Real.sqrt n) N⟫ =
      (∑ n ∈ Icc 1 N, u n / n * upwardModeRow φ c N m n) / Real.sqrt (m.totient : ℝ) := by
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hsL : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change Real.sqrt (Real.log N) * (∑ n : PrimeHorizonIndex N, u n / Real.sqrt n *
    (upwardPrimeRow (atomDilate φ (c / N)) N
      (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
        (∫ x, atomDilate φ (c / N) x ^ 2))) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => u n / Real.sqrt n *
    (upwardPrimeRow (atomDilate φ (c / N)) N
      (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
        (∫ x, atomDilate φ (c / N) x ^ 2))), mul_sum, sum_div]
  apply sum_congr rfl
  intro n hn
  rw [upwardPrimeRow_normalizedRamanujan_eq hφ hsupp hM hc hm hN hn]
  calc
    _ = u n * upwardModeRow φ c N m n /
        ((Real.sqrt n) ^ 2 * Real.sqrt (m.totient : ℝ)) := by
      field_simp [hsL] <;> ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]; ring

/-- Restoring the conductor energy cancels the artificial pole and shell diagonals exactly. -/
theorem completeWeilMatrix_ramanujan_eq_terminal_channels {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N m : ℕ}
    (hN : 1 ≤ N) (hm : 0 < m) :
    Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) =
      -(Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) +
      completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N +
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
        (normalizedRamanujanHorizonVector m N) -
      Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N) +
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N) +
      ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
        nearCenterVector φ c N m) -
      upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) +
      (completeWeilSelfFinitePart φ c + ramanujanAdjunctionEnergy m -
        Real.eulerMascheroniConstant) • normalizedRamanujanHorizonVector m N := by
  calc
    _ = (Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N) +
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N :=
      (sub_add_cancel _ _).symm
    _ = _ := by
      rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc hN hm,
        completedConductorEnergy_eq_sub_shellCorrection hc hm]
      simp only [completeWeilAdjunctionEnergy]
      module

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.sqrt_log_mul_terminal_kernel_pair
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.sum_terminal_nearGammaDownwardRow_one_eq
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.completeWeilMatrix_ramanujan_eq_terminal_channels
