import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheGrowingGammaPairMeanIsPolar
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheActualNearCenterHasItsSignedFinitePart
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGramRetainsItsLogarithmicAccuracy
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeResidueHasASignedPolarLimit

/-!
# The growing Gamma and center residue is supported at the pole

The actual near and far Gamma pairings combine with the rational center.
Their nonpolar diagonal and divisor-jet terms cancel. After scaling by
log N / c, only the conductor-one finite part remains.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem log_mul_normalized_matrix_inner {N m l : ℕ} (hL : 0 < Real.log N)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) :
    Real.log N * ⟪Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N),
      normalizedRamanujanHorizonVector l N⟫ =
      ⟪Matrix.toEuclideanLin A (ramanujanHorizonVector m N), ramanujanHorizonVector l N⟫ := by
  simp only [normalizedRamanujanHorizonVector, map_smul, real_inner_smul_left,
    real_inner_smul_right]
  have hs : Real.log N * ((Real.sqrt (Real.log N))⁻¹ *
      (Real.sqrt (Real.log N))⁻¹) = 1 := by
    rw [← mul_inv, ← sq, Real.sq_sqrt hL.le, mul_inv_cancel₀ hL.ne']
  calc
    _ = (Real.log N * ((Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹)) *
        ⟪Matrix.toEuclideanLin A (ramanujanHorizonVector m N), ramanujanHorizonVector l N⟫ := by ring
    _ = _ := by rw [hs, one_mul]

/-- A natural-index kernel has its literal Ramanujan pairing after logarithmic normalization. -/
theorem log_mul_kernelMatrix_ramanujan_pair {N m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    (hL : 0 < Real.log N) (A : ℕ → ℕ → ℝ) :
    Real.log N * ⟪Matrix.toEuclideanLin (fun n j : PrimeHorizonIndex N => A n j)
        (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫ =
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        ramanujanLagCoefficient l n * ramanujanLagCoefficient m j * A n j /
          (Real.sqrt n * Real.sqrt j)) /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) := by
  rw [log_mul_normalized_matrix_inner hL, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, ramanujanPoleProfile l n *
    ∑ j : PrimeHorizonIndex N, A n j * ramanujanPoleProfile m j) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile l n *
    ∑ j : PrimeHorizonIndex N, A n j * ramanujanPoleProfile m j), sum_div]
  apply sum_congr rfl
  intro n hn
  rw [sum_coe_sort (Icc 1 N) (fun j => A n j * ramanujanPoleProfile m j),
    mul_sum, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [ramanujanPoleProfile_eq hm, ramanujanPoleProfile_eq hl]
  ring

/-- The complete separated matrix pairing is exactly the raw far-pair sum. -/
theorem log_mul_separatedCross_pair {φ : ℝ → ℝ} {c : ℝ} {N m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hL : 0 < Real.log N) :
    Real.log N * ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫ =
      farCrossPair φ (c / N) N (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) := by
  let A : ℕ → ℕ → ℝ := fun n j =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0
  have hpair := log_mul_kernelMatrix_ramanujan_pair hm hl hL A
  change Real.log N * ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
    (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫ = _ at hpair
  rw [hpair]
  dsimp only [A]
  unfold farCrossPair
  congr 1
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro j hj
  split_ifs <;> ring

private theorem log_mul_downward_pair {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N m l : ℕ} (hN : 1 ≤ N)
    (hm : 0 < m) (hl : 0 < l) (hL : 0 < Real.log N) :
    Real.log N * ⟪downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N),
      normalizedRamanujanHorizonVector l N⟫ =
      nrSum φ c N m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) := by
  let s : ℝ := (Real.sqrt (Real.log N))⁻¹
  have hext : ∀ k : ℕ, ∀ n ∈ Icc 1 N,
      primeHorizonExtension (normalizedRamanujanHorizonVector k N) n =
        s * primeHorizonExtension (ramanujanHorizonVector k N) n := by
    intro k n hn
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩, primeHorizonExtension_coe _ ⟨n, hn⟩]
    rfl
  have hvl (n : PrimeHorizonIndex N) : normalizedRamanujanHorizonVector l N n =
      s * primeHorizonExtension (ramanujanHorizonVector l N) n := by
    rw [primeHorizonExtension_coe]
    rfl
  have hinner : ⟪downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N),
      normalizedRamanujanHorizonVector l N⟫ =
      s ^ 2 * ((∑ n ∈ Icc 1 N, primeHorizonExtension (ramanujanHorizonVector l N) n *
        downwardPrimeRow (atomDilate φ (c / N)) N
          (primeHorizonExtension (ramanujanHorizonVector m N)) n) /
            (∫ u, atomDilate φ (c / N) u ^ 2)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ n : PrimeHorizonIndex N,
      normalizedRamanujanHorizonVector l N n *
        (downwardPrimeRow (atomDilate φ (c / N)) N
          (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
            (∫ u, atomDilate φ (c / N) u ^ 2))) = _
    rw [← sum_coe_sort (Icc 1 N)]
    rw [sum_div, mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [hvl n, downwardPrimeRow_congr_smul (hext m)]
    ring
  rw [hinner, sum_downward_ramanujan_eq hφ hsupp hM hc hN hm hl]
  have hs : Real.log N * s ^ 2 = 1 := by
    dsimp only [s]
    rw [inv_pow, Real.sq_sqrt hL.le, mul_inv_cancel₀ hL.ne']
  rw [← mul_assoc, hs, one_mul]

private theorem abs_log_gap_pos_iff {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    0 < |Real.log j - Real.log n| ↔ j ≠ n := by
  constructor
  · intro h hne
    subst j
    exact (lt_irrefl (0 : ℝ)) (by simpa only [sub_self, abs_zero] using h)
  · intro hne
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    apply abs_pos.mpr
    apply sub_ne_zero.mpr
    rcases lt_or_gt_of_ne hne with h | h
    · exact (Real.log_lt_log hj0 (by exact_mod_cast h)).ne
    · exact (Real.log_lt_log hn0 (by exact_mod_cast h)).ne'

private theorem shellAutocorr_div_abs (φ : ℝ → ℝ) (x w : ℝ) :
    shellAutocorr φ (x / w) = shellAutocorr φ (|x| / w) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), neg_div, shellAutocorr_neg]

/-- The interior downward pairing is the logarithmic near-Gram minus its divisor jet. -/
theorem nrInterior_div_totient_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N m l : ℕ} (hN : 1 ≤ N) (hm : 0 < m) (hl : 0 < l) :
    nrInterior φ c N m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) =
      Real.log N * fixedWidthNearGram φ (c / N) N l m -
        (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          fixedWidthNearPair φ (c / N) l m n j * (Real.log N - Real.log j)) -
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, fixedWidthNearJetPair φ (c / N) l m n j := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  unfold nrInterior fixedWidthNearGram
  simp only [sum_div, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro j hj
  by_cases hnear : j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * (c / N)
  · rw [if_neg hnear.1, fixedWidthNearPair, fixedWidthNearJetPair,
      if_pos hnear, if_pos hnear, ramanujanPoleProfile_eq hm,
      ramanujanPoleProfile_eq hl, shellAutocorr_div_abs φ]
    ring
  · rw [fixedWidthNearPair, fixedWidthNearJetPair, if_neg hnear, if_neg hnear]
    by_cases hjeq : j = n
    · rw [if_pos hjeq]
      ring
    · have hgt : 2 * (c / N) < |Real.log j - Real.log n| :=
        lt_of_not_ge fun h => hnear ⟨hjeq, h⟩
      have hG : shellAutocorr φ ((Real.log j - Real.log n) / (c / N)) = 0 := by
        apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
        rw [abs_div, abs_of_pos hw, le_div_iff₀ hw]
        linarith only [hgt, hw]
      rw [if_neg hjeq, hG]
      ring

/-- The overlap matrix retains its near remainder, logarithmic shell, and exact rational center. -/
theorem log_mul_overlap_pair_eq {φ : ℝ → ℝ} {c : ℝ} {N m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hL : 0 < Real.log N) :
    Real.log N * ⟪Matrix.toEuclideanLin (overlapMatrix φ c N)
        (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫ =
      gapMatrixPair (nearArchimedeanRemainder φ (c / N)) 0 2 (c / N) N
          (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) +
      Real.log (1 / (c / N)) * fixedWidthNearGram φ (c / N) N l m +
      (completeWeilPoleShift φ c / N) /
          (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) *
        nearCenterPair c N (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) := by
  let A : ℕ → ℕ → ℝ := fun n j =>
    if n ≠ j ∧ |Real.log j - Real.log n| ≤ 2 * (c / N) then
      atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) +
        (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j else 0
  have hpair := log_mul_kernelMatrix_ramanujan_pair hm hl hL A
  change Real.log N * ⟪Matrix.toEuclideanLin (overlapMatrix φ c N)
    (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫ = _ at hpair
  rw [hpair]
  dsimp only [A]
  unfold gapMatrixPair fixedWidthNearGram nearCenterPair
  have hcut : 2 * c / (N : ℝ) = 2 * (c / N) := by ring
  simp only [nearRowIndices, hcut, sum_filter, zero_mul,
    sum_div, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro j hj
  have hpos := abs_log_gap_pos_iff (mem_Icc.mp hn).1 (mem_Icc.mp hj).1
  by_cases hnear : j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * (c / N)
  · have hnear' : n ≠ j ∧ |Real.log j - Real.log n| ≤ 2 * (c / N) :=
      ⟨hnear.1.symm, hnear.2⟩
    have hgap : 0 < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ 2 * (c / N) :=
      ⟨hpos.mpr hnear.1, hnear.2⟩
    simp only [fixedWidthNearPair, nearArchimedeanRemainder,
      if_pos hnear, if_pos hnear', if_pos hgap,
      ramanujanPoleProfile_eq hm, ramanujanPoleProfile_eq hl]
    ring
  · have hnear' : ¬(n ≠ j ∧ |Real.log j - Real.log n| ≤ 2 * (c / N)) :=
      fun h => hnear ⟨h.1.symm, h.2⟩
    have hgap : ¬(0 < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ 2 * (c / N)) :=
      fun h => hnear ⟨hpos.mp h.1, h.2⟩
    simp only [fixedWidthNearPair, hnear, hnear', hgap, if_false, mul_zero, zero_div,
      zero_add]

private theorem log_mul_normalized_gram {N m l : ℕ} (hL : 0 < Real.log N) :
    Real.log N * ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ =
      ⟪ramanujanHorizonVector m N, ramanujanHorizonVector l N⟫ := by
  simp only [normalizedRamanujanHorizonVector, real_inner_smul_left, real_inner_smul_right]
  have hs : Real.log N * ((Real.sqrt (Real.log N))⁻¹ *
      (Real.sqrt (Real.log N))⁻¹) = 1 := by
    rw [← mul_inv, ← sq, Real.sq_sqrt hL.le, mul_inv_cancel₀ hL.ne']
  calc
    _ = (Real.log N * ((Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹)) *
        ⟪ramanujanHorizonVector m N, ramanujanHorizonVector l N⟫ := by ring
    _ = _ := by rw [hs, one_mul]

/-- The full center residual scales exactly by overlap, before passage to a limit. -/
theorem scaled_fullCenter_residual_eq {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N m l : ℕ} (hL : 0 < Real.log N) :
    (Real.log N / c) *
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫ =
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) N)
          (ramanujanHorizonVector m N), ramanujanHorizonVector l N⟫ -
        (if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0) *
          ⟪ramanujanHorizonVector m N, ramanujanHorizonVector l N⟫ := by
  let a : ℝ := (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)
  have hshift : completeWeilPoleShift φ c = c * a := by
    unfold completeWeilPoleShift
    dsimp only [a]
    ring
  have hmat : fullWeilCenterMatrix (completeWeilPoleShift φ c) N =
      c • fullWeilCenterMatrix a N := by
    ext n j
    change (completeWeilPoleShift φ c / N) *
      (arithmeticPoleKernel n j - archimedeanCenterKernel n j) =
      c * ((a / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j))
    rw [hshift]
    ring
  rw [inner_sub_left, real_inner_smul_left, hmat]
  simp only [map_smul, LinearMap.smul_apply, real_inner_smul_left]
  have hA := log_mul_normalized_matrix_inner (m := m) (l := l) hL (fullWeilCenterMatrix a N)
  have hG := log_mul_normalized_gram (m := m) (l := l) hL
  rw [← hA, ← hG, hshift]
  by_cases hm1 : m = 1
  · simp only [if_pos hm1]
    field_simp [hc.ne']
    ring
  · simp only [if_neg hm1, zero_mul, sub_zero]
    field_simp [hc.ne']

/-- The full center finite part is unchanged along every positive overlap clock. -/
theorem tendsto_scaled_fullCenter_residual {φ : ℝ → ℝ} {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) :
    Tendsto (fun N : ℕ => (Real.log N / c N) *
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ (c N)) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ (c N) else 0) • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫) atTop
      (𝓝 (centerSecondOrder ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) m l)) := by
  apply (tendsto_centerPairing_sub ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) hm hl).congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hL
  exact (scaled_fullCenter_residual_eq (hc N) hL).symm

/-- Exterior downward products vanish after division by overlap on a controlled growing clock. -/
theorem tendsto_nrExterior_div_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0)) (a b : ℕ) :
    Tendsto (fun N : ℕ => nrExterior φ (c N) N a b / c N) atTop (𝓝 0) := by
  let S : ℝ := ∑ d ∈ b.divisors, (d : ℝ)
  let K : ℝ := 12 * S * a.totient * (1 + Real.log 4)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hlim := he.const_mul K
  simp only [mul_zero] at hlim
  have hw := tendsto_overlap_width_of_fourth_log_error hc he
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    hw.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hL hwN
  change 1 ≤ Real.log (N : ℝ) at hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hcN : c N ≤ N := (div_le_one hN0).mp hwN.le
  have hb := abs_nrExterior_le hφ hsupp hM hc0 hN hcN a b
  have hp : 2 * (2 * c N + 1) * (c N + 1) ≤ 12 * c N ^ 2 := by
    have h1 : 2 * c N + 1 ≤ 3 * c N := by linarith [hc N]
    have h2 : c N + 1 ≤ 2 * c N := by linarith [hc N]
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul h1 h2 (by positivity) (by positivity)) zero_le_two
    nlinarith only [h]
  have hlog : Real.log (4 * (N : ℝ)) ≤ (1 + Real.log 4) * Real.log N := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hN0.ne']
    nlinarith only [mul_le_mul_of_nonneg_left hL hlog4]
  have hpoly : 2 * (2 * c N + 1) * (c N + 1) * S * a.totient * Real.log (4 * (N : ℝ)) ≤
      12 * c N ^ 2 * S * a.totient * ((1 + Real.log 4) * Real.log N) :=
    mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp hS) (Nat.cast_nonneg a.totient)) hlog
      (Real.log_nonneg (by
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith only [hN1])) (by positivity)
  have hc4 : c N ≤ c N ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ (hc N) (by norm_num : 1 ≤ 4)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hc0]
  calc
    _ ≤ (2 * (2 * c N + 1) * (c N + 1) * S * a.totient * Real.log (4 * (N : ℝ)) / N) / c N :=
      div_le_div_of_nonneg_right hb hc0.le
    _ ≤ (12 * c N ^ 2 * S * a.totient * ((1 + Real.log 4) * Real.log N) / N) / c N :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hpoly hN0.le) hc0.le
    _ = K * (c N * Real.log N / N) := by
      dsimp only [K]
      field_simp [hc0.ne']
    _ ≤ K * (c N ^ 4 * Real.log N / N) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc4 (Real.log_natCast_nonneg N)) hN0.le) hK

/-- The center and Gamma contribution to the literal complete conductor residual. -/
def gammaCenterResidual (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
    (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N) -
  Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N) +
  ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
    nearCenterVector φ c N m)

private def centerReferencePair (φ : ℝ → ℝ) (N m l : ℕ) : ℝ :=
  ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) N)
      (ramanujanHorizonVector m N), ramanujanHorizonVector l N⟫ -
    (if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0) *
      ⟪ramanujanHorizonVector m N, ramanujanHorizonVector l N⟫

private def nearLogPair (φ : ℝ → ℝ) (c : ℝ) (N m l : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    fixedWidthNearPair φ (c / N) l m n j * (Real.log N - Real.log j)

private def nearJetPair (φ : ℝ → ℝ) (c : ℝ) (N m l : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, fixedWidthNearJetPair φ (c / N) l m n j

private theorem scaled_gammaCenterResidual_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N m l : ℕ} (hN : 1 ≤ N)
    (hm : 0 < m) (hl : 0 < l) (hL : 0 < Real.log N) :
    let D : ℝ := Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)
    let a : ℝ := (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)
    (Real.log N / c) * ⟪gammaCenterResidual φ c N m, normalizedRamanujanHorizonVector l N⟫ =
      centerReferencePair φ N m l +
      (gapMatrixPair (nearArchimedeanRemainder φ (c / N)) 0 2 (c / N) N
          (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) -
        farCrossPair φ (c / N) N (ramanujanLagCoefficient l) (ramanujanLagCoefficient m)) / c / D +
      nearLogPair φ c N m l / c + nearJetPair φ c N m l / c -
      Real.log c * (fixedWidthNearGram φ (c / N) N l m / c) +
      (a / D) * (nearCenterPair c N (ramanujanLagCoefficient l) (ramanujanLagCoefficient m) / N) -
      nrExterior φ c N m l / c / D := by
  intro D a
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hov : Matrix.toEuclideanLin (overlapMatrix φ c N) (normalizedRamanujanHorizonVector m N) =
      downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) +
        ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
          nearCenterVector φ c N m) := by
    ext n
    exact overlapMatrix_ramanujan_row_eq φ c hm n
  have hshape : gammaCenterResidual φ c N m =
      (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N) +
      (Matrix.toEuclideanLin (overlapMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N)) -
      Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N) := by
    rw [hov]
    unfold gammaCenterResidual
    module
  have hscale (x : ℝ) : Real.log N / c * x = (Real.log N * x) / c := by ring
  have hoverlap :
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N),
        normalizedRamanujanHorizonVector l N⟫ =
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (normalizedRamanujanHorizonVector m N),
        normalizedRamanujanHorizonVector l N⟫ -
      ⟪downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N),
        normalizedRamanujanHorizonVector l N⟫ := inner_sub_left _ _ _
  rw [hshape, inner_sub_left, inner_add_left, hoverlap, mul_sub, mul_add,
    scaled_fullCenter_residual_eq hc hL, mul_sub]
  rw [hscale, hscale, hscale,
    log_mul_overlap_pair_eq hm hl hL, log_mul_downward_pair hφ hsupp hM hc hN hm hl hL,
    log_mul_separatedCross_pair hm hl hL,
    nrSum_eq_interior_add_exterior φ hc hN m l,
    add_div (nrInterior φ c N m l) (nrExterior φ c N m l)
      (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)),
    nrInterior_div_totient_eq hφ hsupp hc hN hm hl]
  have hlog : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc.ne' hN0.ne']
    ring
  rw [hlog]
  unfold centerReferencePair nearLogPair nearJetPair completeWeilPoleShift
  dsimp only [D, a]
  field_simp [hc.ne']
  ring

/-- The joint Gamma and center residue is supported only at conductor one. -/
theorem tendsto_scaled_gammaCenterResidual {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log N / c N) *
      ⟪gammaCenterResidual φ (c N) N m, normalizedRamanujanHorizonVector l N⟫) atTop
      (𝓝 (if m = 1 ∧ l = 1 then
        ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * (1 - Real.log (4 * Real.pi)) else 0)) := by
  let a : ℝ := (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)
  let D : ℝ := Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  have he1 := tendsto_fourth_overlap_log_error_of_sq hc he
  have hw := tendsto_overlap_width_of_fourth_log_error hc he1
  have hcenter : Tendsto (fun N : ℕ => centerReferencePair φ N m l) atTop
      (𝓝 (centerSecondOrder a m l)) := tendsto_centerPairing_sub a hm hl
  have hgamma := (tendsto_nearArchimedean_sub_farCross_pair_div_overlap
    hφ hsupp hM hl hm hc0 hcinf hw).div_const D
  have hlog := tendsto_fixedWidthNearPair_log_row_div_overlap hφ hsupp hM hc hcinf he1 hl hm
  have hjet := tendsto_fixedWidthNearJetPair_sum_div_overlap hφ hsupp hM hc hcinf he1 hl hm
  have hnear := (tendsto_nearCenterPair_finite_part hm hl hc0 hcinf hw).const_mul (a / D)
  have hgram := tendsto_log_mul_fixedWidthNearGram_relative_error hφ hsupp hM hl hm hc hcinf he
  have hexterior := (tendsto_nrExterior_div_overlap hφ hsupp hM hc he1 m l).div_const D
  have hsum := (((((hcenter.add hgamma).add hlog).add hjet).add hnear).sub hgram).sub hexterior
  simp only [zero_div, sub_zero] at hsum
  have hconstant : centerSecondOrder a m l +
      (if l = 1 ∧ m = 1 then -a * (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant)
        else 0) / D +
      (if l = m then if l = 1 then a else 0 else 0) +
      (if l = 1 then a * (ArithmeticFunction.vonMangoldt m : ℝ) /
        Real.sqrt (m.totient : ℝ) else 0) +
      (a / D) * (if m = l then
        (if m = 1 then Real.log 2 + Real.eulerMascheroniConstant - 1
          else -(ArithmeticFunction.vonMangoldt m : ℝ)) else 0) =
      (if m = 1 ∧ l = 1 then a * (1 - Real.log (4 * Real.pi)) else 0) := by
    by_cases hm1 : m = 1
    · subst m
      by_cases hl1 : l = 1
      · subst l
        simp only [D, centerSecondOrder, centerLimitCoeff, and_self, if_true, Nat.totient_one,
          Nat.cast_one, Real.sqrt_one, mul_one, div_one, ArithmeticFunction.vonMangoldt_apply_one,
          mul_zero, add_zero]
        ring
      · have h1l : (1 : ℕ) ≠ l := Ne.symm hl1
        simp only [D, centerSecondOrder, centerLimitCoeff, h1l, hl1, and_false, false_and,
          if_false, mul_zero, zero_div, add_zero]
    · by_cases hl1 : l = 1
      · subst l
        have h1m : (1 : ℕ) ≠ m := Ne.symm hm1
        simp only [D, centerSecondOrder, centerLimitCoeff, hm1, h1m, false_and, and_false,
          if_false, if_true, Nat.totient_one, Nat.cast_one, Real.sqrt_one, mul_one,
          mul_zero, add_zero]
        ring
      · by_cases hml : m = l
        · subst l
          simp only [D, centerSecondOrder, centerLimitCoeff, hm1, false_and, if_false,
            if_true, zero_div, add_zero]
          ring
        · have hlm : l ≠ m := Ne.symm hml
          simp only [D, centerSecondOrder, centerLimitCoeff, hm1, hl1, hml, hlm,
            false_and, if_false, mul_zero, zero_div, add_zero]
  change Tendsto _ atTop (𝓝 (if m = 1 ∧ l = 1 then a * (1 - Real.log (4 * Real.pi)) else 0))
  rw [hconstant] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
      with N hN hL
  rw [scaled_gammaCenterResidual_eq hφ hsupp hM (hc0 N) hN hm hl hL]
  dsimp only [nearLogPair, nearJetPair, a]
  by_cases hm1 : m = 1
  · subst m
    by_cases hl1 : l = 1
    · subst l
      simp only [and_self, if_true, D, Nat.totient_one, Nat.cast_one, Real.sqrt_one, mul_one, div_one]
      ring
    · simp only [hl1, and_false, false_and, if_false, sub_zero]
      ring
  · simp only [hm1, and_false, false_and, if_false, sub_zero]
    ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.log_mul_overlap_pair_eq
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.nrInterior_div_totient_eq
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_scaled_fullCenter_residual
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_nrExterior_div_overlap
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.scaled_gammaCenterResidual_eq
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_scaled_gammaCenterResidual
