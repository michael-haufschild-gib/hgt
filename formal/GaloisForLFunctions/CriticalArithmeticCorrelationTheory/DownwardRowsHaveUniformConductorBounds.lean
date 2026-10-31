import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NearGammaDownwardCancellationHasPolynomialGrowth
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel

/-!
# Uniform conductor costs for the complete downward source

The exact divisor-jet identity cancels the near-pair logarithm. Its quadratic
conductor envelope gives a fourth-power squared-mass bound. Exterior prime
products retain this same bound after logarithmic normalization.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell
  SuccessorShellArithmetic ArithmeticIntersectionTheory

/-- The full divisor jet has a quadratic conductor envelope. -/
private theorem abs_divisorJet_le_conductor_sq {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |ramanujanLogDivisorJet m n| ≤ 2 * (m : ℝ) ^ 2 := by
  have hmangoldt : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
  have htri := abs_add_le (ramanujanLogDivisorJet m n - ArithmeticFunction.vonMangoldt m)
    (ArithmeticFunction.vonMangoldt m)
  rw [sub_add_cancel, abs_of_nonneg hmangoldt] at htri
  have henvelope := abs_ramanujanLogDivisorJet_sub_mean_le hm n
  have htot : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log (m : ℝ) ≤ m :=
    (Real.log_le_sub_one_of_pos hm0).trans (by linarith only)
  have hdiff := mul_le_mul_of_nonneg_left (tameDifferent_le_log hm) (Nat.cast_nonneg m.totient)
  have hprod := mul_le_mul htot hlog (Real.log_natCast_nonneg m) hm0.le
  nlinarith only [htri, henvelope, hdiff, hprod]

/-- Exact downward cancellation has one coefficient constant before the conductor factor. -/
theorem exists_nearGammaDownwardCoefficient_uniform_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
        |nearGammaDownwardCoefficient φ c N m n j| ≤ E * (m : ℝ) ^ 2 * c := by
  obtain ⟨C, hC, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let R : ℝ := 2 * Real.exp 2
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  refine ⟨C + R + 3, by positivity, ?_⟩
  intro m hm c hc1 N hN hw1 n hn j hj
  let A : ℝ := m
  let J : ℝ := 2 * (m : ℝ) ^ 2
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hc : 0 < c := zero_lt_one.trans_le hc1
  let B := linearNearRowRadius c
  have hB : 0 ≤ B := by dsimp only [B, linearNearRowRadius]; positivity
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hlogc : |Real.log c| ≤ c := by
    rw [abs_of_nonneg (Real.log_nonneg hc1)]
    exact (Real.log_le_sub_one_of_pos hc).trans (by linarith only [hc])
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hjN := (mem_filter.mp hj).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
  have hw0 : 0 < c / N := div_pos hc hN0
  have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
    have h := (mem_filter.mp hj).2.2
    change |Real.log j - Real.log n| ≤ 2 * c / N at h
    simpa only [mul_div_assoc] using h
  let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)
  let a := atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2)
  have hrem : |a - Real.log (1 / (c / N)) * q| ≤ C := by
    simpa only [a, q, mul_div_assoc] using hpair (c / N) hw0 hw1 n j hs
  have hq : |q| ≤ 1 := by
    have h := abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp)
      (|Real.log j - Real.log n| / (c / N))
    change |shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ ∫ u, φ u ^ 2 at h
    dsimp only [q]
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact h
  have hcm : |ramanujanLagCoefficient m j| ≤ A :=
    (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j).trans
      (by dsimp only [A]; exact_mod_cast Nat.totient_le m)
  have hjb : |ramanujanLogDivisorJet m j| ≤ J := abs_divisorJet_le_conductor_sq hm j
  have hquot : (N : ℝ) / j ≤ B :=
    (div_le_iff₀ hj0).mpr (nearRow_geometry_small_width hc hn hj hw).2.2
  have hloglow : 0 ≤ Real.log N - Real.log j := sub_nonneg.mpr
    (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
  have hloghigh : Real.log N - Real.log j ≤ B := by
    have h := Real.log_le_sub_one_of_pos (div_pos hN0 hj0)
    rw [Real.log_div hN0.ne' hj0.ne'] at h
    linarith only [h, hquot]
  have hlogeq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc.ne' hN0.ne']
    ring
  have hlog : |Real.log (1 / (c / N)) - Real.log j| ≤ B + |Real.log c| := by
    rw [hlogeq, show Real.log N - Real.log c - Real.log j =
      (Real.log N - Real.log j) - Real.log c by ring]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hloglow]; linarith only [hloghigh])
  have heq : nearGammaDownwardCoefficient φ c N m n j =
      (a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
      (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
      q * ramanujanLogDivisorJet m j := by
    rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m
      (mem_Icc.mp hjN).1]
    dsimp only [a, q]
    ring
  rw [heq]
  calc
    _ ≤ |(a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j| +
        |(Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j| +
        |q * ramanujanLogDivisorJet m j| := abs_add_three _ _ _
    _ ≤ C * A + (B + |Real.log c|) * A + J := by
      simp only [abs_mul]
      have h1 := mul_le_mul hrem hcm (abs_nonneg _) hC
      have h2 := mul_le_mul (mul_le_mul hlog hq (abs_nonneg _) (by positivity))
        hcm (abs_nonneg _) (by positivity)
      have h3 := mul_le_mul hq hjb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simp only [mul_one, one_mul] at h2 h3
      linarith only [h1, h2, h3]
    _ ≤ ((C + R + 1) * A + J) * c := by
      have hlog := mul_le_mul_of_nonneg_right hlogc hA
      have hCmul := mul_le_mul_of_nonneg_left hc1 (mul_nonneg hC hA)
      have hJmul := mul_le_mul_of_nonneg_left hc1 hJ
      dsimp only [B, linearNearRowRadius, R]
      nlinarith only [hlog, hCmul, hJmul]
    _ ≤ _ := by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1]
      have hscale := mul_le_mul_of_nonneg_left hm2
        (show 0 ≤ C + R + 1 by positivity)
      apply mul_le_mul_of_nonneg_right _ hc.le
      dsimp only [A, J]
      nlinarith only [hscale]

/-- Near-row geometry converts the quadratic coefficient envelope to fourth-power mass. -/
theorem exists_nearGammaDownwardRow_uniform_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      (∑ n ∈ Icc 1 N, nearGammaDownwardRow φ c N m n ^ 2) ≤
        C * (m : ℝ) ^ 4 * c ^ 5 := by
  obtain ⟨E, hE, hbound⟩ :=
    exists_nearGammaDownwardCoefficient_uniform_conductor_bound hφ hsupp hM
  refine ⟨4 * (2 * Real.exp 2) ^ 3 * E ^ 2, by positivity, ?_⟩
  intro m hm c hc N hN hw
  have hb := sum_near_div_sqrt_sq_le_small_width (zero_lt_one.trans_le hc) hN
    (hw.trans (by norm_num)) (nearGammaDownwardCoefficient φ c N m)
    (hbound m hm c hc N hN hw)
  exact hb.trans_eq (by unfold linearNearRowRadius; ring)

/-- The literal downward source, including exterior products, has a uniform conductor cost. -/
theorem exists_fullNearGammaDownward_uniform_conductor_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      ‖normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
        C * (m : ℝ) ^ 4 * c ^ 5 / Real.log N := by
  obtain ⟨A, hA, hnear⟩ := exists_nearGammaDownwardRow_uniform_conductor_bound hφ hsupp hM
  let B : ℝ := (Real.exp 1 + 2) * (2 * (Real.exp 1 + 1)) ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨2 * (A + B), by positivity, ?_⟩
  intro m hm c hc N hN hw
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp (div_pos hc0 hN0)
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq (div_pos hc0 hN0)]
    exact mul_pos (div_pos hc0 hN0) hM
  have hnear' : ‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      A * (m : ℝ) ^ 4 * c ^ 5 / Real.log N := by
    rw [normalizedNearGammaDownwardVector_norm_sq]
    exact div_le_div_of_nonneg_right (hnear m hm c hc N hN hw)
      (Real.log_natCast_nonneg N)
  have hext : ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
      B * (m : ℝ) ^ 4 * c ^ 5 / Real.log N := by
    rw [normalizedExteriorDownwardVector_norm_sq]
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
    have ht : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1]
    have ht2 := pow_le_pow_left₀ (Nat.cast_nonneg m.totient) (ht.trans hm2) 2
    have hc35 := pow_le_pow_right₀ hc (by norm_num : 3 ≤ 5)
    calc
      _ ≤ ((Real.exp 1 + 2) * (2 * m.totient * (Real.exp 1 + 1)) ^ 2) * c ^ 3 :=
        sum_actualExteriorDownwardRow_sq_le_polynomial hg.continuous hc hN hgsupp hG
          (hw.trans (by norm_num)) m
      _ = B * (m.totient : ℝ) ^ 2 * c ^ 3 := by dsimp only [B]; ring
      _ ≤ B * (m : ℝ) ^ 4 * c ^ 5 := by
        have hm4 : (m.totient : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := by
          simpa only [← pow_mul] using ht2
        exact mul_le_mul (mul_le_mul_of_nonneg_left hm4 hB) hc35
          (by positivity) (by positivity)
  rw [normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0]
  have htriangle := norm_sub_le (normalizedNearGammaDownwardVector φ c N m)
    (normalizedExteriorDownwardVector φ c N m)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  have hdiff := sq_nonneg (‖normalizedNearGammaDownwardVector φ c N m‖ -
    ‖normalizedExteriorDownwardVector φ c N m‖)
  calc
    _ ≤ 2 * (‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 +
        ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2) := by
      nlinarith only [hsq, hdiff]
    _ ≤ 2 * (A * (m : ℝ) ^ 4 * c ^ 5 / Real.log N +
        B * (m : ℝ) ^ 4 * c ^ 5 / Real.log N) :=
      mul_le_mul_of_nonneg_left (add_le_add hnear' hext) zero_le_two
    _ = _ := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_nearGammaDownwardCoefficient_uniform_conductor_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_nearGammaDownwardRow_uniform_conductor_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_fullNearGammaDownward_uniform_conductor_bound

