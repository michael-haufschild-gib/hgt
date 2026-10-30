import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheWeightedPrimeShellsAreUniformOnBoundedOverlap

/-!
# Polynomial growth of the full affine prime shells

Autocorrelation support confines every active prime index to `k ≥ X/c`.
The complete Chebyshev bound then gives a quadratic overlap bound for
the literal shell source, its signed mean, and their error.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem abs_affineRamanujanPrimeShell_le_linear_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (q n b : ℕ) {c X : ℝ} (hc : 0 < c) (hX : 1 ≤ X)
    {h : ℕ} (hh : 1 ≤ h) :
    |affineRamanujanPrimeShell q n b φ c h X| ≤
      (Real.log 4 + 4) * q.totient * (∫ u, φ u ^ 2) * c := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hC : 0 ≤ Real.log (4 : ℝ) + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith only [this]
  have hG (s : ℝ) : |shellAutocorr φ s| ≤ ∫ u, φ u ^ 2 :=
    abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) s
  have hpoint (k : ℕ) (hk : k ∈ Icc 1 ⌊X⌋₊) :
      |(ArithmeticFunction.vonMangoldt k : ℝ) / k * ramanujanLagCoefficient q (k * n + b) *
        shellAutocorr φ ((h : ℝ) * X / (c * k))| ≤
      (c / X) * (ArithmeticFunction.vonMangoldt k : ℝ) * q.totient * (∫ u, φ u ^ 2) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt k : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    by_cases hz : shellAutocorr φ ((h : ℝ) * X / (c * k)) = 0
    · rw [hz, mul_zero, abs_zero]
      positivity
    · have hs : (h : ℝ) * X / (c * k) < 1 := by
        by_contra hnot
        exact hz (shellAutocorr_eq_zero_of_one_le hφ hsupp (le_of_not_gt hnot))
      have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
      have hactive : X ≤ c * k := by
        have hb := (div_lt_one (mul_pos hc hk0)).mp hs
        have hlow := mul_le_mul_of_nonneg_right hhR hX0.le
        nlinarith only [hb, hlow]
      have hinv : 1 / (k : ℝ) ≤ c / X := by
        apply (div_le_div_iff₀ hk0 hX0).mpr
        simpa only [one_mul] using hactive
      have hw : (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤
          (c / X) * ArithmeticFunction.vonMangoldt k := by
        calc
          _ = (ArithmeticFunction.vonMangoldt k : ℝ) * (1 / (k : ℝ)) := by ring
          _ ≤ (ArithmeticFunction.vonMangoldt k : ℝ) * (c / X) :=
            mul_le_mul_of_nonneg_left hinv hΛ
          _ = _ := mul_comm _ _
      rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg hΛ hk0.le)]
      exact mul_le_mul
        (mul_le_mul hw (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient
          q (k * n + b)) (abs_nonneg _) (mul_nonneg (div_nonneg hc.le hX0.le) hΛ))
        (hG _) (abs_nonneg _) (by positivity)
  have hsum : (∑ k ∈ Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ)) = Chebyshev.psi X := by
    rw [Chebyshev.psi]
    congr 1
  unfold affineRamanujanPrimeShell
  calc
    _ ≤ ∑ k ∈ Icc 1 ⌊X⌋₊, |(ArithmeticFunction.vonMangoldt k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + b) * shellAutocorr φ ((h : ℝ) * X / (c * k))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Icc 1 ⌊X⌋₊,
        (c / X) * (ArithmeticFunction.vonMangoldt k : ℝ) * q.totient * (∫ u, φ u ^ 2) :=
      sum_le_sum hpoint
    _ = (c / X) * q.totient * (∫ u, φ u ^ 2) * Chebyshev.psi X := by
      rw [← hsum, mul_sum]
      exact sum_congr rfl fun k _ => by ring
    _ ≤ (c / X) * q.totient * (∫ u, φ u ^ 2) * ((Real.log 4 + 4) * X) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self hX0.le) (by positivity)
    _ = _ := by field_simp

/-- The full affine prime source is polynomially bounded in overlap at every source horizon. -/
theorem abs_affinePrimeShellCorrectionOfShift_le_polynomial {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (q n : ℕ) (shift : ℕ → ℕ)
    {c X : ℝ} (hc : 1 ≤ c) (hX : 1 ≤ X) :
    |affinePrimeShellCorrectionOfShift q n shift φ c X| ≤
      4 * (Real.log 4 + 4) * q.totient * c ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hC : 0 ≤ Real.log (4 : ℝ) + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith only [this]
  have hcard : ((Ico 1 ⌈c⌉₊).card : ℝ) ≤ 2 * c := by
    have hn : (Ico 1 ⌈c⌉₊).card ≤ ⌈c⌉₊ := by rw [Nat.card_Ico]; omega
    have hceil : (⌈c⌉₊ : ℝ) < c + 1 := Nat.ceil_lt_add_one hc0.le
    have hnr : ((Ico 1 ⌈c⌉₊).card : ℝ) ≤ ⌈c⌉₊ := by exact_mod_cast hn
    linarith only [hnr, hceil, hc]
  unfold affinePrimeShellCorrectionOfShift
  rw [abs_mul, abs_of_pos (div_pos zero_lt_two hM)]
  calc
    _ ≤ (2 / (∫ u, φ u ^ 2)) * ∑ h ∈ Ico 1 ⌈c⌉₊,
        |affineRamanujanPrimeShell q n (shift h) φ c h X| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (2 / (∫ u, φ u ^ 2)) * ∑ _h ∈ Ico 1 ⌈c⌉₊,
        (Real.log 4 + 4) * q.totient * (∫ u, φ u ^ 2) * c :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun h hh =>
        abs_affineRamanujanPrimeShell_le_linear_overlap hφ hsupp hM q n (shift h) hc0 hX
          (mem_Ico.mp hh).1) (by positivity)
    _ = 2 * (Real.log 4 + 4) * q.totient * (Ico 1 ⌈c⌉₊).card * c := by
      rw [sum_const, nsmul_eq_mul]
      field_simp
    _ ≤ 2 * (Real.log 4 + 4) * q.totient * (2 * c) * c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity)) hc0.le
    _ = _ := by ring

/-- The signed shell mean inherits the same polynomial bound as its actual source. -/
theorem abs_shellCorrectionOfShift_mean_le_polynomial {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (n : ℕ) (shift : ℕ → ℕ) {c : ℝ} (hc : 1 ≤ c) :
    |ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤
      4 * (Real.log 4 + 4) * q.totient * c ^ 2 := by
  by_contra hbad
  have hgap : 0 < |ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| -
      4 * (Real.log 4 + 4) * q.totient * c ^ 2 := sub_pos.mpr (lt_of_not_ge hbad)
  obtain ⟨X, hsource, hX⟩ := ((eventually_affinePrimeShellCorrectionOfShift_uniform hq hφ hsupp
    (zero_lt_one.trans_le hc) shift (half_pos hgap)).and (eventually_ge_atTop (1 : ℝ))).exists
  have hbound := abs_affinePrimeShellCorrectionOfShift_le_polynomial hφ hsupp hM q n shift hc hX
  have htri := abs_sub (affinePrimeShellCorrectionOfShift q n shift φ c X)
    (affinePrimeShellCorrectionOfShift q n shift φ c X -
      ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift)
  have hid : affinePrimeShellCorrectionOfShift q n shift φ c X -
      (affinePrimeShellCorrectionOfShift q n shift φ c X -
        ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift) =
      ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift := by ring
  rw [hid] at htri
  linarith only [hsource n, hbound, htri, hgap]

/-- Every affine multiplier and every shell-shift family share one polynomial global error. -/
theorem abs_affineShellCorrection_error_le_polynomial {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (n : ℕ) (shift : ℕ → ℕ) {c X : ℝ}
    (hc : 1 ≤ c) (hX : 1 ≤ X) :
    |affinePrimeShellCorrectionOfShift q n shift φ c X -
      ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤
        8 * (Real.log 4 + 4) * q.totient * c ^ 2 := by
  have hs := abs_affinePrimeShellCorrectionOfShift_le_polynomial hφ hsupp hM q n shift hc hX
  have hm := abs_shellCorrectionOfShift_mean_le_polynomial hq hφ hsupp hM n shift hc
  have ht := abs_sub (affinePrimeShellCorrectionOfShift q n shift φ c X)
    (ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift)
  linarith only [hs, hm, ht]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_affinePrimeShellCorrectionOfShift_le_polynomial
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_affineShellCorrection_error_le_polynomial
