import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AffinePrimeShellsHavePolynomialGrowth

/-!
# Active-shell counting gives a linear affine prime source

At a fixed prime-power index `k`, support permits only `h < ck/X`.
Interchanging the finite sums before estimating therefore cancels the
prime weight's denominator and leaves the complete Chebyshev sum.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-- Positive samples of a supported autocorrelation have at most linear mass. -/
theorem sum_abs_shellAutocorr_samples_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 ≤ ∫ u, φ u ^ 2) {r : ℝ} (hr : 0 < r) (H : ℕ) :
    (∑ h ∈ Ico 1 H, |shellAutocorr φ ((h : ℝ) / r)|) ≤ r * ∫ u, φ u ^ 2 := by
  classical
  let S : Finset ℕ := (Ico 1 H).filter (fun h : ℕ => (h : ℝ) < r)
  have heq : (∑ h ∈ S, |shellAutocorr φ ((h : ℝ) / r)|) =
      ∑ h ∈ Ico 1 H, |shellAutocorr φ ((h : ℝ) / r)| := by
    apply sum_subset (filter_subset _ _)
    intro h hh hnot
    have hge : r ≤ (h : ℝ) := by
      by_contra h
      exact hnot (mem_filter.mpr ⟨hh, lt_of_not_ge h⟩)
    rw [shellAutocorr_eq_zero_of_one_le hφ hsupp ((one_le_div hr).mpr hge), abs_zero]
  have hsub : S ⊆ Ico 1 ⌈r⌉₊ := by
    intro h hh
    exact mem_Ico.mpr ⟨(mem_Ico.mp (mem_filter.mp hh).1).1,
      Nat.lt_ceil.mpr (mem_filter.mp hh).2⟩
  have hceil1 : 1 ≤ ⌈r⌉₊ := by
    by_contra hnot
    have hz : ⌈r⌉₊ = 0 := by omega
    have hle := Nat.le_ceil r
    rw [hz, Nat.cast_zero] at hle
    linarith only [hr, hle]
  have hcard : (S.card : ℝ) ≤ r := by
    have hs : (S.card : ℝ) ≤ (Ico 1 ⌈r⌉₊).card := by exact_mod_cast card_le_card hsub
    have ht : ((Ico 1 ⌈r⌉₊).card : ℝ) ≤ r := by
      rw [Nat.card_Ico, Nat.cast_sub hceil1, Nat.cast_one]
      have h := Nat.ceil_lt_add_one hr.le
      linarith only [h]
    exact hs.trans ht
  rw [← heq]
  calc
    _ ≤ ∑ _h ∈ S, ∫ u, φ u ^ 2 := sum_le_sum fun h _ =>
      abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _
    _ = (S.card : ℝ) * ∫ u, φ u ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hM

/-- The literal affine source is linear in overlap, uniformly in conductor and shifts. -/
theorem abs_affinePrimeShellCorrectionOfShift_le_linear {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (q n : ℕ) (shift : ℕ → ℕ)
    {c X : ℝ} (hc : 0 < c) (hX : 1 ≤ X) :
    |affinePrimeShellCorrectionOfShift q n shift φ c X| ≤
      2 * (Real.log 4 + 4) * q.totient * c := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  let M := ∫ u, φ u ^ 2
  have hM0 : 0 < M := hM
  have hinner (k : ℕ) (hk : k ∈ Icc 1 ⌊X⌋₊) :
      |∑ h ∈ Ico 1 ⌈c⌉₊, (ArithmeticFunction.vonMangoldt k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + shift h) *
          shellAutocorr φ ((h : ℝ) * X / (c * k))| ≤
        (c / X) * q.totient * M * ArithmeticFunction.vonMangoldt k := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt k : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hsample := sum_abs_shellAutocorr_samples_le hφ hsupp hM.le
      (div_pos (mul_pos hc hk0) hX0) ⌈c⌉₊
    have hid (h : ℕ) : (h : ℝ) / (c * k / X) = (h : ℝ) * X / (c * k) := by field_simp
    simp_rw [hid] at hsample
    calc
      _ ≤ ∑ h ∈ Ico 1 ⌈c⌉₊, |(ArithmeticFunction.vonMangoldt k : ℝ) / k *
          ramanujanLagCoefficient q (k * n + shift h) *
            shellAutocorr φ ((h : ℝ) * X / (c * k))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Ico 1 ⌈c⌉₊, ((ArithmeticFunction.vonMangoldt k : ℝ) / k * q.totient) *
          |shellAutocorr φ ((h : ℝ) * X / (c * k))| := by
        apply sum_le_sum
        intro h _
        rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg hΛ hk0.le)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q _)
            (div_nonneg hΛ hk0.le)) (abs_nonneg _)
      _ = ((ArithmeticFunction.vonMangoldt k : ℝ) / k * q.totient) *
          ∑ h ∈ Ico 1 ⌈c⌉₊, |shellAutocorr φ ((h : ℝ) * X / (c * k))| := (mul_sum _ _ _).symm
      _ ≤ ((ArithmeticFunction.vonMangoldt k : ℝ) / k * q.totient) * (c * k / X * M) :=
        mul_le_mul_of_nonneg_left hsample (by positivity)
      _ = _ := by field_simp
  have hsum : (∑ k ∈ Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ)) = Chebyshev.psi X := by
    rw [Chebyshev.psi]
    congr 1
  unfold affinePrimeShellCorrectionOfShift affineRamanujanPrimeShell
  rw [sum_comm, abs_mul, abs_of_pos (div_pos zero_lt_two hM)]
  calc
    _ ≤ (2 / M) * ∑ k ∈ Icc 1 ⌊X⌋₊, |∑ h ∈ Ico 1 ⌈c⌉₊,
        (ArithmeticFunction.vonMangoldt k : ℝ) / k * ramanujanLagCoefficient q (k * n + shift h) *
          shellAutocorr φ ((h : ℝ) * X / (c * k))| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (2 / M) * ∑ k ∈ Icc 1 ⌊X⌋₊,
        (c / X) * q.totient * M * ArithmeticFunction.vonMangoldt k :=
      mul_le_mul_of_nonneg_left (sum_le_sum hinner) (by positivity)
    _ = (2 / M) * ((c / X) * q.totient * M * Chebyshev.psi X) := by
      rw [← hsum]
      congr 1
      exact (mul_sum _ _ _).symm
    _ ≤ (2 / M) * ((c / X) * q.totient * M * ((Real.log 4 + 4) * X)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self hX0.le) (by positivity))
        (by positivity)
    _ = _ := by field_simp

/-- The signed arithmetic mean inherits the uniform linear source bound. -/
theorem abs_shellCorrectionOfShift_mean_le_linear {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (n : ℕ) (shift : ℕ → ℕ) {c : ℝ} (hc : 0 < c) :
    |ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤
      2 * (Real.log 4 + 4) * q.totient * c := by
  by_contra hbad
  have hgap : 0 < |ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| -
      2 * (Real.log 4 + 4) * q.totient * c := sub_pos.mpr (lt_of_not_ge hbad)
  obtain ⟨X, hsource, hX⟩ := ((eventually_affinePrimeShellCorrectionOfShift_uniform hq hφ hsupp
    hc shift (half_pos hgap)).and (eventually_ge_atTop (1 : ℝ))).exists
  have hbound := abs_affinePrimeShellCorrectionOfShift_le_linear hφ hsupp hM q n shift hc hX
  have htri := abs_sub (affinePrimeShellCorrectionOfShift q n shift φ c X)
    (affinePrimeShellCorrectionOfShift q n shift φ c X -
      ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift)
  have hid : affinePrimeShellCorrectionOfShift q n shift φ c X -
      (affinePrimeShellCorrectionOfShift q n shift φ c X -
        ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift) =
      ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift := by ring
  rw [hid] at htri
  linarith only [hsource n, hbound, htri, hgap]

/-- The full affine error has a linear bound at every horizon. -/
theorem abs_affineShellCorrection_error_le_linear {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (n : ℕ) (shift : ℕ → ℕ) {c X : ℝ}
    (hc : 0 < c) (hX : 1 ≤ X) :
    |affinePrimeShellCorrectionOfShift q n shift φ c X -
      ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤
        4 * (Real.log 4 + 4) * q.totient * c := by
  have hs := abs_affinePrimeShellCorrectionOfShift_le_linear hφ hsupp hM q n shift hc hX
  have hm := abs_shellCorrectionOfShift_mean_le_linear hq hφ hsupp hM n shift hc
  have ht := abs_sub (affinePrimeShellCorrectionOfShift q n shift φ c X)
    (ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift)
  linarith only [hs, hm, ht]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_abs_shellAutocorr_samples_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_affinePrimeShellCorrectionOfShift_le_linear
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_shellCorrectionOfShift_mean_le_linear
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_affineShellCorrection_error_le_linear
