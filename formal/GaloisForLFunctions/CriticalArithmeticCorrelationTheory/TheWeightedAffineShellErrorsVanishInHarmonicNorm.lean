import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheWeightedAffinePrimeShellsHaveTheirSignedMean
import GaloisForLFunctions.HTGeometry.HarmonicQuotientSquareError

/-!
# Weighted affine shell errors vanish in harmonic norm

Uniform affine prime-shell convergence controls the entire moving horizon
`N/n`. A bounded tail supremum turns the source error into a vanishing
harmonic-quotient majorant, yielding convergence in Euclidean norm after
logarithmic normalization. Arbitrary fixed shell shifts include negative
offsets represented modulo the conductor.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A nonnegative shift representing the negative offset modulo the conductor. -/
def reflectedAffineShift (q h : ℕ) : ℕ := q * h - h

theorem ramanujanLagCoefficient_reflectedShift {q : ℕ} (hq : 1 ≤ q) (h : ℕ) :
    ramanujanLagCoefficient q (reflectedAffineShift q h) = ramanujanLagCoefficient q h := by
  have hlow : h ≤ q * h := by simpa only [one_mul] using Nat.mul_le_mul_right h hq
  unfold ramanujanLagCoefficient reflectedAffineShift
  apply sum_congr rfl
  intro d hd
  have hdM : d ∣ q * h := (Nat.dvd_of_mem_divisors hd).trans (dvd_mul_right q h)
  have he : d ∣ q * h - h ↔ d ∣ h := by
    constructor
    · intro hb
      simpa only [Nat.sub_sub_self hlow] using Nat.dvd_sub hdM hb
    · exact Nat.dvd_sub hdM
  simp only [he]

theorem ramanujanLagCoefficient_sub_eq_reflected {q : ℕ} (hq : 1 ≤ q)
    {T h : ℕ} (hhT : h ≤ T) :
    ramanujanLagCoefficient q (T - h) =
      ramanujanLagCoefficient q (T + reflectedAffineShift q h) := by
  have hlow : h ≤ q * h := by simpa only [one_mul] using Nat.mul_le_mul_right h hq
  have heq : T + reflectedAffineShift q h = (T - h) + q * h := by
    dsimp only [reflectedAffineShift]
    omega
  have hmod : Nat.ModEq q (T - h) (T + reflectedAffineShift q h) := by
    change (T - h) % q = (T + reflectedAffineShift q h) % q
    rw [heq, Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, add_zero, Nat.mod_mod]
  unfold ramanujanLagCoefficient
  exact sum_congr rfl fun d hd => by
    simp only [hmod.dvd_iff (Nat.dvd_of_mem_divisors hd)]

private theorem abs_affineRamanujanPrimeShell_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0) (q n b : ℕ) (c : ℝ) (h : ℕ) (X : ℝ) :
    |affineRamanujanPrimeShell q n b φ c h X| ≤
      (q.totient : ℝ) * (∫ u, φ u ^ 2) * mertensSum ⌊X⌋₊ := by
  have hG (s : ℝ) : |shellAutocorr φ s| ≤ ∫ u, φ u ^ 2 :=
    abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) s
  unfold affineRamanujanPrimeShell
  calc
    _ ≤ ∑ k ∈ Icc 1 ⌊X⌋₊, |(ArithmeticFunction.vonMangoldt k : ℝ) / k *
        ramanujanLagCoefficient q (k * n + b) * shellAutocorr φ ((h : ℝ) * X / (c * k))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) / k *
        (q.totient : ℝ) * (∫ u, φ u ^ 2) := by
      apply sum_le_sum
      intro k _
      have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt k : ℝ) / k :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
      rw [abs_mul, abs_mul, abs_of_nonneg hΛ]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q (k * n + b)) hΛ)
        (hG _) (abs_nonneg _) (mul_nonneg hΛ (Nat.cast_nonneg _))
    _ = _ := by
      rw [mertensSum, mul_sum]
      exact sum_congr rfl fun k _ => by ring

/-- Literal reciprocal shell readings with an arbitrary fixed affine shift in each shell. -/
def affinePrimeShellCorrectionOfShift (q n : ℕ) (shift : ℕ → ℕ)
    (φ : ℝ → ℝ) (c X : ℝ) : ℝ :=
  2 / (∫ u, φ u ^ 2) * ∑ h ∈ Ico 1 ⌈c⌉₊,
    affineRamanujanPrimeShell q n (shift h) φ c h X

/-- The exact signed unit mean for the chosen shell shifts. -/
def shellCorrectionOfShift (φ : ℝ → ℝ) (c : ℝ) (q : ℕ) (shift : ℕ → ℕ) : ℝ :=
  2 / ((∫ u, φ u ^ 2) * q.totient) * ∑ h ∈ Ico 1 ⌈c⌉₊,
    ramanujanLagCoefficient q (shift h) * ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u

theorem eventually_affinePrimeShellCorrectionOfShift_uniform {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) (shift : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ,
      |affinePrimeShellCorrectionOfShift q n shift φ c X -
        ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤ ε := by
  let S := Ico 1 ⌈c⌉₊
  let A := 2 / (∫ u, φ u ^ 2)
  let δ := ε / (|A| * S.card + 1)
  have hden : 0 < |A| * (S.card : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : δ * (|A| * S.card + 1) = ε := div_mul_cancel₀ ε hden.ne'
  -- The overlap fixes a finite shell family, so their common horizon is uniform in the mode index.
  have hevent : ∀ᶠ X : ℝ in atTop, ∀ h : S, ∀ n b : ℕ,
      |affineRamanujanPrimeShell q n b φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q b / (q.totient : ℝ)) *
          ∫ u in ((h : ℕ) : ℝ) / c..1, shellAutocorr φ u / u| ≤ δ := by
    apply Filter.eventually_all.mpr
    intro h
    exact eventually_affineRamanujanPrimeShell_uniform hq hφ hsupp hc
      (mem_Ico.mp h.property).1 hδ
  filter_upwards [hevent] with X hX
  intro n
  have heq : affinePrimeShellCorrectionOfShift q n shift φ c X -
      ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift =
      A * ∑ h ∈ S, (affineRamanujanPrimeShell q n (shift h) φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q (shift h) / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u) := by
    simp only [affinePrimeShellCorrectionOfShift, shellCorrectionOfShift, S, A, sum_sub_distrib,
      mul_sub, mul_sum, div_eq_mul_inv, mul_inv_rev]
    congr 1
    exact sum_congr rfl fun h _ => by ring
  rw [heq, abs_mul]
  calc
    _ ≤ |A| * ∑ h ∈ S, |affineRamanujanPrimeShell q n (shift h) φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q (shift h) / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |A| * ∑ _h ∈ S, δ := mul_le_mul_of_nonneg_left
      (sum_le_sum fun h hh => hX ⟨h, hh⟩ n (shift h)) (abs_nonneg _)
    _ ≤ ε := by
      rw [sum_const, nsmul_eq_mul]
      nlinarith only [hδeq, hδ]

private theorem abs_affinePrimeShellCorrectionOfShift_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    (q n : ℕ) (shift : ℕ → ℕ) (c X : ℝ) :
    |affinePrimeShellCorrectionOfShift q n shift φ c X| ≤
      2 * q.totient * (Ico 1 ⌈c⌉₊).card * mertensSum ⌊X⌋₊ := by
  unfold affinePrimeShellCorrectionOfShift
  rw [abs_mul, abs_of_pos (div_pos (by norm_num) hM)]
  calc
    _ ≤ (2 / (∫ u, φ u ^ 2)) * ∑ h ∈ Ico 1 ⌈c⌉₊, |affineRamanujanPrimeShell q n (shift h) φ c h X| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (2 / (∫ u, φ u ^ 2)) * ∑ _h ∈ Ico 1 ⌈c⌉₊,
        (q.totient : ℝ) * (∫ u, φ u ^ 2) * mertensSum ⌊X⌋₊ :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum fun h _ => abs_affineRamanujanPrimeShell_le hφ hsupp q n (shift h) c h X) (by positivity)
    _ = _ := by
      rw [sum_const, nsmul_eq_mul]
      field_simp

private theorem exists_shiftedAffineShellCorrection_error_bound {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) (shift : ℕ → ℕ) :
    ∃ C : ℝ, ∀ X : ℝ, ∀ n : ℕ,
      |affinePrimeShellCorrectionOfShift q n shift φ c X - ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤ C := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_affinePrimeShellCorrectionOfShift_uniform hq hφ hsupp hc shift (by norm_num : (0 : ℝ) < 1))
  let A : ℝ := 2 * q.totient * (Ico 1 ⌈c⌉₊).card
  refine ⟨max 1 (A * mertensSum ⌊T⌋₊ + q.totient * |shellCorrectionOfShift φ c q shift|), ?_⟩
  intro X n
  by_cases hXT : T ≤ X
  · exact (hT X hXT n).trans (le_max_left _ _)
  · have hmert : mertensSum ⌊X⌋₊ ≤ mertensSum ⌊T⌋₊ := by
      unfold mertensSum
      exact sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc le_rfl (Nat.floor_le_floor (le_of_not_ge hXT)))
        (fun k _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
    calc
      _ ≤ |affinePrimeShellCorrectionOfShift q n shift φ c X| +
          |ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| := abs_sub _ _
      _ ≤ A * mertensSum ⌊T⌋₊ + q.totient * |shellCorrectionOfShift φ c q shift| := by
        rw [abs_mul]
        exact add_le_add
          ((abs_affinePrimeShellCorrectionOfShift_le hφ hsupp hM q n shift c X).trans
            (mul_le_mul_of_nonneg_left hmert (by positivity)))
          (mul_le_mul_of_nonneg_right
            (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q n) (abs_nonneg _))
      _ ≤ _ := le_max_right _ _


private theorem exists_uniform_real_tail_majorant (R : ℝ → ℕ → ℝ)
    (hbounded : ∃ C : ℝ, ∀ X n, |R X n| ≤ C)
    (hzero : ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop, ∀ n, |R X n| ≤ ε) :
    ∃ F : ℕ → ℝ, Tendsto F atTop (𝓝 0) ∧
      ∀ (Y : ℕ) (X : ℝ) (n : ℕ), (Y : ℝ) ≤ X → |R X n| ≤ F Y := by
  classical
  obtain ⟨C, hC⟩ := hbounded
  have hC0 : 0 ≤ C := (abs_nonneg (R 0 0)).trans (hC 0 0)
  let F : ℕ → ℝ := fun Y => ⨆ p : ℝ × ℕ, if (Y : ℝ) ≤ p.1 then |R p.1 p.2| else 0
  have hBdd (Y : ℕ) : BddAbove (Set.range fun p : ℝ × ℕ =>
      if (Y : ℝ) ≤ p.1 then |R p.1 p.2| else 0) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨p, rfl⟩
    dsimp only
    split_ifs
    · exact hC p.1 p.2
    · exact hC0
  have hdom (Y : ℕ) (X : ℝ) (n : ℕ) (hYX : (Y : ℝ) ≤ X) : |R X n| ≤ F Y := by
    have h := le_ciSup (hBdd Y) (X, n)
    simpa only [F, if_pos hYX] using h
  have hF0 (Y : ℕ) : 0 ≤ F Y := (abs_nonneg (R Y 0)).trans (hdom Y Y 0 le_rfl)
  refine ⟨F, ?_, hdom⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hzero (ε / 2) (half_pos hε))
  refine ⟨⌈T⌉₊, ?_⟩
  intro Y hY
  have hTY : T ≤ (Y : ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast hY)
  have hsmall : F Y ≤ ε / 2 := by
    apply ciSup_le
    intro p
    by_cases hp : (Y : ℝ) ≤ p.1
    · simp only [if_pos hp]
      exact hT p.1 (hTY.trans hp) p.2
    · simp only [if_neg hp]
      exact (half_pos hε).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hF0 Y)]
  exact hsmall.trans_lt (half_lt_self hε)

/-- The reciprocal weighted source error in one square-root conductor row. -/
def shiftedReciprocalUpwardRowError (φ : ℝ → ℝ) (c : ℝ) (shift : ℕ → ℕ) (N m n : ℕ) : ℝ :=
  (affinePrimeShellCorrectionOfShift m n shift φ c ((N : ℝ) / n) -
    ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m shift) / Real.sqrt n

/-- Uniform affine source convergence upgrades to squared norm on the actual harmonic horizon. -/
theorem tendsto_shiftedReciprocalUpwardRowError_sq_div_log {m : ℕ} (hm : 0 < m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) (shift : ℕ → ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) /
      Real.log N) atTop (𝓝 0) := by
  let R : ℝ → ℕ → ℝ := fun X n => affinePrimeShellCorrectionOfShift m n shift φ c X -
    ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m shift
  obtain ⟨F, hF, hdom⟩ := exists_uniform_real_tail_majorant R
    (exists_shiftedAffineShellCorrection_error_bound hm hφ hsupp hM hc shift)
    (fun ε hε => eventually_affinePrimeShellCorrectionOfShift_uniform hm hφ hsupp hc shift hε)
  apply GaloisForLFunctions.HTGeometry.tendsto_harmonicQuotient_square_error hF
    (fun N n => shiftedReciprocalUpwardRowError φ c shift N m n)
  intro N n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hquot : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := by
    rw [le_div_iff₀ hn0]
    exact_mod_cast Nat.div_mul_le_self N n
  have h := hdom (N / n) ((N : ℝ) / n) n hquot
  rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
  exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg n)

/-- The reciprocal weighted prime-source residual on the normalized conductor vector. -/
def normalizedShiftedReciprocalUpwardResidual (φ : ℝ → ℝ) (c : ℝ) (shift : ℕ → ℕ) (N m : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => shiftedReciprocalUpwardRowError φ c shift N m n / Real.sqrt (Real.log N))

theorem normalizedShiftedReciprocalUpwardResidual_norm_sq (φ : ℝ → ℝ) (c : ℝ) (shift : ℕ → ℕ) (N m : ℕ) :
    ‖normalizedShiftedReciprocalUpwardResidual φ c shift N m‖ ^ 2 =
      (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) / Real.log N := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ n : PrimeHorizonIndex N,
    (shiftedReciprocalUpwardRowError φ c shift N m n / Real.sqrt (Real.log N)) ^ 2) = _
  simp only [div_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← sum_div]
  congr 1
  exact sum_coe_sort (Icc 1 N) (fun n => shiftedReciprocalUpwardRowError φ c shift N m n ^ 2)

theorem tendsto_normalizedShiftedReciprocalUpwardResidual_norm {m : ℕ} (hm : 0 < m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) (shift : ℕ → ℕ) :
    Tendsto (fun N : ℕ => ‖normalizedShiftedReciprocalUpwardResidual φ c shift N m‖) atTop (𝓝 0) := by
  have h := (tendsto_shiftedReciprocalUpwardRowError_sq_div_log hm hφ hsupp hM hc shift).sqrt
  simpa only [← normalizedShiftedReciprocalUpwardResidual_norm_sq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using h

/-- Reflection preserves the signed shell correction. -/
theorem shellCorrectionOfShift_reflected {q : ℕ} (hq : 1 ≤ q) (φ : ℝ → ℝ) (c : ℝ) :
    shellCorrectionOfShift φ c q (reflectedAffineShift q) = shellCorrection φ c q := by
  unfold shellCorrectionOfShift shellCorrection
  congr 1
  exact sum_congr rfl fun h _ => by rw [ramanujanLagCoefficient_reflectedShift hq]

/-- The explicit tilted spline has vanishing shifted reciprocal-source residual. -/
theorem tendsto_tiltedUnitSpline_shiftedReciprocalResidual_norm {m : ℕ} (hm : 0 < m)
    {c : ℝ} (hc : 0 < c) (shift : ℕ → ℕ) :
    Tendsto (fun N : ℕ => ‖normalizedShiftedReciprocalUpwardResidual tiltedUnitSpline c shift N m‖)
      atTop (𝓝 0) :=
  tendsto_normalizedShiftedReciprocalUpwardResidual_norm hm contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc shift

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_normalizedShiftedReciprocalUpwardResidual_norm
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_tiltedUnitSpline_shiftedReciprocalResidual_norm

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ramanujanLagCoefficient_sub_eq_reflected
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.shellCorrectionOfShift_reflected
