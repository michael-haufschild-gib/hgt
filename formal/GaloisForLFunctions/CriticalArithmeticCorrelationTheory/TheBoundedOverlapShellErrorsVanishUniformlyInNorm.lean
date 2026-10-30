import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheWeightedPrimeShellsAreUniformOnBoundedOverlap

/-!
# Bounded-overlap shell errors vanish uniformly in harmonic norm

The literal signed affine shell error has a common source horizon for every bounded overlap and
shift family. A finite-source Mertens bound controls the remaining initial interval. Its real tail
supremum therefore tends to zero uniformly, and the harmonic quotient estimate converts this
common majorant into the normalized reciprocal-source norm law.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-- A bounded number of shells has a common finite-source Mertens bound, independently of all
shift choices and of the mode index. -/
theorem abs_affinePrimeShellCorrectionOfShift_le_boundedOverlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (q n : ℕ) (shift : ℕ → ℕ) {c K : ℝ} (hcK : c ≤ K) (X : ℝ) :
    |affinePrimeShellCorrectionOfShift q n shift φ c X| ≤
      2 * q.totient * ⌈K⌉₊ * mertensSum ⌊X⌋₊ := by
  have hG (s : ℝ) : |shellAutocorr φ s| ≤ ∫ u, φ u ^ 2 :=
    abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) s
  have hmert : 0 ≤ mertensSum ⌊X⌋₊ := by
    unfold mertensSum
    exact sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hsingle (h : ℕ) : |affineRamanujanPrimeShell q n (shift h) φ c h X| ≤
      (q.totient : ℝ) * (∫ u, φ u ^ 2) * mertensSum ⌊X⌋₊ := by
    unfold affineRamanujanPrimeShell
    calc
      _ ≤ ∑ k ∈ Icc 1 ⌊X⌋₊, |(ArithmeticFunction.vonMangoldt k : ℝ) / k *
          ramanujanLagCoefficient q (k * n + shift h) * shellAutocorr φ ((h : ℝ) * X / (c * k))| :=
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
            (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q (k * n + shift h)) hΛ)
          (hG _) (abs_nonneg _) (mul_nonneg hΛ (Nat.cast_nonneg _))
      _ = _ := by
        rw [mertensSum, mul_sum]
        exact sum_congr rfl fun k _ => by ring
  have hcard : ((Ico 1 ⌈c⌉₊).card : ℝ) ≤ ⌈K⌉₊ := by
    have hceil := Nat.ceil_mono hcK
    have hnat : (Ico 1 ⌈c⌉₊).card ≤ ⌈K⌉₊ := by rw [Nat.card_Ico]; omega
    exact_mod_cast hnat
  unfold affinePrimeShellCorrectionOfShift
  rw [abs_mul, abs_of_pos (div_pos zero_lt_two hM)]
  calc
    _ ≤ (2 / (∫ u, φ u ^ 2)) * ∑ h ∈ Ico 1 ⌈c⌉₊,
        |affineRamanujanPrimeShell q n (shift h) φ c h X| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (div_nonneg zero_le_two hM.le)
    _ ≤ (2 / (∫ u, φ u ^ 2)) * ∑ _h ∈ Ico 1 ⌈c⌉₊,
        (q.totient : ℝ) * (∫ u, φ u ^ 2) * mertensSum ⌊X⌋₊ :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun h _ => hsingle h) (div_nonneg zero_le_two hM.le)
    _ = 2 * q.totient * (Ico 1 ⌈c⌉₊).card * mertensSum ⌊X⌋₊ := by
      rw [sum_const, nsmul_eq_mul]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (by positivity)) hmert

private theorem exists_affineShellCorrection_uniform_error_bound {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 0 < K) :
    ∃ C : ℝ, ∀ X c : ℝ, 1 ≤ c → c ≤ K → ∀ shift : ℕ → ℕ, ∀ n : ℕ,
      |affinePrimeShellCorrectionOfShift q n shift φ c X -
        ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤ C := by
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (eventually_affinePrimeShellCorrectionOfShift_uniform_overlap hq hφ hsupp hK
      (by norm_num : (0 : ℝ) < 1))
  let Z := max 1 Y
  let A := 2 * (q.totient : ℝ) * ⌈K⌉₊ * mertensSum ⌊Z⌋₊
  have hmert : 0 ≤ mertensSum ⌊Z⌋₊ := by
    unfold mertensSum
    exact sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hYZ : Y ≤ Z := le_max_right _ _
  refine ⟨2 * A + 1, ?_⟩
  intro X c hc1 hcK shift n
  by_cases hZX : Z ≤ X
  · exact (hY X (hYZ.trans hZX) c hc1 hcK shift n).trans (by linarith only [hA])
  · have hsource (U : ℝ) (hUZ : U ≤ Z) :
        |affinePrimeShellCorrectionOfShift q n shift φ c U| ≤ A := by
      have hmon : mertensSum ⌊U⌋₊ ≤ mertensSum ⌊Z⌋₊ := by
        unfold mertensSum
        exact sum_le_sum_of_subset_of_nonneg
          (Icc_subset_Icc le_rfl (Nat.floor_le_floor hUZ))
          (fun k _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
      exact (abs_affinePrimeShellCorrectionOfShift_le_boundedOverlap hφ hsupp hM q n shift hcK U).trans
        (mul_le_mul_of_nonneg_left hmon (by positivity))
    have hmean : |ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤ A + 1 := by
      calc
        _ = |affinePrimeShellCorrectionOfShift q n shift φ c Z -
            (affinePrimeShellCorrectionOfShift q n shift φ c Z -
              ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift)| := by congr 1; ring
        _ ≤ |affinePrimeShellCorrectionOfShift q n shift φ c Z| +
            |affinePrimeShellCorrectionOfShift q n shift φ c Z -
              ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| := abs_sub _ _
        _ ≤ A + 1 := add_le_add (hsource Z le_rfl) (hY Z hYZ c hc1 hcK shift n)
    calc
      _ ≤ |affinePrimeShellCorrectionOfShift q n shift φ c X| +
          |ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| := abs_sub _ _
      _ ≤ A + (A + 1) := add_le_add (hsource X (le_of_not_ge hZX)) hmean
      _ = 2 * A + 1 := by ring

private theorem exists_uniform_real_tail_majorant_index {ι : Type*} [Nonempty ι]
    (R : ℝ → ι → ℝ) (hbounded : ∃ C : ℝ, ∀ X i, |R X i| ≤ C)
    (hzero : ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop, ∀ i, |R X i| ≤ ε) :
    ∃ F : ℕ → ℝ, Tendsto F atTop (𝓝 0) ∧ (∀ Y, 0 ≤ F Y) ∧
      ∀ (Y : ℕ) (X : ℝ) (i : ι), (Y : ℝ) ≤ X → |R X i| ≤ F Y := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨C, hC⟩ := hbounded
  have hC0 : 0 ≤ C := (abs_nonneg (R 0 i₀)).trans (hC 0 i₀)
  let F : ℕ → ℝ := fun Y => ⨆ p : ℝ × ι, if (Y : ℝ) ≤ p.1 then |R p.1 p.2| else 0
  have hBdd (Y : ℕ) : BddAbove (Set.range fun p : ℝ × ι =>
      if (Y : ℝ) ≤ p.1 then |R p.1 p.2| else 0) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨p, rfl⟩
    dsimp only
    split_ifs
    · exact hC p.1 p.2
    · exact hC0
  have hdom (Y : ℕ) (X : ℝ) (i : ι) (hYX : (Y : ℝ) ≤ X) : |R X i| ≤ F Y := by
    have h := le_ciSup (hBdd Y) (X, i)
    simpa only [F, if_pos hYX] using h
  have hF0 (Y : ℕ) : 0 ≤ F Y := (abs_nonneg (R Y i₀)).trans (hdom Y Y i₀ le_rfl)
  refine ⟨F, ?_, hF0, hdom⟩
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

/-- A single harmonic majorant controls every overlap in the interval and every shifted shell
family, so the squared source norm tends uniformly to zero. -/
theorem eventually_shiftedReciprocalUpwardRowError_sq_uniform_overlap {m : ℕ} (hm : 0 < m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ shift : ℕ → ℕ,
      (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) / Real.log N ≤ ε := by
  let ι := {c : ℝ // 1 ≤ c ∧ c ≤ K} × ((ℕ → ℕ) × ℕ)
  haveI : Nonempty ι := ⟨(⟨1, le_rfl, hK⟩, (id, 0))⟩
  let R : ℝ → ι → ℝ := fun X p => affinePrimeShellCorrectionOfShift m p.2.2 p.2.1 φ p.1 X -
    ramanujanLagCoefficient m p.2.2 * shellCorrectionOfShift φ p.1 m p.2.1
  have hbounded : ∃ C : ℝ, ∀ X i, |R X i| ≤ C := by
    obtain ⟨C, hC⟩ := exists_affineShellCorrection_uniform_error_bound hm hφ hsupp hM
      (zero_lt_one.trans_le hK)
    exact ⟨C, fun X p => hC X p.1 p.1.property.1 p.1.property.2 p.2.1 p.2.2⟩
  have hzero : ∀ η : ℝ, 0 < η → ∀ᶠ X : ℝ in atTop, ∀ i, |R X i| ≤ η := by
    intro η hη
    filter_upwards [eventually_affinePrimeShellCorrectionOfShift_uniform_overlap hm hφ hsupp
      (zero_lt_one.trans_le hK) hη] with X hX
    intro p
    exact hX p.1 p.1.property.1 p.1.property.2 p.2.1 p.2.2
  obtain ⟨F, hF, hF0, hdom⟩ := exists_uniform_real_tail_majorant_index R hbounded hzero
  let B : ℕ → ℕ → ℝ := fun N n => F (N / n) / Real.sqrt n
  have hlim := GaloisForLFunctions.HTGeometry.tendsto_harmonicQuotient_square_error hF B
    (fun N n _ => by
      dsimp only [B]
      rw [abs_div, abs_of_nonneg (hF0 _), abs_of_nonneg (Real.sqrt_nonneg n)])
  filter_upwards [hlim.eventually (ge_mem_nhds hε)] with N hN
  intro c hc1 hcK shift
  have hsum : (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) ≤
      ∑ n ∈ Icc 1 N, B N n ^ 2 := by
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hquot : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := by
      rw [le_div_iff₀ hn0]
      exact_mod_cast Nat.div_mul_le_self N n
    have hrow : |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ B N n := by
      have h := hdom (N / n) ((N : ℝ) / n) (⟨c, hc1, hcK⟩, (shift, n)) hquot
      rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
      exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg n)
    have h := mul_self_le_mul_self (abs_nonneg _) hrow
    simpa only [← sq, sq_abs] using h
  exact (div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)).trans hN

/-- The normalized reciprocal-source residual vanishes uniformly over bounded overlap and
arbitrary shell shifts. -/
theorem eventually_normalizedShiftedReciprocalUpwardResidual_norm_uniform_overlap {m : ℕ} (hm : 0 < m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ shift : ℕ → ℕ,
      ‖normalizedShiftedReciprocalUpwardResidual φ c shift N m‖ ≤ ε := by
  filter_upwards [eventually_shiftedReciprocalUpwardRowError_sq_uniform_overlap hm hφ hsupp hM hK
    (sq_pos_of_pos hε)] with N hN
  intro c hc1 hcK shift
  have h := hN c hc1 hcK shift
  rw [← normalizedShiftedReciprocalUpwardResidual_norm_sq] at h
  nlinarith only [h, hε, norm_nonneg (normalizedShiftedReciprocalUpwardResidual φ c shift N m)]

/-- The explicit tilted spline satisfies the common-horizon norm law without a profile premise. -/
theorem eventually_tiltedUnitSpline_shiftedReciprocalResidual_norm_uniform_overlap {m : ℕ} (hm : 0 < m)
    {K : ℝ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ shift : ℕ → ℕ,
      ‖normalizedShiftedReciprocalUpwardResidual tiltedUnitSpline c shift N m‖ ≤ ε :=
  eventually_normalizedShiftedReciprocalUpwardResidual_norm_uniform_overlap hm
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hK hε

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_shiftedReciprocalUpwardRowError_sq_uniform_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_normalizedShiftedReciprocalUpwardResidual_norm_uniform_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_shiftedReciprocalResidual_norm_uniform_overlap
