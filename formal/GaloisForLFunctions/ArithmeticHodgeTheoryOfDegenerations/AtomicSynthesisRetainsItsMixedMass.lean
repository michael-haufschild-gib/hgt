import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheGammaReserveSurvivesGrowingOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePrimeCrossOfAPrefixAndATopIsADirichletConvolution
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfAHorizonBlock
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingPairsWithStrongPhysicalLimits

/-!
# Mixed mass of normalized atomic synthesis

The tilted-spline mass floor bounds coefficient norm by `O(c⁴)` at unit
physical mass. Poisson summation in each logarithmic-grid row separates
the mixed physical mass into its bulk term and aliasing term, with error
`O(c/N)‖x‖₂`. On a critical overlap schedule, the rescaled mixed mass defect
has the exact weighted aliasing limit along strong physical `L¹` limits.
-/

set_option autoImplicit false
noncomputable section
open Finset Filter Topology MeasureTheory Zeta23
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticDegenerationTheory

/-- The physical normalization preserves the mass floor, with loss exactly `c⁸`. -/
theorem normalized_tilted_synthesis_mass_ge {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N)
    (x : ℕ → ℝ) :
    growingMassConstant * (∫ u, tiltedUnitSpline u ^ 2) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      c ^ 8 * ∫ u, normalizedCentredAtomicTest tiltedUnitSpline x c N u ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hmass := integral_atomicTest_sq_ge_growing hc hN x
  have hn : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN0.le
  have hnorm : (∫ u, normalizedCentredAtomicTest tiltedUnitSpline x c N u ^ 2) =
      (N : ℝ) / c ^ 2 * ∫ u, atomicTest N x (atomDilate tiltedUnitSpline (c / N)) u ^ 2 := by
    simp only [normalizedCentredAtomicTest, centredAtomicTest, mul_pow]
    rw [integral_const_mul,
      integral_add_right_eq_self
        (fun u => atomicTest N x (atomDilate tiltedUnitSpline (c / N)) u ^ 2)
        (Real.log N), div_pow, hn]
  rw [hnorm]
  have h := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ (N : ℝ) * c ^ 6)
  have hl : (N : ℝ) * c ^ 6 *
      (growingMassConstant / c ^ 7 * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        ∑ n ∈ Icc 1 N, x n ^ 2) =
      growingMassConstant * (∫ u, tiltedUnitSpline u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
    field_simp
  have hr : (N : ℝ) * c ^ 6 *
      (∫ u, atomicTest N x (atomDilate tiltedUnitSpline (c / N)) u ^ 2) =
      c ^ 8 * ((N : ℝ) / c ^ 2 *
        ∫ u, atomicTest N x (atomDilate tiltedUnitSpline (c / N)) u ^ 2) := by
    field_simp
  rw [hl, hr] at h
  exact h

/-- Unit physical mass bounds the Euclidean coefficient norm by a fourth power of overlap. -/
theorem exists_normalized_tilted_synthesis_coefficient_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, ∀ x : ℕ → ℝ,
      (∫ u, normalizedCentredAtomicTest tiltedUnitSpline x c N u ^ 2) ≤ 1 →
      Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2) ≤ B * c ^ 4 := by
  let d := growingMassConstant * ∫ u, tiltedUnitSpline u ^ 2
  have hd : 0 < d := mul_pos growingMassConstant_pos integral_tiltedUnitSpline_sq_pos
  refine ⟨(Real.sqrt d)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hd), ?_⟩
  intro c hc N x hmass
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  by_cases hN : N = 0
  · subst N
    simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty, Real.sqrt_zero]
    positivity
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hf := normalized_tilted_synthesis_mass_ge hc hN1 x
  have hb : d * (∑ n ∈ Icc 1 N, x n ^ 2) ≤ c ^ 8 :=
    hf.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass (pow_nonneg hc0.le 8))
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt hS, mul_pow, inv_pow, Real.sq_sqrt hd.le]
  have hb' := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hb)
  convert hb' using 1; ring

/-- The physical cross mass is the logarithmic-grid autocorrelation matrix. -/
theorem integral_normalized_synthesis_mul_horizon {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hs : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (∫ u, normalizedCentredAtomicTest φ x c N u *
      normalizedCentredAtomicTest φ (horizonWeights h N) c N u) =
      1 / c * ∑ n ∈ Icc 1 N, x n * ∑ m ∈ Icc 1 N, horizonWeights h N m *
        shellAutocorr φ (N * (Real.log m - Real.log n) / c) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨hg, hgs, hgc⟩ := RenormalizedArithmeticPotentialTheory.atomDilate_facts hφ hs hw
  have hi : (∫ u, normalizedCentredAtomicTest φ x c N u *
      normalizedCentredAtomicTest φ (horizonWeights h N) c N u) =
      (Real.sqrt N / c) ^ 2 * ∫ u,
        atomicTest N (horizonWeights h N) (atomDilate φ (c / N)) (u + Real.log N) *
        atomicTest N x (atomDilate φ (c / N)) (u + Real.log N) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    simp only [normalizedCentredAtomicTest, centredAtomicTest]
    ring
  rw [hi, integral_add_right_eq_self
    (fun u => atomicTest N (horizonWeights h N) (atomDilate φ (c / N)) u *
      atomicTest N x (atomDilate φ (c / N)) u) (Real.log N),
    div_pow, Real.sq_sqrt hN0.le,
    integral_atomicTest_mul_atomicTest hg.continuous hgc, Finset.sum_comm]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro m hm
  rw [bumpCorr_atomDilate_eq' hw]
  have he : (Real.log m - Real.log n) / (c / N) =
      N * (Real.log m - Real.log n) / c := by field_simp
  rw [he]
  field_simp

private theorem horizonWeights_mul_ratio (h : ℝ → ℝ) {N n : ℕ}
    (hN : 1 ≤ N) (hn : 1 ≤ n) :
    horizonWeights h N n * ((n : ℝ) / N) =
      halfWeight h (Real.log n - Real.log N) / Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp ((Real.log n - Real.log N) / 2) = Real.sqrt n / Real.sqrt N := by
    rw [sub_div, Real.exp_sub, Real.exp_half, Real.exp_half,
      Real.exp_log hn0, Real.exp_log hN0]
  rw [horizonWeights, halfWeight, he]
  have hsn := Real.sq_sqrt hn0.le
  have hsN := Real.sq_sqrt hN0.le
  field_simp
  linear_combination (h (Real.log n - Real.log N) * (n : ℝ)) * hsN -
    (h (Real.log n - Real.log N) * (N : ℝ)) * hsn

/-- A smooth recovery vector detects the bulk mass and the discrete aliasing of every
coefficient vector, with error controlled by its Euclidean norm. -/
theorem abs_normalized_synthesis_mixed_mass_sub_le {φ h : ℝ → ℝ} {A : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N → ∀ x : ℕ → ℝ,
      |(∫ u, normalizedCentredAtomicTest φ x c N u *
          normalizedCentredAtomicTest φ (horizonWeights h N) c N u) -
        1 / Real.sqrt N * ∑ n ∈ Icc 1 N, x n * halfWeight h (Real.log n - Real.log N) *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N))| ≤
        C * c / N * Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2) := by
  obtain ⟨Bk, Lk, hk, hkL⟩ := exists_bound_lipschitz (contDiff_taperedProfile hh)
    (A := A) fun y hy => taperedProfile_eq_zero hsupp hy
  have hG2 := contDiff_shellAutocorr hφ hφsupp
  have hG1 : ∀ t, 1 ≤ |t| → shellAutocorr φ t = 0 := fun t ht =>
    shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ht
  have hGc : HasCompactSupport (shellAutocorr φ) :=
    HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun t ht => by
      refine hG1 t ?_
      by_contra hlt
      exact ht (abs_le.mp (not_le.mp hlt).le)
  obtain ⟨BG, hBG⟩ := hGc.exists_bound_of_continuous hG2.continuous
  obtain ⟨LG, hLG⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGc hG2 (by norm_num)
  have hGb : ∀ t, |shellAutocorr φ t| ≤ |BG| := fun t =>
    (by simpa [Real.norm_eq_abs] using hBG t : |shellAutocorr φ t| ≤ BG).trans (le_abs_self _)
  have hGL : ∀ s t, |shellAutocorr φ s - shellAutocorr φ t| ≤ (LG : ℝ) * |s - t| := fun s t => by
    simpa [Real.dist_eq] using hLG.dist_le_mul s t
  have hkb : ∀ y, |taperedProfile h y| ≤ |Bk| := fun y => (hk y).trans (le_abs_self _)
  have hkL' : ∀ u v, |taperedProfile h u - taperedProfile h v| ≤ |Lk| * |u - v| := fun u v =>
    (hkL u v).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _))
  have hk0 : ∀ y, 0 < y → taperedProfile h y = 0 := fun y hy =>
    taperedProfile_eq_zero hsupp fun hm => by linarith only [hm.2, hy]
  let C := 5 * (|Lk| * |BG| + 8 * |Bk| * (LG : ℝ))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro c hc N hcN x
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by linarith only [hcN, hc]
  have hN : 1 ≤ N := by exact_mod_cast hN0
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  let row (n : ℕ) := ∑ m ∈ Icc 1 N, horizonWeights h N m *
    shellAutocorr φ (N * (Real.log m - Real.log n) / c)
  let main (n : ℕ) := horizonWeights h N n * (c * n / N) *
    ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N))
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) : |row n - main n| ≤ C * c ^ 2 / (N * Real.sqrt N) := by
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN := (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hr := abs_row_sub_le hkb hkL' hGb hGL hG1 hk0 (abs_nonneg _) (abs_nonneg _)
      (NNReal.coe_nonneg _) (abs_nonneg _) hc hcN hn1 hnN
    rw [tsum_shellAutocorr_eq hφ hφsupp (by positivity : 0 < c * n / N)] at hr
    have hw : row n = ∑ m ∈ Icc 1 N,
        taperedProfile h (Real.log m - Real.log N) / Real.sqrt N *
          shellAutocorr φ (N * (Real.log m - Real.log n) / c) := by
      apply sum_congr rfl
      intro m hm
      rw [horizonWeights_eq_tapered h hN (Finset.mem_Icc.mp hm).1]
    rw [hw]
    dsimp only [main]
    rw [horizonWeights_eq_tapered h hN hn1]
    simpa only [C, mul_assoc] using hr
  have hmain : 1 / c * ∑ n ∈ Icc 1 N, x n * main n =
      1 / Real.sqrt N * ∑ n ∈ Icc 1 N, x n * halfWeight h (Real.log n - Real.log N) *
        ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N)) := by
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro n hn
    have hh := horizonWeights_mul_ratio h hN (Finset.mem_Icc.mp hn).1
    dsimp only [main]
    calc
      _ = x n * (horizonWeights h N n * ((n : ℝ) / N)) *
          ((∫ u, φ u) ^ 2 + 2 * aliasDensity φ (c * n / N)) := by field_simp
      _ = _ := by rw [hh]; ring
  have hsum : ∑ n ∈ Icc 1 N, |x n| ≤
      Real.sqrt N * Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2) := by
    have h := sum_mul_sq_le_sq_mul_sq (Icc 1 N) (fun _ => (1 : ℝ)) (fun n => |x n|)
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs,
      Nat.card_Icc, Nat.add_sub_cancel] at h
    have hs := Real.sqrt_le_sqrt h
    rw [Real.sqrt_sq (sum_nonneg fun _ _ => abs_nonneg _),
      Real.sqrt_mul (Nat.cast_nonneg N)] at hs
    exact hs
  rw [integral_normalized_synthesis_mul_horizon hφ hφsupp h hc0 hN, ← hmain,
    ← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr hc0)]
  change 1 / c * |(∑ n ∈ Icc 1 N, x n * row n) - ∑ n ∈ Icc 1 N, x n * main n| ≤ _
  rw [← sum_sub_distrib]
  have herr : |∑ n ∈ Icc 1 N, (x n * row n - x n * main n)| ≤
      (Real.sqrt N * Real.sqrt (∑ n ∈ Icc 1 N, x n ^ 2)) *
        (C * c ^ 2 / (N * Real.sqrt N)) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, |x n * row n - x n * main n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, |x n| * (C * c ^ 2 / (N * Real.sqrt N)) := by
        apply sum_le_sum
        intro n hn
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (hrow n hn) (abs_nonneg _)
      _ = (∑ n ∈ Icc 1 N, |x n|) * (C * c ^ 2 / (N * Real.sqrt N)) := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by positivity)
  refine (mul_le_mul_of_nonneg_left herr (one_div_nonneg.mpr hc0.le)).trans_eq ?_
  field_simp

/-- Unit physical mass supplies the coefficient control required by discrete aliasing. -/
theorem tendsto_criticalCurve_aliasing_pair_of_unit_physical_mass_along_filter
    {l : Filter ℕ} (hl : l ≤ atTop)
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F g : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hs : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {Lg : NNReal} (hg : LipschitzWith Lg g) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
        (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))) l
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * g y) * Real.exp (-(8 * y)))) := by
  obtain ⟨B, hB, hb⟩ := exists_normalized_tilted_synthesis_coefficient_bound
  exact tendsto_criticalCurve_aliasing_pair_of_polynomial_norm_bound_along_filter hl hc1 hR hcrit
    (m := 4) (fun N => hb (c N) (hc1 N) N (x N) (hmass N)) hF hL1 hA hs hg hBg

/-- Unit physical mass supplies the full-sequence aliasing pairing. -/
theorem tendsto_criticalCurve_aliasing_pair_of_unit_physical_mass
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F g : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hs : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {Lg : NNReal} (hg : LipschitzWith Lg g) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      ∑ n ∈ Icc 1 N, x N n * g (Real.log n - Real.log N) *
        (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))) atTop
      (𝓝 ((7 / 2 : ℝ) * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * g y) * Real.exp (-(8 * y)))) := by
  exact tendsto_criticalCurve_aliasing_pair_of_unit_physical_mass_along_filter le_rfl
    hc1 hR hcrit hmass hF hL1 hA hs hg hBg

/-- Against a smooth recovery vector, the rescaled physical mass defect converges to
its sharp weighted aliasing pairing. -/
theorem tendsto_criticalCurve_mixed_mass_defect_along_filter
    {l : Filter ℕ} (hl : l ≤ atTop)
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F h : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) l (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hh : ContDiff ℝ 2 h)
    (hs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) * c N ^ 8 *
      ((∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u *
        normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N u) -
       (∫ u, tiltedUnitSpline u) * ∫ u,
         normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u * halfWeight h u))
      l (𝓝 (7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * halfWeight h y) * Real.exp (-(8 * y)))) := by
  let m := ∫ u, tiltedUnitSpline u
  let U := fun N => normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N
  let V := fun N => normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N
  let S := fun N : ℕ => 1 / Real.sqrt N *
    ∑ n ∈ Icc 1 N, x N n * halfWeight h (Real.log n - Real.log N)
  let P := fun N : ℕ => m / Real.sqrt N *
    ∑ n ∈ Icc 1 N, x N n * halfWeight h (Real.log n - Real.log N) *
      (c N ^ 8 * aliasDensity tiltedUnitSpline (c N * n / N))
  let Q := fun N : ℕ => 1 / Real.sqrt N *
    ∑ n ∈ Icc 1 N, x N n * halfWeight h (Real.log n - Real.log N) *
      (m ^ 2 + 2 * aliasDensity tiltedUnitSpline (c N * n / N))
  have hH := contDiff_halfWeight hh
  have hHc := hasCompactSupport_halfWeight (hasCompactSupport_of_window hs)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hHc hH (by norm_num)
  obtain ⟨D, hD⟩ := hHc.exists_bound_of_continuous hH.continuous
  have hDs : ∀ y, |halfWeight h y| ≤ D := fun y => by simpa only [Real.norm_eq_abs] using hD y
  have hHs : ∀ y, y ∉ Set.Icc (-A) 0 → halfWeight h y = 0 :=
    fun y hy => by simp only [halfWeight, hs y hy, mul_zero]
  have hPlim := tendsto_criticalCurve_aliasing_pair_of_unit_physical_mass_along_filter
    hl hc1 hR hcrit hmass hF hL1 hA hHs hL hDs
  obtain ⟨B, hB, hcoef⟩ := exists_normalized_tilted_synthesis_coefficient_bound
  have hcoef' (N : ℕ) := hcoef (c N) (hc1 N) N (x N) (hmass N)
  have hpow (k : ℕ) : Tendsto (fun N : ℕ => c N ^ k / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hR hcrit k 0
  have hsmall : ∀ᶠ N : ℕ in atTop, 4 * c N ≤ N := by
    filter_upwards [(hpow 1).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      eventually_ge_atTop 1] with N hn hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [pow_one] at hn
    have hn' := (div_le_iff₀ hN0).mp hn
    linarith only [hn']
  obtain ⟨C, hC, hrow⟩ := abs_normalized_synthesis_mixed_mass_sub_le
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hh hs
  have hrowlim : Tendsto (fun N => c N ^ 8 * ((∫ u, U N u * V N u) - Q N)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa only [mul_zero] using (hpow 13).const_mul (C * B))
    filter_upwards [hsmall] with N hn
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc1 N)
    have hb := hrow (c N) (hc1 N) N hn (x N)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0.le 8)]
    have he := mul_le_mul_of_nonneg_left hb (pow_nonneg hc0.le 8)
    refine he.trans ?_
    calc
      _ = (C * c N ^ 9 / N) * Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2) := by ring
      _ ≤ (C * c N ^ 9 / N) * (B * c N ^ 4) :=
        mul_le_mul_of_nonneg_left (hcoef' N) (by positivity)
      _ = _ := by ring
  have hadjlim : Tendsto (fun N => c N ^ 8 * ((∫ u, U N u * halfWeight h u) - m * S N))
      atTop (𝓝 0) := by
    have hdec := (hpow 13).const_mul ((L : ℝ) * (∫ u, |tiltedUnitSpline u|) * B)
    simp only [mul_zero] at hdec
    refine squeeze_zero_norm' ?_ hdec
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc1 N)
    have hb := abs_integral_normalizedCentredAtomicTest_mul_sub_le
      contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_eq_zero hL hc0 hN (x N)
    have hsN : m * S N = m / Real.sqrt N *
        ∑ n ∈ Icc 1 N, x N n * halfWeight h (Real.log n - Real.log N) := by dsimp only [S]; ring
    rw [hsN, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0.le 8)]
    have he := mul_le_mul_of_nonneg_left hb (pow_nonneg hc0.le 8)
    refine he.trans ?_
    calc
      _ = ((L : ℝ) * (∫ u, |tiltedUnitSpline u|) * c N ^ 9 / N) *
          Real.sqrt (∑ n ∈ Icc 1 N, x N n ^ 2) := by ring
      _ ≤ ((L : ℝ) * (∫ u, |tiltedUnitSpline u|) * c N ^ 9 / N) * (B * c N ^ 4) :=
        mul_le_mul_of_nonneg_left (hcoef' N) (by positivity)
      _ = _ := by ring
  have hid (N : ℕ) :
      m * c N ^ 8 * ((∫ u, U N u * V N u) - m * ∫ u, U N u * halfWeight h u) =
      m * (c N ^ 8 * ((∫ u, U N u * V N u) - Q N)) -
        m ^ 2 * (c N ^ 8 * ((∫ u, U N u * halfWeight h u) - m * S N)) + 2 * P N := by
    have hQ : m * c N ^ 8 * Q N = m ^ 3 * c N ^ 8 * S N + 2 * P N := by
      dsimp only [Q, S, P]
      simp only [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro n hn
      ring
    linear_combination hQ
  have hlim := (((hrowlim.mono_left hl).const_mul m).sub
    ((hadjlim.mono_left hl).const_mul (m ^ 2))).add (hPlim.const_mul 2)
  have hlim' := hlim.congr fun N => (hid N).symm
  convert hlim' using 1; ring

/-- The mixed physical mass defect along the full horizon sequence. -/
theorem tendsto_criticalCurve_mixed_mass_defect
    {x : ℕ → ℕ → ℝ} {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (hmass : ∀ N, (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u ^ 2) ≤ 1)
    {F h : ℝ → ℝ} (hF : Integrable F)
    (hL1 : Tendsto (fun N => ∫ y,
      ‖normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N y - F y‖) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hh : ContDiff ℝ 2 h)
    (hs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    Tendsto (fun N : ℕ => (∫ u, tiltedUnitSpline u) * c N ^ 8 *
      ((∫ u, normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u *
        normalizedCentredAtomicTest tiltedUnitSpline (horizonWeights h N) (c N) N u) -
       (∫ u, tiltedUnitSpline u) * ∫ u,
         normalizedCentredAtomicTest tiltedUnitSpline (x N) (c N) N u * halfWeight h u))
      atTop (𝓝 (7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, (F y * halfWeight h y) * Real.exp (-(8 * y)))) := by
  exact tendsto_criticalCurve_mixed_mass_defect_along_filter le_rfl
    hc1 hR hcrit hmass hF hL1 hA hh hs

#print axioms tendsto_criticalCurve_mixed_mass_defect
#print axioms tendsto_criticalCurve_aliasing_pair_of_unit_physical_mass
#print axioms normalized_tilted_synthesis_mass_ge
#print axioms abs_normalized_synthesis_mixed_mass_sub_le

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
