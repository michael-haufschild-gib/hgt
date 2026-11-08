import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarGammaMeansHaveOneLimit
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalStripsVanishAtCriticalScale

/-!
# Fixed polar far annuli converge in square mean

A fixed logarithmic annulus has a bounded row, including terminal rows. Its
interior lattice error vanishes after division by the atom width, while its
terminal strip has vanishing normalized cardinality.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The actual separated polar row on a fixed logarithmic annulus, divided by atom width. -/
def polarFarAnnulusRow (T c : ℝ) (N n : ℕ) : ℝ :=
  (∑ j ∈ logarithmicBallIndices (T * (c / N)) N n \ logarithmicBallIndices (2 * (c / N)) N n,
    atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j /
      (Real.sqrt n * Real.sqrt j)) / (c / N)

/-- Fixed-annulus curvature and lattice errors vanish at the interior row scale. -/
theorem exists_polarFarAnnulusRow_interior_bound {T : ℝ} (hT : 2 ≤ T) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ {c : ℝ} {N n : ℕ}, 0 < c →
      T * (c / N) ≤ 1 / 2 → n ∈ Icc 1 N →
      (n : ℝ) * Real.exp (T * (c / N)) ≤ N →
      |polarFarAnnulusRow T c N n - polarFarMean T (c / N)| ≤
        C * ((N : ℝ) / n) / c + D * (c / N) := by
  obtain ⟨C, hC, hb⟩ := exists_polarFar_annulus_mean_bound
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let D : ℝ := 2 * Real.exp 3 *
    (5 / 2 * (∫ t, |bumpAutocorr tiltedUnitSpline t|) / (∫ u, tiltedUnitSpline u ^ 2)) * T
  have hD : 0 ≤ D := by
    have hT0 : 0 ≤ T := by linarith only [hT]
    dsimp only [D]
    positivity
  have hT0 : 0 ≤ T := by linarith only [hT]
  refine ⟨(32 * T + 98) * C, D, by positivity, hD, ?_⟩
  intro c N n hc hw hn hint
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hw0 : 0 < c / N := div_pos hc hN0
  let S := logarithmicBallIndices (T * (c / N)) N n \ logarithmicBallIndices (2 * (c / N)) N n
  let A : ℝ := ∑ j ∈ S, atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j /
    (Real.sqrt n * Real.sqrt j)
  let B : ℝ := ∑ j ∈ S, crossSingular tiltedUnitSpline ((c / N) / |Real.log j - Real.log n|) /
    (Real.sqrt n * Real.sqrt j)
  have hcurv : |A - B| ≤ D * (c / N) ^ 2 := by
    have hh := abs_polarFar_actual_sub_singular_row_le
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      hT hw0 (hw.trans (by norm_num)) hn
    have he : A - B = ∑ j ∈ S,
        (atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j -
          crossSingular tiltedUnitSpline ((c / N) / |Real.log j - Real.log n|)) /
            (Real.sqrt n * Real.sqrt j) := by
      dsimp only [A, B]
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by ring
    rw [he]
    exact hh
  have hmean : |B - (c / N) * polarFarMean T (c / N)| ≤ (32 * T + 98) * C / n := by
    have hh := hb hT hw0 hw hn hint
    have he :
        (∫ t in (-T)..T, polarFarClampedKernel tiltedUnitSpline t * ((c / N) * Real.exp ((c / N) * t / 2))) -
        (∫ t in (-2 : ℝ)..2, polarFarClampedKernel tiltedUnitSpline t * ((c / N) * Real.exp ((c / N) * t / 2))) =
        (c / N) * polarFarMean T (c / N) := by
      unfold polarFarMean
      rw [mul_sub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      congr 1 <;> apply intervalIntegral.integral_congr <;> intro t _ <;> ring
    rw [he] at hh
    exact hh
  have hh := (abs_sub_le A B ((c / N) * polarFarMean T (c / N))).trans
    (add_le_add hcurv hmean)
  have hh' := div_le_div_of_nonneg_right hh hw0.le
  have he : |A - (c / N) * polarFarMean T (c / N)| / (c / N) =
      |polarFarAnnulusRow T c N n - polarFarMean T (c / N)| := by
    conv_lhs => arg 2; rw [← abs_of_pos hw0]
    rw [← abs_div]
    congr 1
    change (A - (c / N) * polarFarMean T (c / N)) / (c / N) = A / (c / N) - _
    field_simp [hw0.ne']
  rw [he] at hh'
  exact hh'.trans_eq (by field_simp [hc.ne', hN0.ne', hn0.ne']; ring)

/-- The normalized annulus row is bounded uniformly up to the terminal boundary. -/
theorem exists_polarFarAnnulusRow_global_bound {T : ℝ} (hT : 2 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {c : ℝ} {N n : ℕ}, 0 < c → T * (c / N) ≤ 1 / 2 →
      n ∈ Icc 1 N → |polarFarAnnulusRow T c N n - polarFarMean T (c / N)| ≤ K := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hI := integral_tiltedUnitSpline_sq_pos
  obtain ⟨A, hA, hbound, _⟩ := exists_crossSingular_inverse_bounds hφ hsupp hI
  obtain ⟨C, hC, hmean⟩ := exists_abs_polarFarMean_sub_zero_le hT
  let D : ℝ := 2 * Real.exp 3 *
    (5 / 2 * (∫ t, |bumpAutocorr tiltedUnitSpline t|) / (∫ u, tiltedUnitSpline u ^ 2)) * T
  have hT0 : 0 < T := by linarith only [hT]
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D + 2 * Real.exp 3 * T * A + |polarFarMean T 0| + C, by positivity, ?_⟩
  intro c N n hc hw hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hw0 : 0 < c / N := div_pos hc hN0
  have hw1 : c / N ≤ 1 := by nlinarith only [hw, hT, hw0]
  let S := logarithmicBallIndices (T * (c / N)) N n \ logarithmicBallIndices (2 * (c / N)) N n
  let B : ℝ := ∑ j ∈ S, crossSingular tiltedUnitSpline ((c / N) / |Real.log j - Real.log n|) /
    (Real.sqrt n * Real.sqrt j)
  have hB : |B| ≤ A * (2 * Real.exp 3 * (T * (c / N))) := by
    have hpt : ∀ j ∈ S,
        |crossSingular tiltedUnitSpline ((c / N) / |Real.log j - Real.log n|) /
          (Real.sqrt n * Real.sqrt j)| ≤ A * (1 / (Real.sqrt n * Real.sqrt j)) := by
      intro j hj
      obtain ⟨hjT, hj2⟩ := mem_sdiff.mp hj
      obtain ⟨hjI, hjn, _⟩ := mem_filter.mp hjT
      have hgap : 2 * (c / N) < |Real.log j - Real.log n| := lt_of_not_ge
        (fun hle => hj2 (mem_filter.mpr ⟨hjI, hjn, hle⟩))
      have hb := hbound (|Real.log j - Real.log n| / (c / N))
        ((le_div_iff₀ hw0).mpr hgap.le)
      rw [one_div_div] at hb
      rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ) * Real.sqrt j)]
      exact (div_le_div_of_nonneg_right hb (by positivity)).trans_eq (by ring)
    have hsum : (∑ j ∈ S, 1 / (Real.sqrt n * Real.sqrt j)) ≤
        2 * Real.exp 3 * (T * (c / N)) :=
      (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)).trans
        (sum_logarithmic_ball_reciprocal_sqrt_le (mul_pos hT0 hw0) (hw.trans (by norm_num)) hn)
    calc
      |B| ≤ ∑ j ∈ S, A * (1 / (Real.sqrt n * Real.sqrt j)) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
      _ = A * ∑ j ∈ S, 1 / (Real.sqrt n * Real.sqrt j) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hA
  have hcurv : |polarFarAnnulusRow T c N n - B / (c / N)| ≤ D * (c / N) := by
    have hh := abs_polarFar_actual_sub_singular_row_le hφ hsupp hI hT hw0
      (hw.trans (by norm_num)) hn
    have he : polarFarAnnulusRow T c N n - B / (c / N) =
        (∑ j ∈ S, (atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j -
          crossSingular tiltedUnitSpline ((c / N) / |Real.log j - Real.log n|)) /
            (Real.sqrt n * Real.sqrt j)) / (c / N) := by
      unfold polarFarAnnulusRow
      dsimp only [B, S]
      rw [← sub_div, ← sum_sub_distrib]
      congr 1
      exact sum_congr rfl fun j _ => by ring
    rw [he, abs_div, abs_of_pos hw0]
    exact (div_le_div_of_nonneg_right hh hw0.le).trans_eq
      (by dsimp only [D]; field_simp [hw0.ne'])
  have hB' : |B / (c / N)| ≤ 2 * Real.exp 3 * T * A := by
    rw [abs_div, abs_of_pos hw0]
    exact (div_le_div_of_nonneg_right hB hw0.le).trans_eq (by field_simp [hw0.ne'])
  have hm := hmean (w := c / N) (by rw [abs_of_pos hw0]; simpa only [mul_comm] using hw)
  rw [abs_of_pos hw0] at hm
  have htri : |polarFarAnnulusRow T c N n - polarFarMean T (c / N)| ≤
      |polarFarAnnulusRow T c N n - B / (c / N)| + |B / (c / N)| +
        |polarFarMean T (c / N) - polarFarMean T 0| + |polarFarMean T 0| := by
    have h1 := abs_sub_le (polarFarAnnulusRow T c N n) (B / (c / N)) (polarFarMean T (c / N))
    have h2 := abs_sub (B / (c / N)) (polarFarMean T (c / N))
    have h3 := abs_add_le (polarFarMean T (c / N) - polarFarMean T 0) (polarFarMean T 0)
    rw [sub_add_cancel] at h3
    linarith only [h1, h2, h3]
  have hd := mul_le_mul_of_nonneg_left hw1 hD
  have hc' := mul_le_mul_of_nonneg_left hw1 hC
  linarith only [htri, hcurv, hB', hm, hd, hc']

/-- Each fixed far annulus converges in normalized square mean to its scalar annular mean. -/
theorem tendsto_polarFarAnnulusRow_square_mean
    {δ T : ℝ} (hδ : 0 < δ) (hT : 2 ≤ T)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (polarFarAnnulusRow T (c N) N n - polarFarMean T (c N / N)) ^ 2) / N)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := exists_polarFarAnnulusRow_global_bound hT
  obtain ⟨C, D, hC, hD, hi⟩ := exists_polarFarAnnulusRow_interior_bound hT
  have hT0 : 0 < T := by linarith only [hT]
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hevent : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ T * (c N / N) ≤ 1 / 2 := by
    have ht := hcN.const_mul T
    rw [mul_zero] at ht
    filter_upwards [eventually_ge_atTop 1,
      ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with N hN hw
    exact ⟨hN, hw.le⟩
  apply tendsto_normalized_square_mean_of_terminal_strip hc hR hcrit
    (T := T) (C := C / δ) (D := D) (K := K) hT0.le
  · filter_upwards [hevent] with N hN n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hh := hb (zero_lt_one.trans_le (hc N)) hN.2
      (mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn).2⟩)
    exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hc N) hK)
  · filter_upwards [hevent] with N hN n hn hint
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hc0 := zero_lt_one.trans_le (hc N)
    have hnδ : δ * (N : ℝ) ≤ n := le_of_lt
      ((Nat.floor_lt (by positivity : 0 ≤ δ * (N : ℝ))).mp (mem_Ioc.mp hn).1)
    have hh := hi hc0 hN.2 (mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn).2⟩) hint
    have hratio : (N : ℝ) / n ≤ 1 / δ := by
      apply (div_le_div_iff₀ hn0 hδ).mpr
      simpa only [one_mul, mul_one, mul_comm] using hnδ
    have hpay := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) hc0.le
    exact hh.trans (add_le_add (hpay.trans_eq (by ring)) le_rfl)

/-- The zero-width far mean is the strong limit of every fixed annular row. -/
theorem tendsto_polarFarAnnulusRow_zero_width_square_mean
    {δ T : ℝ} (hδ : 0 < δ) (hT : 2 ≤ T)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (polarFarAnnulusRow T (c N) N n - polarFarMean T 0) ^ 2) / N)
      atTop (𝓝 0) := by
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hm := ((continuous_polarFarMean T).continuousAt.tendsto.comp hcN).sub_const (polarFarMean T 0)
  rw [sub_self] at hm
  have hconst := tendsto_normalized_square_mean_const
    (S := fun N => Ioc ⌊δ * (N : ℝ)⌋₊ N)
    (fun N => by rw [Nat.card_Ioc]; exact Nat.sub_le _ _) hm
  have hsum := tendsto_normalized_square_mean_add
    (tendsto_polarFarAnnulusRow_square_mean hδ hT hc hR hcrit) hconst
  exact hsum.congr fun N => by
    congr 1
    exact sum_congr rfl fun n _ => by congr 1; dsimp only [Function.comp_def]; ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
