import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarFarAnnuliHaveStrongMeans

/-!
# The full polar far row has its strong finite-part mean

Fixed annuli converge in square mean. The remaining row tail is bounded by a
vanishing horizon error plus a reciprocal annulus radius. Sending the radius
to infinity identifies the full mean with twice the archimedean finite part.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The full separated polar row in the scalar receiving-row normalization. -/
def polarFarRow (c : ℝ) (N n : ℕ) : ℝ :=
  (∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * (c / N) < |Real.log j - Real.log n|),
    atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j /
      (Real.sqrt n * Real.sqrt j)) / (c / N)

/-- The full separated row outside a fixed annulus has reciprocal-radius decay. -/
theorem abs_polarFarRow_sub_annulus_le {c T : ℝ} {N n : ℕ}
    (hc : 0 < c) (hcN : c ≤ N) (hT : 2 ≤ T) (hn : n ∈ Icc 1 N) :
    |polarFarRow c N n - polarFarAnnulusRow T c N n| ≤
      4 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
          c / Real.sqrt n +
        64 * (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) / T := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hw0 : 0 < c / N := div_pos hc hN0
  let A := logarithmicBallIndices (T * (c / N)) N n \ logarithmicBallIndices (2 * (c / N)) N n
  let B := (Icc 1 N).filter (fun j : ℕ => T * (c / N) < |Real.log j - Real.log n|)
  let F := (Icc 1 N).filter (fun j : ℕ => 2 * (c / N) < |Real.log j - Real.log n|)
  have h2T : 2 * (c / N) ≤ T * (c / N) := mul_le_mul_of_nonneg_right hT hw0.le
  have hset : F = A ∪ B := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjI, hgap⟩ := mem_filter.mp hj
      by_cases hsmall : |Real.log j - Real.log n| ≤ T * (c / N)
      · have hjn : j ≠ n := by
          intro h
          subst j
          rw [sub_self, abs_zero] at hgap
          linarith only [hgap, hw0]
        apply mem_union_left
        apply Finset.mem_sdiff.mpr
        exact ⟨mem_filter.mpr ⟨hjI, hjn, hsmall⟩,
          fun h => (not_le_of_gt hgap) (mem_filter.mp h).2.2⟩
      · exact mem_union_right _ (mem_filter.mpr ⟨hjI, lt_of_not_ge hsmall⟩)
    · intro hj
      rcases mem_union.mp hj with hjA | hjB
      · obtain ⟨hjT, hj2⟩ := Finset.mem_sdiff.mp hjA
        obtain ⟨hjI, hjn, _⟩ := mem_filter.mp hjT
        exact mem_filter.mpr ⟨hjI, lt_of_not_ge
          (fun hle => hj2 (mem_filter.mpr ⟨hjI, hjn, hle⟩))⟩
      · obtain ⟨hjI, hgap⟩ := mem_filter.mp hjB
        exact mem_filter.mpr ⟨hjI, h2T.trans_lt hgap⟩
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro j hjA hjB
    have hle := (mem_filter.mp (Finset.mem_sdiff.mp hjA).1).2.2
    have hgt := (mem_filter.mp hjB).2
    exact (not_lt_of_ge hle) hgt
  have he : polarFarRow c N n - polarFarAnnulusRow T c N n =
      (∑ j ∈ B, atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j / Real.sqrt j) /
        (Real.sqrt n * (c / N)) := by
    change (∑ j ∈ F, _) / (c / N) - (∑ j ∈ A, _) / (c / N) = _
    rw [hset, sum_union hdisj, add_div, add_sub_cancel_left, sum_div]
    rw [sum_div]
    exact sum_congr rfl fun j _ => by ring
  have ht := separatedCross_tail_row_le (m := 1) (by norm_num) hn hc hcN hT
  simp only [Nat.cast_one, Real.sqrt_one, normalizedRamanujanMode_one, mul_one, mul_one_div] at ht
  rw [he, abs_div, abs_of_pos (mul_pos hsn hw0)]
  exact (div_le_div_of_nonneg_right ht (mul_pos hsn hw0).le).trans_eq
    (by field_simp [hc.ne', hN0.ne', hsn.ne'])

/-- The full far polar row converges in sampled square mean to its archimedean finite part. -/
theorem tendsto_polarFarRow_square_mean
    {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (polarFarRow (c N) N n - 2 * farCrossFinitePart tiltedUnitSpline) ^ 2) / (N : ℝ))
      atTop (𝓝 0) := by
  let K := 152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hc2N : Tendsto (fun N : ℕ => c N ^ 2 / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 2 0
  have ha : Tendsto (fun N : ℕ => (4 * K / Real.sqrt δ) * Real.sqrt (c N ^ 2 / N))
      atTop (𝓝 0) := by
    have hh := (Real.continuous_sqrt.continuousAt.tendsto.comp hc2N).const_mul (4 * K / Real.sqrt δ)
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using hh
  apply tendsto_normalized_square_mean_of_annular_limits
    (S := fun N => Ioc ⌊δ * (N : ℝ)⌋₊ N)
    (g := fun T N n => polarFarAnnulusRow T (c N) N n)
    (m := fun T => polarFarMean T 0) (B := 64 * K) (C := 4)
    (fun N => by rw [Nat.card_Ioc]; exact Nat.sub_le _ _) ha
    (fun T hT => tendsto_polarFarAnnulusRow_zero_width_square_mean hδ hT hc hR hcrit)
    ?_ (fun T hT => abs_polarFarMean_zero_sub_le hT)
  intro T hT
  filter_upwards [eventually_ge_atTop 1,
    hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hw n hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 := zero_lt_one.trans_le (hc N)
  have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnδ : δ * (N : ℝ) ≤ n := le_of_lt
    ((Nat.floor_lt (by positivity : 0 ≤ δ * (N : ℝ))).mp (mem_Ioc.mp hn).1)
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsδN : 0 < Real.sqrt (δ * N) := Real.sqrt_pos.mpr (mul_pos hδ hN0)
  have hh := abs_polarFarRow_sub_annulus_le hc0 ((div_le_one hN0).mp hw.le) hT
    (mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn).2⟩)
  have hdiv : c N / Real.sqrt n ≤ Real.sqrt (c N ^ 2 / N) / Real.sqrt δ := by
    calc
      _ ≤ c N / Real.sqrt (δ * N) := div_le_div_of_nonneg_left hc0.le hsδN
        (Real.sqrt_le_sqrt hnδ)
      _ = _ := by
        rw [Real.sqrt_mul hδ.le, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hc0.le]
        ring
  have hp := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 4 * K)
  have he : (4 * K) * (Real.sqrt (c N ^ 2 / N) / Real.sqrt δ) =
      (4 * K / Real.sqrt δ) * Real.sqrt (c N ^ 2 / N) := by ring
  rw [he] at hp
  exact hh.trans (add_le_add (by simpa only [K, mul_div_assoc] using hp) le_rfl)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
