import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarNearGammaRowsHaveUniformMeans
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheGrowingGammaPairMeanIsPolar

/-!
# Uniform means for the polar far Gamma row

Clamping the reciprocal singular kernel across the central gap gives a bounded
Lipschitz function. Subtracting two logarithmic balls then gives the mean of each
fixed separated annulus, with a lattice error of order `1/n`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The separated singular profile extended constantly across its central gap. -/
def polarFarClampedKernel (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  crossSingular φ (1 / max 2 |t|)

/-- Clamping the reciprocal profile preserves boundedness and Lipschitz regularity. -/
theorem exists_polarFarClampedKernel_bounds {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ t, |polarFarClampedKernel φ t| ≤ C) ∧
      ∀ s t, |polarFarClampedKernel φ s - polarFarClampedKernel φ t| ≤ C * |s - t| := by
  obtain ⟨C, hC, hA, hL⟩ := exists_crossSingular_inverse_bounds hφ hsupp hM
  refine ⟨C, hC, fun t => hA _ (le_max_left _ _), ?_⟩
  intro s t
  have hmax : |max (2 : ℝ) (|s|) - max 2 (|t|)| ≤ |s - t| := by
    have hab := abs_le.mp (abs_abs_sub_abs_le s t)
    by_cases hs : |s| ≤ 2 <;> by_cases ht : |t| ≤ 2
    · rw [max_eq_left hs, max_eq_left ht, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [max_eq_left hs, max_eq_right (le_of_not_ge ht)]
      apply abs_le.mpr
      constructor <;> linarith only [hab.1, hab.2, hs, le_of_not_ge ht, abs_nonneg (s - t)]
    · rw [max_eq_right (le_of_not_ge hs), max_eq_left ht]
      apply abs_le.mpr
      constructor <;> linarith only [hab.1, hab.2, ht, le_of_not_ge hs, abs_nonneg (s - t)]
    · rw [max_eq_right (le_of_not_ge hs), max_eq_right (le_of_not_ge ht)]
      exact abs_abs_sub_abs_le s t
  exact (hL _ _ (le_max_left _ _) (le_max_left _ _)).trans
    (mul_le_mul_of_nonneg_left hmax hC)

/-- Subtracting nested logarithmic balls yields the corresponding annulus mean. -/
theorem abs_logarithmic_annulus_row_sub_mean_le {K : ℝ → ℝ} {A L T w : ℝ} {N n : ℕ}
    (hT : 2 ≤ T) (hw : 0 < w) (hTw : T * w ≤ 1 / 2) (hL0 : 0 ≤ L)
    (hA : ∀ s ∈ Set.Icc (-T) T, |K s| ≤ A)
    (hL : ∀ s ∈ Set.Icc (-T) T, ∀ t ∈ Set.Icc (-T) T,
      |K s - K t| ≤ L * |s - t|)
    (hn : n ∈ Icc 1 N) (hinterior : (n : ℝ) * Real.exp (T * w) ≤ N) :
    |(∑ j ∈ logarithmicBallIndices (T * w) N n \ logarithmicBallIndices (2 * w) N n,
        K ((Real.log j - Real.log n) / w) / (Real.sqrt n * Real.sqrt j)) -
      ((∫ t in (-T)..T, K t * (w * Real.exp (w * t / 2))) -
        ∫ t in (-2 : ℝ)..2, K t * (w * Real.exp (w * t / 2)))| ≤
      ((32 * T + 64) * L + 34 * A) / n := by
  have h2w : 2 * w ≤ T * w := mul_le_mul_of_nonneg_right hT hw.le
  have hsmall : Set.Icc (-2 : ℝ) 2 ⊆ Set.Icc (-T) T := by
    intro s hs
    constructor <;> linarith only [hs.1, hs.2, hT]
  have hsmallInterior : (n : ℝ) * Real.exp (2 * w) ≤ N :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2w) (Nat.cast_nonneg n)).trans hinterior
  have hbig := abs_logarithmic_ball_row_sub_mean_le
    (by linarith only [hT] : 0 < T) hw hTw hL0 hA hL hn hinterior
  have hsmallMean := abs_logarithmic_ball_row_sub_mean_le
    (by norm_num : (0 : ℝ) < 2) hw (h2w.trans hTw) hL0
    (fun s hs => hA s (hsmall hs))
    (fun s hs t ht => hL s (hsmall hs) t (hsmall ht)) hn hsmallInterior
  have hsub : logarithmicBallIndices (2 * w) N n ⊆ logarithmicBallIndices (T * w) N n := by
    intro j hj
    obtain ⟨hjI, hjn, hjgap⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨hjI, hjn, hjgap.trans h2w⟩
  let f : ℕ → ℝ := fun j => K ((Real.log j - Real.log n) / w) / (Real.sqrt n * Real.sqrt j)
  have hsum : (∑ j ∈ logarithmicBallIndices (T * w) N n \ logarithmicBallIndices (2 * w) N n, f j) =
      (∑ j ∈ logarithmicBallIndices (T * w) N n, f j) -
        ∑ j ∈ logarithmicBallIndices (2 * w) N n, f j := by
    have hh := sum_sdiff (f := f) hsub
    linarith only [hh]
  change |(∑ j ∈ logarithmicBallIndices (T * w) N n \ logarithmicBallIndices (2 * w) N n, f j) - _| ≤ _
  rw [hsum]
  have hid (a b c d : ℝ) : (a - b) - (c - d) = (a - c) - (b - d) := by ring
  rw [hid]
  exact ((abs_sub _ _).trans (add_le_add hbig hsmallMean)).trans_eq (by ring)

/-- The far singular profile has one mean on each fixed annulus. -/
theorem exists_polarFar_annulus_mean_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T w : ℝ} {N n : ℕ}, 2 ≤ T → 0 < w → T * w ≤ 1 / 2 →
      n ∈ Icc 1 N → (n : ℝ) * Real.exp (T * w) ≤ N →
      |(∑ j ∈ logarithmicBallIndices (T * w) N n \ logarithmicBallIndices (2 * w) N n,
          crossSingular φ (w / |Real.log j - Real.log n|) / (Real.sqrt n * Real.sqrt j)) -
        ((∫ t in (-T)..T, polarFarClampedKernel φ t * (w * Real.exp (w * t / 2))) -
          ∫ t in (-2 : ℝ)..2, polarFarClampedKernel φ t * (w * Real.exp (w * t / 2)))| ≤
        (32 * T + 98) * C / n := by
  obtain ⟨C, hC, hA, hL⟩ := exists_polarFarClampedKernel_bounds hφ hsupp hM
  refine ⟨C, hC, ?_⟩
  intro T w N n hT hw hTw hn hinterior
  have h := abs_logarithmic_annulus_row_sub_mean_le hT hw hTw hC
    (fun s _ => hA s) (fun s _ t _ => hL s t) hn hinterior
  have he : (∑ j ∈ logarithmicBallIndices (T * w) N n \ logarithmicBallIndices (2 * w) N n,
      polarFarClampedKernel φ ((Real.log j - Real.log n) / w) / (Real.sqrt n * Real.sqrt j)) =
      ∑ j ∈ logarithmicBallIndices (T * w) N n \ logarithmicBallIndices (2 * w) N n,
        crossSingular φ (w / |Real.log j - Real.log n|) / (Real.sqrt n * Real.sqrt j) := by
    refine sum_congr rfl fun j hj => ?_
    obtain ⟨hjT, hj2⟩ := mem_sdiff.mp hj
    obtain ⟨hjI, hjn, _⟩ := mem_filter.mp hjT
    have hgap : 2 * w < |Real.log j - Real.log n| := lt_of_not_ge
      (fun hle => hj2 (mem_filter.mpr ⟨hjI, hjn, hle⟩))
    have hlarge : 2 ≤ |(Real.log j - Real.log n) / w| := by
      rw [abs_div, abs_of_pos hw]
      exact (le_div_iff₀ hw).mpr hgap.le
    dsimp only [polarFarClampedKernel]
    rw [max_eq_right hlarge, abs_div, abs_of_pos hw, one_div_div]
  rw [he] at h
  exact h.trans_eq (by ring)

/-- A logarithmic ball has uniformly bounded reciprocal square-root mass, including rows
whose ball meets the terminal boundary. -/
lemma sum_logarithmic_ball_reciprocal_sqrt_le {N n : ℕ} {t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 2) (hn : n ∈ Icc 1 N) :
    (∑ j ∈ logarithmicBallIndices t N n, 1 / (Real.sqrt n * Real.sqrt j)) ≤
      2 * Real.exp 3 * t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by
    exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  let c : ℝ := t * N / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hw : c / N = t / 2 := by dsimp only [c]; field_simp
  have hset : nearRowIndices c N n = logarithmicBallIndices t N n := by
    have hwidth : 2 * c / N = t := by dsimp only [c]; field_simp
    simp only [nearRowIndices, logarithmicBallIndices, hwidth]
  obtain ⟨hcard, hpoint⟩ := nearRowIndices_card_and_pointwise_local
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hc hN0 (by rw [hw]; linarith only [ht2]) hn
  rw [hset] at hcard hpoint
  have hcard' : ((logarithmicBallIndices t N n).card : ℝ) ≤ 2 * n * Real.exp 2 * t := by
    have hid : 2 * (n : ℝ) * (linearNearRowRadius c / N) = 2 * n * Real.exp 2 * t := by
      unfold linearNearRowRadius
      dsimp only [c]
      field_simp
    exact hcard.trans_eq hid
  calc
    _ ≤ ∑ _j ∈ logarithmicBallIndices t N n, Real.exp 1 / n := by
      refine sum_le_sum fun j hj => ?_
      have hh := mul_le_mul_of_nonneg_left (hpoint j hj).1 (le_of_lt (one_div_pos.mpr hsn))
      have he : (1 / Real.sqrt (n : ℝ)) * (Real.exp 1 / Real.sqrt n) = Real.exp 1 / n := by
        rw [div_mul_div_comm, one_mul, ← pow_two, Real.sq_sqrt hn0.le]
      calc
        _ = (1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt j) := by ring
        _ ≤ (1 / Real.sqrt (n : ℝ)) * (Real.exp 1 / Real.sqrt n) := hh
        _ = _ := he
    _ = ((logarithmicBallIndices t N n).card : ℝ) * (Real.exp 1 / n) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * n * Real.exp 2 * t) * (Real.exp 1 / n) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = _ := by
      have he : Real.exp (2 : ℝ) * Real.exp 1 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
      calc
        _ = 2 * t * (Real.exp 2 * Real.exp 1) := by field_simp [hn0.ne']
        _ = _ := by rw [he]; ring

/-- Atomic curvature contributes only a quadratic-width error to a fixed far-annulus row. -/
theorem abs_polarFar_actual_sub_singular_row_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {T w : ℝ} {N n : ℕ}
    (hT : 2 ≤ T) (hw : 0 < w) (hTw : T * w ≤ 2) (hn : n ∈ Icc 1 N) :
    |∑ j ∈ logarithmicBallIndices (T * w) N n \ logarithmicBallIndices (2 * w) N n,
        (atomCrossErrorKernel (atomDilate φ w) n j -
          crossSingular φ (w / |Real.log j - Real.log n|)) /
            (Real.sqrt n * Real.sqrt j)| ≤
      2 * Real.exp 3 * (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2)) * T * w ^ 2 := by
  let D : ℝ := 5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  let S := logarithmicBallIndices (T * w) N n \ logarithmicBallIndices (2 * w) N n
  have hpt : ∀ j ∈ S,
      |(atomCrossErrorKernel (atomDilate φ w) n j -
        crossSingular φ (w / |Real.log j - Real.log n|)) / (Real.sqrt n * Real.sqrt j)| ≤
      (D * w) * (1 / (Real.sqrt n * Real.sqrt j)) := by
    intro j hj
    obtain ⟨hjT, hj2⟩ := mem_sdiff.mp hj
    obtain ⟨hjI, hjn, _⟩ := mem_filter.mp hjT
    have hj1 := (mem_Icc.mp hjI).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hgap : 2 * w < |Real.log j - Real.log n| := lt_of_not_ge
      (fun hle => hj2 (mem_filter.mpr ⟨hjI, hjn, hle⟩))
    have hb := abs_atomCrossErrorKernel_sub_crossSingular_le hφ hsupp hM hw hn1 hj1
      (Ne.symm hjn) (by linarith only [hgap, hw])
    rw [abs_div, abs_of_pos (mul_pos (Real.sqrt_pos.mpr hn0) (Real.sqrt_pos.mpr hj0))]
    exact (div_le_div_of_nonneg_right hb (by positivity)).trans_eq (by dsimp only [D]; ring)
  have hsum : (∑ j ∈ S, 1 / (Real.sqrt n * Real.sqrt j)) ≤ 2 * Real.exp 3 * (T * w) :=
    (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)).trans
      (sum_logarithmic_ball_reciprocal_sqrt_le (mul_pos (by linarith only [hT]) hw) hTw hn)
  calc
    _ ≤ ∑ j ∈ S, (D * w) * (1 / (Real.sqrt n * Real.sqrt j)) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
    _ = (D * w) * ∑ j ∈ S, 1 / (Real.sqrt n * Real.sqrt j) := (mul_sum _ _ _).symm
    _ ≤ (D * w) * (2 * Real.exp 3 * (T * w)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hD hw.le)
    _ = _ := by dsimp only [D]; ring

#print axioms abs_polarFar_actual_sub_singular_row_le
#print axioms exists_polarFarClampedKernel_bounds
#print axioms exists_polarFar_annulus_mean_bound
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
