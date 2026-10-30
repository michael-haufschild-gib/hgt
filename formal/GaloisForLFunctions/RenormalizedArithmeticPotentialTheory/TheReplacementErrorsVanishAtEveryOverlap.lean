import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixDecomposesAtEveryOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixHasRamanujanQuasimodes
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.OverlapForcesNewRamanujanTerms

/-!
# The replacement errors vanish on Ramanujan modes at every overlap

Below touching the complete matrix differs from its arithmetic model by three replacement errors:
the self-energy error, the two-pole error and the atom-cross error. At a fixed overlap ratio
`c > 0` the first two are controlled exactly as before once `c ≤ N`. The cross error is kept only on
far pairs, at log-distance `s > 2w`, where `s − w > s/2` gives the reciprocal-square bound
`|E(n, j)| ≤ 152 (∫|φ|)²/∫φ² · w² · max(n, j)²/|n − j|²` at every overlap. All three vanish in norm
on every normalized Ramanujan vector (`tendsto_completeWeilSelfError_of_pos`,
`tendsto_fullWeilPoleErrorMatrix_ramanujan_norm_of_pos`,
`tendsto_separatedCrossErrorMatrix_ramanujan_norm`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis HTGeometry
open _root_.RHTower (archLevyDensity)

variable {φ : ℝ → ℝ}

/-- The self-energy error vanishes at every fixed overlap ratio. -/
theorem tendsto_completeWeilSelfError_of_pos (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) :
    Tendsto (completeWeilSelfError φ c) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => Real.exp (1 / 2) / 2 * (c / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).const_mul (Real.exp (1 / 2) / 2)
  have hbound : ∀ᶠ N : ℕ in atTop, |completeWeilSelfError φ c N| ≤ Real.exp (1 / 2) / 2 * (c / N) := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈c⌉₊] with N hN hcN
    exact abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc0 hN
      ((Nat.le_ceil c).trans (by exact_mod_cast hcN))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _)
    (by simpa only [Real.norm_eq_abs] using hbound) hlim

/-- The two-pole replacement coefficient is quadratic in the width once `c ≤ N`. -/
theorem abs_atomPoleErrorCoefficient_le_of_le (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (hcN : c ≤ N) :
    |atomPoleErrorCoefficient φ c N| ≤ atomPoleMomentErrorConstant φ * (c / N) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr hcN
  have h := abs_dilated_pole_product_sub_le hφ hsupp hM hw0 hw1
  have heq : atomPoleErrorCoefficient φ c N =
      atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) *
        atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) /
          (∫ u, atomDilate φ (c / N) u ^ 2) -
        (c / N) * (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) := by
    simp only [atomPoleErrorCoefficient, completeWeilPoleShift]
    ring
  rw [heq]
  exact h

/-- The two-pole replacement vanishes in norm on every normalized Ramanujan mode, at every `c`. -/
theorem tendsto_fullWeilPoleErrorMatrix_ramanujan_norm_of_pos (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  have hb : ∀ᶠ N : ℕ in atTop,
      ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector m N)‖ ^ 2 ≤
        4 * (atomPoleMomentErrorConstant φ) ^ 2 * A ^ 2 * c ^ 4 := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈c⌉₊] with N hN hcN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcN' : c ≤ N := (Nat.le_ceil c).trans (by exact_mod_cast hcN)
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hd := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM hc0 hN hcN'
    have hs := mul_self_le_mul_self (abs_nonneg _) hd
    rw [← sq, sq_abs, ← sq] at hs
    have hprof : ∀ j ∈ Icc 1 N, |normalizedRamanujanMode m j| ≤ A :=
      fun j _ => abs_normalizedRamanujanMode_le hm j
    calc (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, atomPoleErrorCoefficient φ c N *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * ramanujanPoleProfile m j) ^ 2)
        = ∑ n ∈ Icc 1 N, (atomPoleErrorCoefficient φ c N * ∑ j ∈ Icc 1 N,
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
            (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 := by
          refine sum_congr rfl fun n _ => ?_
          rw [mul_sum]
          congr 1
          refine sum_congr rfl fun j _ => ?_
          simp only [ramanujanPoleProfile]
          ring
      _ ≤ 4 * (atomPoleErrorCoefficient φ c N) ^ 2 * A ^ 2 * (N : ℝ) ^ 4 :=
          sum_sq_twoPoleKernel_poleProfile_le hA N hprof _
      _ ≤ 4 * (atomPoleMomentErrorConstant φ * (c / N) ^ 2) ^ 2 * A ^ 2 * (N : ℝ) ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = _ := by field_simp [hN0.ne']
  have h := tendsto_horizon_normalized_norm_of_sq_bounded
    (fun N => Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector m N)) hb
  simpa only [normalizedRamanujanHorizonVector, map_smul] using h

/-- Far pairs of the cross error obey the reciprocal-square bound at every overlap ratio. -/
theorem abs_separatedCrossError_le (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    {N n j : ℕ} (hN : 1 ≤ N) (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    |(if 2 * (c / N) < |Real.log j - Real.log n| then
        atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0)| ≤
      (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) * (c / N) ^ 2) *
        (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 := div_pos hc0 hN0
  have hK0 : 0 ≤ 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) * (c / N) ^ 2 := by positivity
  split_ifs with hs
  · obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw0
    set g := atomDilate φ (c / N) with hgdef
    set s := |Real.log j - Real.log n| with hsdef
    have hnj : n ≠ j := by
      intro h; subst h; simp [hsdef] at hs; linarith
    have hG : 0 < ∫ u, g u ^ 2 := by rw [hgdef, integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
    have hws : c / N < s := by linarith
    have herr := abs_crossTerm_sub_le hg.continuous hgc hgsupp hw0.le hws
    have hvar := archLevyDensity_window_sub_le hw0.le hws
    have hsw : s / 2 < s - c / N := by linarith
    have hs0 : 0 < s := by linarith
    have hrel : |(n : ℝ) - j| / max (n : ℝ) j ≤ s := by
      have := gap_div_le_abs_log_div (mem_Icc.mp hn).1 (mem_Icc.mp hj).1 hnj
      rw [Real.log_div (by exact_mod_cast (by have := (mem_Icc.mp hn).1; omega : n ≠ 0))
        (by exact_mod_cast (by have := (mem_Icc.mp hj).1; omega : j ≠ 0))] at this
      rw [hsdef, abs_sub_comm (Real.log j)]
      exact this
    have hnz : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hjz : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
    rw [atomCrossErrorKernel, if_neg hnj, archimedeanCenterKernel,
      if_neg (by simp only [hnj, hnz, hjz, or_self, not_false_eq_true])]
    have heq : atomCrossTerm g s / (∫ u, g u ^ 2) -
        ((∫ u, g u) ^ 2 / (∫ u, g u ^ 2)) * archLevyDensity s =
        (atomCrossTerm g s - archLevyDensity s * (∫ u, g u) ^ 2) / (∫ u, g u ^ 2) := by ring
    rw [heq, abs_div, abs_of_pos hG]
    have habs : (∫ u, |g u|) = c / N * ∫ u, |φ u| := integral_abs_atomDilate hw0
    have hgM : (∫ u, g u ^ 2) = c / N * ∫ u, φ u ^ 2 := integral_atomDilate_sq hw0
    have hmax0 : 0 < max (n : ℝ) j := lt_of_lt_of_le (by exact_mod_cast Nat.pos_of_ne_zero hnz)
      (le_max_left _ _)
    have hd0 : 0 < |(n : ℝ) - j| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hnj))
    have hinv : 1 / (s - c / N) ^ 2 ≤ 4 * ((max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) := by
      have h1 : 1 / (s - c / N) ^ 2 ≤ 1 / (s / 2) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hsw.le 2)
      have h2 : 1 / (s / 2) ^ 2 = 4 * (1 / s ^ 2) := by field_simp; ring
      have h3 : 1 / s ^ 2 ≤ (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        have := pow_le_pow_left₀ (by positivity) hrel 2
        rw [div_pow, div_le_iff₀ (by positivity)] at this
        linarith
      linarith
    calc |atomCrossTerm g s - archLevyDensity s * (∫ u, g u) ^ 2| / (∫ u, g u ^ 2)
        ≤ ((38 * (c / N) / (s - c / N) ^ 2) * (∫ u, |g u|) ^ 2) / (∫ u, g u ^ 2) :=
          div_le_div_of_nonneg_right (herr.trans (mul_le_mul_of_nonneg_right hvar (sq_nonneg _)))
            hG.le
      _ = (38 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) * (c / N) ^ 2) * (1 / (s - c / N) ^ 2) := by
          rw [habs, hgM]; field_simp
      _ ≤ (38 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) * (c / N) ^ 2) *
          (4 * ((max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2)) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  · rw [abs_zero]
    by_cases hnj : n = j
    · subst hnj; simp
    · have hd0 : 0 < |(n : ℝ) - j| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hnj))
      positivity

/-- The far cross error vanishes in norm on every normalized Ramanujan mode, at every overlap. -/
theorem tendsto_separatedCrossErrorMatrix_ramanujan_norm (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  set K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hb : ∀ᶠ N : ℕ in atTop,
      ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (ramanujanHorizonVector m N)‖ ^ 2 ≤
        (36 * K₀ * A * c ^ 2) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => if 2 * (c / N) < |Real.log j - Real.log n| then
        atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hentry := fun (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ Icc 1 N) =>
      abs_separatedCrossError_le hφ hsupp hM hc0 hN hn hj
    have h := sum_sq_kernel_poleProfile_le (mul_nonneg hK₀0 (sq_nonneg (c / (N : ℝ)))) hentry hA
      (fun j _ => abs_normalizedRamanujanMode_le hm j)
    calc (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, (if 2 * (c / N) < |Real.log j - Real.log n| then
          atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) * ramanujanPoleProfile m j) ^ 2)
        = ∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, (if 2 * (c / N) < |Real.log j - Real.log n| then
          atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) *
            (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 := by
          refine sum_congr rfl fun n _ => ?_
          congr 1
      _ ≤ (36 * (K₀ * (c / N) ^ 2) * A) ^ 2 * (N : ℝ) ^ 4 := h
      _ = (36 * K₀ * A * c ^ 2) ^ 2 := by field_simp [hN0.ne']
  have h := tendsto_horizon_normalized_norm_of_sq_bounded
    (fun N => Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (ramanujanHorizonVector m N)) hb
  simpa only [normalizedRamanujanHorizonVector, map_smul] using h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
