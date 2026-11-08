import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarCenterRowHasItsStrongProfile
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation

/-!
# The full polar center has its sampled profile

The exact matrix row is the harmonic polar center times its square-root weight.
The harmonic-to-logarithmic square-mean estimate therefore gives convergence of
the actual center channel in the top-window matrix normalization.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The exact polar center matrix row is its harmonic boundary expression. -/
theorem fullWeilCenter_polar_coordinate (α : ℝ) {N : ℕ} (idx : PrimeHorizonIndex N) :
    (Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
      (normalizedRamanujanHorizonVector 1 N)) idx =
      (α / N) * Real.sqrt idx.1 * polarCenterRow N idx.1 / Real.sqrt (Real.log N) := by
  have hn0 : (0 : ℝ) < idx.1 := by exact_mod_cast (mem_Icc.mp idx.2).1
  have hs0 : Real.sqrt (idx.1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have happ : (Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
      (normalizedRamanujanHorizonVector 1 N)) idx =
      (∑ j ∈ Icc 1 N, (α / N) *
        (arithmeticPoleKernel idx.1 j - archimedeanCenterKernel idx.1 j) *
          (normalizedRamanujanMode 1 j / Real.sqrt j)) / Real.sqrt (Real.log N) := by
    rw [normalizedRamanujanHorizonVector, map_smul]
    change (Real.sqrt (Real.log N))⁻¹ *
      ((Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
        (ramanujanHorizonVector 1 N)) idx) = _
    rw [div_eq_inv_mul]
    congr 1
    exact horizonKernelMatrix_apply_profile
      (fun n j => (α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j))
      (ramanujanPoleProfile 1) N idx
  rw [happ]
  simp only [normalizedRamanujanMode_one]
  have hsum : (∑ j ∈ Icc 1 N, (α / N) *
      (arithmeticPoleKernel idx.1 j - archimedeanCenterKernel idx.1 j) * (1 / Real.sqrt j)) =
      (α / N) * (Real.sqrt idx.1 * polarCenterRow N idx.1) := by
    simp_rw [mul_assoc]
    rw [← mul_sum]
    congr 1
    simp only [arithmeticPoleKernel, mul_one_div]
    rw [sum_pole_minus_center_div_sqrt idx.2]
    unfold polarCenterRow
    have he : (N : ℝ) / Real.sqrt idx.1 = Real.sqrt idx.1 * ((N : ℝ) / idx.1) := by
      apply (div_eq_iff hs0).mpr
      calc
        (N : ℝ) = ((N : ℝ) / idx.1) * idx.1 := (div_mul_cancel₀ _ hn0.ne').symm
        _ = ((N : ℝ) / idx.1) * (Real.sqrt idx.1) ^ 2 := by rw [Real.sq_sqrt hn0.le]
        _ = _ := by ring
    rw [he]
    ring
  rw [hsum]
  ring

/-- The logarithmic polar center sampled at the horizon coordinates. -/
def polarCenterMeanVector (α : ℝ) (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun idx : PrimeHorizonIndex N =>
    (α / N) * Real.sqrt idx.1 * polarCenterProfile (fun _ => 1) ((idx.1 : ℝ) / N) /
      Real.sqrt (Real.log N))

/-- The full center channel converges to its sampled logarithmic profile in the normalized
top-window square norm. -/
theorem tendsto_topWindow_full_polarCenter_mean
    (φ : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N
        (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ (c N)) N)
          (normalizedRamanujanHorizonVector 1 N) -
          polarCenterMeanVector (completeWeilPoleShift φ (c N)) N)) atTop (𝓝 0) := by
  let a : ℝ := (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)
  have hlim := (tendsto_normalized_polarCenter_profile_error hδ).const_mul (a ^ 2)
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hN hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hshift : completeWeilPoleShift φ (c N) = c N * a := by
    unfold completeWeilPoleShift
    dsimp only [a]
    ring
  have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (Real.log (N : ℝ) / c N ^ 2) *
        primeHorizonExtension
          (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ (c N)) N)
            (normalizedRamanujanHorizonVector 1 N) -
            polarCenterMeanVector (completeWeilPoleShift φ (c N)) N) n ^ 2 ≤
      (a ^ 2 / N) * (polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N)) ^ 2 := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hnN := (mem_Ioc.mp hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, hnN⟩⟩
    have hext : primeHorizonExtension
        (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ (c N)) N)
          (normalizedRamanujanHorizonVector 1 N) -
          polarCenterMeanVector (completeWeilPoleShift φ (c N)) N) n =
        ((c N * a) / N) * Real.sqrt n *
          (polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N)) /
            Real.sqrt (Real.log N) := by
      change primeHorizonExtension _ idx.1 = _
      rw [primeHorizonExtension_coe]
      change (Matrix.toEuclideanLin _ _) idx - (polarCenterMeanVector _ N) idx = _
      rw [fullWeilCenter_polar_coordinate, hshift]
      change _ - ((c N * a) / N) * Real.sqrt n *
        polarCenterProfile (fun _ => 1) ((n : ℝ) / N) / Real.sqrt (Real.log N) = _
      ring
    rw [hext]
    have he : (Real.log (N : ℝ) / c N ^ 2) *
        (((c N * a) / N) * Real.sqrt n *
          (polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N)) /
            Real.sqrt (Real.log N)) ^ 2 =
        (a ^ 2 / N) * ((n : ℝ) / N) *
          (polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N)) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hL.le]
      field_simp [hN0.ne', hL.ne', (hc N).ne']
      ring
    rw [he]
    have hx : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hnN)
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ a ^ 2 / N)).trans_eq (mul_one _))
      (sq_nonneg _)
  unfold topWindowResidualMass
  rw [mul_sum]
  exact (sum_le_sum hpt).trans_eq (by rw [← mul_sum]; ring)

#print axioms fullWeilCenter_polar_coordinate
#print axioms tendsto_topWindow_full_polarCenter_mean
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
