import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.RegularizedPolarNearRowsHaveOneStrongMean
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarFarRowHasItsStrongMean
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheFullPolarCenterHasItsSampledProfile
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarUpwardRowHasAChebyshevProfile
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarReferenceDiagonalsVanishOnTerminalFractions
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarSamplingPreservesSquareMeanBounds
import Mathlib.NumberTheory.Chebyshev

/-!
# The polar matrix row has an explicit strong profile

The harmonic center and finite Chebyshev rows retain their sampled profiles.
Near and far Gamma means combine to the completed archimedean constant. All
remaining literal channels vanish in the critical top-window square norm.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The scalar polar profile in the receiving square-root coordinates. -/
def polarMatrixSampleProfile (x : ℝ) : ℝ :=
  ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
    (polarCenterProfile (fun _ => 1) x - Chebyshev.psi (1 / x) - Real.log (2 * Real.pi))

/-- The joint near vector is the polar sampling of its scalar row. -/
lemma polar_near_vector_eq_sample {c : ℝ} (hc : 0 < c) (N : ℕ) :
    normalizedNearGammaDownwardVector tiltedUnitSpline c N 1 +
      nearCenterVector tiltedUnitSpline c N 1 = polarSampleVector c N (polarNearRow c N) := by
  ext idx
  have hn0 : (0 : ℝ) < idx.1 := by exact_mod_cast (mem_Icc.mp idx.2).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp idx.2).1.trans (mem_Icc.mp idx.2).2
  have hs : Real.sqrt (idx.1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  change nearGammaDownwardRow tiltedUnitSpline c N 1 idx.1 / Real.sqrt (Real.log N) +
    (∑ j ∈ nearRowIndices c N idx.1,
      completeWeilPoleShift tiltedUnitSpline c / N * archimedeanCenterKernel idx.1 j *
        normalizedRamanujanMode 1 j / Real.sqrt j) / Real.sqrt (Real.log N) = _
  simp only [normalizedRamanujanMode_one, mul_one]
  have he : (∑ j ∈ nearRowIndices c N idx.1,
      completeWeilPoleShift tiltedUnitSpline c / N * archimedeanCenterKernel idx.1 j / Real.sqrt j) =
      (completeWeilPoleShift tiltedUnitSpline c / N) *
        (∑ j ∈ nearRowIndices c N idx.1, archimedeanCenterKernel idx.1 j / Real.sqrt j) := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [he]
  change _ = (c / N) * Real.sqrt idx.1 * polarNearRow c N idx.1 / Real.sqrt (Real.log N)
  unfold polarNearRow
  field_simp [hc.ne', hN0.ne', hs]

/-- The full separated matrix row is the polar sampling of its scalar row. -/
lemma polar_far_vector_eq_sample {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector 1 N) = polarSampleVector c N (polarFarRow c N) := by
  ext idx
  have hn0 : (0 : ℝ) < idx.1 := by exact_mod_cast (mem_Icc.mp idx.2).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp idx.2).1.trans (mem_Icc.mp idx.2).2
  have hs : Real.sqrt (idx.1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have happ : (Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector 1 N)) idx =
      (∑ j ∈ Icc 1 N,
        (if 2 * (c / N) < |Real.log j - Real.log idx.1| then
          atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) idx.1 j else 0) *
            (normalizedRamanujanMode 1 j / Real.sqrt j)) / Real.sqrt (Real.log N) := by
    rw [normalizedRamanujanHorizonVector, map_smul]
    change (Real.sqrt (Real.log N))⁻¹ *
      ((Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N)
        (ramanujanHorizonVector 1 N)) idx) = _
    rw [div_eq_inv_mul]
    congr 1
    exact horizonKernelMatrix_apply_profile
      (fun n j => if 2 * (c / N) < |Real.log j - Real.log n| then
        atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) n j else 0)
      (ramanujanPoleProfile 1) N idx
  rw [happ]
  simp only [normalizedRamanujanMode_one, mul_one_div, ite_div, zero_div]
  rw [← sum_filter]
  change _ = (c / N) * Real.sqrt idx.1 * polarFarRow c N idx.1 / Real.sqrt (Real.log N)
  unfold polarFarRow
  have he : (∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * (c / N) < |Real.log j - Real.log idx.1|),
      atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) idx.1 j /
        (Real.sqrt idx.1 * Real.sqrt j)) =
      (∑ j ∈ (Icc 1 N).filter (fun j : ℕ => 2 * (c / N) < |Real.log j - Real.log idx.1|),
        atomCrossErrorKernel (atomDilate tiltedUnitSpline (c / N)) idx.1 j / Real.sqrt j) /
          Real.sqrt idx.1 := by
    rw [sum_div]
    exact sum_congr rfl fun j _ => by ring
  rw [he]
  field_simp [hc.ne', hN0.ne', hs]

/-- The finite Mangoldt sampling agrees with the reciprocal Chebyshev profile. -/
lemma polarUpwardMeanVector_eq_sample (c : ℝ) (N : ℕ) :
    polarUpwardMeanVector c N = polarSampleVector c N (fun n =>
      ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
        Chebyshev.psi (1 / ((n : ℝ) / N))) := by
  ext idx
  have hn0 : (0 : ℝ) < idx.1 := by exact_mod_cast (mem_Icc.mp idx.2).1
  have hs : Real.sqrt (idx.1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hset : Ioc 0 ⌊(N : ℝ) / idx.1⌋₊ = Icc 1 ⌊(N : ℝ) / idx.1⌋₊ := by
    ext k
    simp only [mem_Ioc, mem_Icc]
    omega
  change (((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
      (c * idx.1 / N) * (∑ k ∈ Icc 1 ⌊(N : ℝ) / idx.1⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ))) /
        (Real.sqrt idx.1 * Real.sqrt (Real.log N)) = _
  change _ = (c / N) * Real.sqrt idx.1 *
    (((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
      Chebyshev.psi (1 / ((idx.1 : ℝ) / N))) / Real.sqrt (Real.log N)
  rw [one_div_div, Chebyshev.psi, hset]
  have he : c * (idx.1 : ℝ) / N = (c / N) * (Real.sqrt idx.1 * Real.sqrt idx.1) := by
    rw [← pow_two, Real.sq_sqrt hn0.le]
    ring
  rw [he]
  field_simp [hs]

/-- The full harmonic center sampling has the polar scalar normalization. -/
lemma polarCenterMeanVector_eq_sample (c : ℝ) (N : ℕ) :
    polarCenterMeanVector (completeWeilPoleShift tiltedUnitSpline c) N =
      polarSampleVector c N (fun n =>
        ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
          polarCenterProfile (fun _ => 1) ((n : ℝ) / N)) := by
  ext idx
  change (completeWeilPoleShift tiltedUnitSpline c / N) * Real.sqrt idx.1 *
    polarCenterProfile (fun _ => 1) ((idx.1 : ℝ) / N) / Real.sqrt (Real.log N) = _
  unfold completeWeilPoleShift
  change _ = (c / N) * Real.sqrt idx.1 *
    (((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
      polarCenterProfile (fun _ => 1) ((idx.1 : ℝ) / N)) / Real.sqrt (Real.log N)
  ring

/-- The retained sampled channels sum to the explicit polar profile. -/
lemma polar_matrix_sample_mean_identity (c : ℝ) (N : ℕ) :
    polarCenterMeanVector (completeWeilPoleShift tiltedUnitSpline c) N - polarUpwardMeanVector c N +
      polarSampleVector c N (fun _ => polarNearJointMean 0) -
      polarSampleVector c N (fun _ => 2 * farCrossFinitePart tiltedUnitSpline) =
    polarSampleVector c N (fun n => polarMatrixSampleProfile ((n : ℝ) / N)) := by
  rw [polarCenterMeanVector_eq_sample, polarUpwardMeanVector_eq_sample]
  rw [← polarSampleVector_sub, ← polarSampleVector_add, ← polarSampleVector_sub]
  congr 1
  funext n
  unfold polarMatrixSampleProfile
  calc
    _ = ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
        polarCenterProfile (fun _ => 1) ((n : ℝ) / N) -
      ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
        Chebyshev.psi (1 / ((n : ℝ) / N)) +
      (polarNearJointMean 0 - 2 * farCrossFinitePart tiltedUnitSpline) := by ring
    _ = _ := by rw [polarNearJointMean_sub_farFinitePart]; ring

/-- The complete polar matrix row converges to its explicit sampled profile on each fixed
terminal fraction of every positive critical curve. -/
theorem tendsto_topWindow_polar_matrix_profile
    {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N
      (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (normalizedRamanujanHorizonVector 1 N) -
        polarSampleVector (c N) N (fun n => polarMatrixSampleProfile ((n : ℝ) / N))))
      atTop (𝓝 0) := by
  have hc0 : ∀ N, 0 < c N := fun N => zero_lt_one.trans_le (hc N)
  have hbulk := tendsto_topWindow_bulk_subchannels (m := 1) (by norm_num) δ hc hR hcrit
  simp only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, inv_one, one_smul] at hbulk
  have hcenter := tendsto_topWindow_full_polarCenter_mean tiltedUnitSpline hδ hc0
  have hup := tendsto_topWindow_upward_polar_mean hδ hc hR hcrit
  have hdiag := tendsto_topWindow_polar_reference_diagonal tiltedUnitSpline
    (ramanujanAdjunctionEnergy 1 - Real.eulerMascheroniConstant) hδ hc0
      (criticalCurve_facts hc hR hcrit).1
  have hnear : Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N
      ((normalizedNearGammaDownwardVector tiltedUnitSpline (c N) N 1 +
        nearCenterVector tiltedUnitSpline (c N) N 1) -
        polarSampleVector (c N) N (fun _ => polarNearJointMean 0))) atTop (𝓝 0) := by
    have hh := tendsto_normalized_topWindow_polarSample hc0
      (tendsto_polarNearRow_square_mean hδ hc hR hcrit)
    exact hh.congr fun N => by rw [polarSampleVector_sub, ← polar_near_vector_eq_sample (hc0 N)]
  have hfar : Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N
      (Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline (c N) N)
        (normalizedRamanujanHorizonVector 1 N) -
        polarSampleVector (c N) N (fun _ => 2 * farCrossFinitePart tiltedUnitSpline))) atTop (𝓝 0) := by
    have hh := tendsto_normalized_topWindow_polarSample hc0
      (tendsto_polarFarRow_square_mean hδ hc hR hcrit)
    exact hh.congr fun N => by rw [polarSampleVector_sub, ← polar_far_vector_eq_sample (hc0 N)]
  have hs := tendsto_normalized_topWindow_add
    (tendsto_normalized_topWindow_add
      (tendsto_normalized_topWindow_add
        (tendsto_normalized_topWindow_add
          (tendsto_normalized_topWindow_add hbulk hcenter) hnear)
            (tendsto_normalized_topWindow_smul hfar (-1)))
              (tendsto_normalized_topWindow_smul hup (-1))) hdiag
  apply hs.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  apply congrArg (fun v => (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N v)
  rw [completeWeilMatrix_ramanujan_eq_terminal_channels contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos (hc0 N) hN (by norm_num),
    normalizedFullNearGammaDownwardVector_eq_sub contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      (hc0 N) N 1, ← polar_matrix_sample_mean_identity]
  simp only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, inv_one, one_smul, neg_one_smul]
  have hscalar : completeWeilSelfFinitePart tiltedUnitSpline (c N) +
      (ramanujanAdjunctionEnergy 1 - Real.eulerMascheroniConstant) =
      completeWeilSelfFinitePart tiltedUnitSpline (c N) + ramanujanAdjunctionEnergy 1 -
        Real.eulerMascheroniConstant := by ring
  rw [hscalar]
  module

/-- Subtracting the completed conductor diagonal preserves the strong polar row profile. -/
theorem tendsto_topWindow_polar_residual_profile
    {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N
      (conductorResidualVector (c N) 1 N -
        polarSampleVector (c N) N (fun n => polarMatrixSampleProfile ((n : ℝ) / N))))
      atTop (𝓝 0) := by
  have hdiag := tendsto_topWindow_completed_polar_diagonal hδ hc (criticalCurve_facts hc hR hcrit).1
  have hh := tendsto_normalized_topWindow_add (tendsto_topWindow_polar_matrix_profile hδ hc hR hcrit)
    (tendsto_normalized_topWindow_smul hdiag (-1))
  exact hh.congr fun N => by
    apply congrArg (fun v => (Real.log (N : ℝ) / c N ^ 2) * topWindowResidualMass δ N v)
    unfold conductorResidualVector
    simp only [neg_one_smul]
    module

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
