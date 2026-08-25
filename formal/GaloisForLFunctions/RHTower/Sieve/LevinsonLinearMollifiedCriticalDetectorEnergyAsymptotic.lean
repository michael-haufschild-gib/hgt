import GaloisForLFunctions.RHTower.Sieve.VonMangoldtMomentRatioAsymptotics

noncomputable section

open Filter Topology Finset
open scoped BigOperators

namespace RHTower.Sieve

/-- Logarithmically scaled detector coefficient used in the critical short-range limit. -/
def levinsonScaledDetectorParameter (r : ℝ) (N : ℕ) : ℝ :=
  r / Real.log N

/-- Exact limiting non-unit energy for the linear mollifier and scaled differentiated detector. -/
theorem tendsto_levinsonLinearMollifiedCriticalDetector_nonunitEnergy (r : ℝ) :
    Tendsto (fun N : ℕ =>
      ∑ k ∈ Finset.Icc 2 N,
        ‖levinsonLinearMollifiedCriticalDetectorCoeff
          (levinsonScaledDetectorParameter r N) N k‖ ^ 2)
      atTop (nhds ((1 - r) ^ 2 / 2 + r ^ 2 / 12)) := by
  have hA := (tendsto_const_nhds (x := (1 - r) ^ 2)).mul
    tendsto_vonMangoldtHarmonicSquareSum_div_logSquare
  have hB := (tendsto_const_nhds (x := 2 * (1 - r) * r)).mul
    tendsto_vonMangoldtSelfConvCrossHarmonicSum_div_logCube
  have hC := (tendsto_const_nhds (x := r ^ 2)).mul
    tendsto_vonMangoldtSelfConvHarmonicSquareSum_div_logFourth
  have hlimit := (hA.sub hB).add hC
  have hnormal : Tendsto (fun N : ℕ =>
      (1 - r) ^ 2 *
          (vonMangoldtHarmonicSquareSum N / Real.log N ^ 2) -
        (2 * (1 - r) * r) *
          (vonMangoldtSelfConvCrossHarmonicSum N / Real.log N ^ 3) +
        r ^ 2 *
          (vonMangoldtSelfConvHarmonicSquareSum N / Real.log N ^ 4))
      atTop (nhds ((1 - r) ^ 2 / 2 + r ^ 2 / 12)) := by
    convert hlimit using 1
    all_goals ring_nf
  refine hnormal.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [sum_norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq_eq_momentQuadratic
    (levinsonScaledDetectorParameter r N) (le_refl N)]
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [levinsonScaledDetectorParameter]
  field_simp [hlog]

/-- Unit coefficient plus non-unit energy gives the full short-range limiting energy. -/
theorem tendsto_levinsonLinearMollifiedCriticalDetector_energy (r : ℝ) :
    Tendsto (fun N : ℕ =>
      ∑ k ∈ Finset.Icc 1 N,
        ‖levinsonLinearMollifiedCriticalDetectorCoeff
          (levinsonScaledDetectorParameter r N) N k‖ ^ 2)
      atTop (nhds (1 + (1 - r) ^ 2 / 2 + r ^ 2 / 12)) := by
  have hsum := (tendsto_const_nhds (x := (1 : ℝ))).add
    (tendsto_levinsonLinearMollifiedCriticalDetector_nonunitEnergy r)
  have hsum' : Tendsto (fun N : ℕ => 1 +
      ∑ k ∈ Finset.Icc 2 N,
        ‖levinsonLinearMollifiedCriticalDetectorCoeff
          (levinsonScaledDetectorParameter r N) N k‖ ^ 2)
      atTop (nhds (1 + (1 - r) ^ 2 / 2 + r ^ 2 / 12)) := by
    convert hsum using 1
    all_goals ring_nf
  refine hsum'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp),
    levinsonLinearMollifiedCriticalDetectorCoeff_one]
  · norm_num
  · exact hN

end RHTower.Sieve
