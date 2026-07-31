import GaloisForLFunctions.RHTower.SummableWeightedHeadEntropyCeiling
import GaloisForLFunctions.RHTower.ProjectiveWeightedBoundedDensityQuantile

/-!
# Fixed-water countable recurrence ceiling

An arbitrary feasible water level on a normalized finite head yields a
constructive recurrence of the complete countable packet. The logarithmic
deadline is expressed exactly in the original, unnormalized head weights,
plus the linear coordinate-rounding cost.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/--
An arbitrary feasible water level gives a countable recurrence ceiling in
the original unnormalized head weights.
-/
theorem exists_countableWeightedCoherenceDeadline_headFixedWaterCeiling
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M : ℕ) (hM : 2 ≤ M)
    (hmass : 0 < summableWeightedHeadMass p M)
    (pivot : Fin M)
    {η lam : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hlam : 0 < lam)
    (hwater :
      projectiveWaterMass
          (normalizedWeightedHeadWeight p M) pivot
          (summableWeightedHeadMass p M * lam) ≤ η) :
    ∃ T : ℕ,
      (∀ omega : ℕ → ℝ, ∃ n : ℕ,
        0 < n ∧ n ≤ T ∧
        1 - (summableWeightedHeadMass p M * η +
            2 * ∑' j, p (M + j)) ≤
          ‖summableWeightedPhaseAmplitude p (fun k =>
            Complex.exp
              (Complex.I * ((((n : ℝ) * omega k : ℝ) : ℂ))))‖) ∧
      Real.log (T : ℝ) ≤
        (1 / 2 : ℝ) *
            ∑ i : Fin M, Real.log (max 1 (lam * p i)) +
          (M - 1 : ℕ) *
            Real.log projectivePhaseResolutionConstant := by
  let w : Fin M → ℝ := normalizedWeightedHeadWeight p M
  let level : ℝ := summableWeightedHeadMass p M * lam
  let x : Fin M → ℝ := projectiveWaterScale w pivot level
  have hlevel : 0 < level := mul_pos hmass hlam
  have hw : ∀ i, 0 ≤ w i :=
    normalizedWeightedHeadWeight_nonneg p hp M hmass
  have hwmass : ∑ i, w i = 1 :=
    sum_normalizedWeightedHeadWeight p M hmass
  have hx : ProjectiveWaterFeasible w pivot η x := by
    constructor
    · exact projectiveWaterScale_ge_one w pivot level
    · rw [projectiveWaterScale_reciprocalMass w pivot level hw hlevel]
      simpa only [w, level] using hwater
  have hcanonical :
      projectiveCanonicalWaterEntropyMinimum
          (by omega : 0 < M) w η ≤
        projectiveCoordinateEntropy pivot x := by
    exact
      (projectiveCanonicalWaterEntropyMinimum_le
        (by omega : 0 < M) w η pivot).trans
        (projectiveCanonicalWaterEntropy_le_of_feasible
          w pivot hw hwmass x hx)
  have hpivotNonneg :
      0 ≤ (1 / 2 : ℝ) *
        Real.log (max 1 (level * w pivot)) := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg (le_max_left _ _))
  have hfixed :
      projectiveCoordinateEntropy pivot x ≤
        projectiveFullWaterEntropyAt w level := by
    rw [projectiveCoordinateEntropy_waterScale,
      projectiveWaterEntropyAt_eq_full_sub_pivot]
    exact sub_le_self _ hpivotNonneg
  obtain ⟨T, hreturn, hlog⟩ :=
    exists_countableWeightedCoherenceDeadline_headEntropyCeiling
      p hp hsum htotal M hM hmass hη0 hη1
  refine ⟨T, hreturn, hlog.trans ?_⟩
  calc
    projectiveCanonicalWaterEntropyMinimum
          (by omega : 0 < M) w η +
        (M - 1 : ℕ) *
          Real.log projectivePhaseResolutionConstant ≤
      projectiveFullWaterEntropyAt w level +
        (M - 1 : ℕ) *
          Real.log projectivePhaseResolutionConstant :=
      by
        simpa only [add_comm] using
          add_le_add_right (hcanonical.trans hfixed)
            ((M - 1 : ℕ) *
              Real.log projectivePhaseResolutionConstant)
    _ =
        (1 / 2 : ℝ) *
            ∑ i : Fin M, Real.log (max 1 (lam * p i)) +
          (M - 1 : ℕ) *
            Real.log projectivePhaseResolutionConstant := by
      rw [show level =
          summableWeightedHeadMass p M * lam by rfl,
        show w = normalizedWeightedHeadWeight p M by rfl,
        projectiveFullWaterEntropyAt_normalizedHead_rescale
          p M hmass lam]

end RHTower
