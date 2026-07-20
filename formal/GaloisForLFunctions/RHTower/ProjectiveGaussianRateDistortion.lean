import GaloisForLFunctions.RHTower.ProjectiveWeightedFloquetRecurrence
import GaloisForLFunctions.RHTower.ProjectiveBinaryWaterEntropy

/-!
# Projective Gaussian rate--distortion law

The anisotropic resolution problem governing weighted projective recurrence
is exactly the reverse-water-filling variational problem for independent
Gaussian modes after one projective pivot is removed.  This file proves the
identification at the level of feasible distortion packets and then states
the recurrence theorem with the rate--distortion value as its single
intrinsic exponent.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Positive distortion allocations for all nonpivot modes, subject to a
total distortion budget.  The pivot allocation is immaterial to the cost and
budget but is kept positive so the scale change is everywhere defined. -/
def ProjectiveGaussianDistortionFeasible {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (eta : ℝ) (D : Fin d → ℝ) : Prop :=
  (∀ j, 0 < D j) ∧ (∀ j, D j ≤ w j) ∧
    (∑ j, if j = k then 0 else D j) ≤ eta

/-- Gaussian rate assigned to a projective distortion packet. -/
def projectiveGaussianRateCost {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (D : Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, if j = k then 0 else Real.log (w j / D j)

/-- Coordinate resolution associated with a distortion allocation. -/
def projectiveScaleOfGaussianDistortion {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (D : Fin d → ℝ) (j : Fin d) : ℝ :=
  if j = k then 1 else w j / D j

/-- Canonical reverse-water-filled Gaussian distortion allocation. -/
def projectiveCanonicalGaussianDistortion {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (eta : ℝ) (j : Fin d) : ℝ :=
  if j = k then w j else
    w j / projectiveWaterScale w k
      (projectiveCanonicalWaterLevel w k eta) j

theorem projectiveScaleOfGaussianDistortion_ge_one
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (D : Fin d → ℝ)
    (hD : ProjectiveGaussianDistortionFeasible w k eta D) :
    ∀ j, 1 ≤ projectiveScaleOfGaussianDistortion w k D j := by
  intro j
  by_cases hjk : j = k
  · simp [projectiveScaleOfGaussianDistortion, hjk]
  · simp only [projectiveScaleOfGaussianDistortion, hjk, ↓reduceIte]
    exact (one_le_div (hD.1 j)).2 (hD.2.1 j)

theorem projectiveScaleOfGaussianDistortion_reciprocalMass
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (D : Fin d → ℝ)
    (hw : ∀ j, 0 < w j) :
    (∑ j, if j = k then 0 else
        w j / projectiveScaleOfGaussianDistortion w k D j) =
      ∑ j, if j = k then 0 else D j := by
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ↓reduceIte, projectiveScaleOfGaussianDistortion]
    field_simp [ne_of_gt (hw j)]

theorem projectiveScaleOfGaussianDistortion_feasible
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {eta : ℝ}
    (D : Fin d → ℝ) (hw : ∀ j, 0 < w j)
    (hD : ProjectiveGaussianDistortionFeasible w k eta D) :
    ProjectiveWaterFeasible w k eta
      (projectiveScaleOfGaussianDistortion w k D) := by
  constructor
  · exact projectiveScaleOfGaussianDistortion_ge_one w k D hD
  · rw [projectiveScaleOfGaussianDistortion_reciprocalMass w k D hw]
    exact hD.2.2

theorem projectiveCoordinateEntropy_scaleOfGaussianDistortion
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (D : Fin d → ℝ) :
    projectiveCoordinateEntropy k
        (projectiveScaleOfGaussianDistortion w k D) =
      projectiveGaussianRateCost w k D := by
  rw [projectiveCoordinateEntropy, projectiveGaussianRateCost]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hjk : j = k <;>
    simp [projectiveScaleOfGaussianDistortion, hjk]

/-- Every admissible Gaussian distortion packet costs at least the canonical
projective water entropy. -/
theorem projectiveCanonicalWaterEntropy_le_gaussianRateCost
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ j, 0 < w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (D : Fin d → ℝ)
    (hD : ProjectiveGaussianDistortionFeasible w k eta D) :
    projectiveCanonicalWaterEntropy w eta k ≤
      projectiveGaussianRateCost w k D := by
  rw [projectiveCanonicalWaterEntropy]
  calc
    projectiveWaterEntropyAt w k
        (projectiveCanonicalWaterLevel w k eta) ≤
      projectiveCoordinateEntropy k
        (projectiveScaleOfGaussianDistortion w k D) :=
      projectiveCanonicalWaterEntropy_le_of_feasible
        w k (fun j ↦ (hw j).le) hmass
        (projectiveScaleOfGaussianDistortion w k D)
        (projectiveScaleOfGaussianDistortion_feasible w k D hw hD)
    _ = projectiveGaussianRateCost w k D :=
      projectiveCoordinateEntropy_scaleOfGaussianDistortion w k D

theorem projectiveCanonicalGaussianDistortion_pos
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (eta : ℝ)
    (hw : ∀ j, 0 < w j) :
    ∀ j, 0 < projectiveCanonicalGaussianDistortion w k eta j := by
  intro j
  by_cases hjk : j = k
  · subst j
    simpa [projectiveCanonicalGaussianDistortion] using hw k
  · simp only [projectiveCanonicalGaussianDistortion, hjk, ↓reduceIte]
    exact div_pos (hw j) (zero_lt_one.trans_le
      (projectiveWaterScale_ge_one w k
        (projectiveCanonicalWaterLevel w k eta) j))

theorem projectiveCanonicalGaussianDistortion_le_weight
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (eta : ℝ)
    (hw : ∀ j, 0 ≤ w j) :
    ∀ j, projectiveCanonicalGaussianDistortion w k eta j ≤ w j := by
  intro j
  by_cases hjk : j = k
  · simp [projectiveCanonicalGaussianDistortion, hjk]
  · simp only [projectiveCanonicalGaussianDistortion, hjk, ↓reduceIte]
    exact div_le_self (hw j)
      (projectiveWaterScale_ge_one w k
        (projectiveCanonicalWaterLevel w k eta) j)

theorem sum_projectiveCanonicalGaussianDistortion_le
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta0 : 0 < eta) :
    (∑ j, if j = k then 0 else
        projectiveCanonicalGaussianDistortion w k eta j) ≤ eta := by
  have hx := projectiveCanonicalWaterScale_feasible
    hd w k hw hmass heta0
  have hsum :
      (∑ j, if j = k then 0 else
          projectiveCanonicalGaussianDistortion w k eta j) =
        ∑ j, if j = k then 0 else
          w j / projectiveWaterScale w k
            (projectiveCanonicalWaterLevel w k eta) j := by
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hjk : j = k <;>
      simp [projectiveCanonicalGaussianDistortion, hjk]
  rw [hsum]
  exact hx.2

theorem projectiveCanonicalGaussianDistortion_feasible
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ j, 0 < w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta0 : 0 < eta) :
    ProjectiveGaussianDistortionFeasible w k eta
      (projectiveCanonicalGaussianDistortion w k eta) := by
  exact ⟨projectiveCanonicalGaussianDistortion_pos w k eta hw,
    projectiveCanonicalGaussianDistortion_le_weight w k eta
      (fun j ↦ (hw j).le),
    sum_projectiveCanonicalGaussianDistortion_le
      hd w k (fun j ↦ (hw j).le) hmass heta0⟩

theorem projectiveScaleOfCanonicalGaussianDistortion
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (eta : ℝ)
    (hw : ∀ j, 0 < w j) :
    projectiveScaleOfGaussianDistortion w k
        (projectiveCanonicalGaussianDistortion w k eta) =
      projectiveWaterScale w k
        (projectiveCanonicalWaterLevel w k eta) := by
  funext j
  by_cases hjk : j = k
  · simp [projectiveScaleOfGaussianDistortion, projectiveWaterScale, hjk]
  · simp only [projectiveScaleOfGaussianDistortion,
      projectiveCanonicalGaussianDistortion, projectiveWaterScale,
      hjk, ↓reduceIte]
    field_simp [ne_of_gt (hw j)]

theorem projectiveGaussianRateCost_canonicalDistortion
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (eta : ℝ)
    (hw : ∀ j, 0 < w j) :
    projectiveGaussianRateCost w k
        (projectiveCanonicalGaussianDistortion w k eta) =
      projectiveCanonicalWaterEntropy w eta k := by
  rw [← projectiveCoordinateEntropy_scaleOfGaussianDistortion,
    projectiveScaleOfCanonicalGaussianDistortion w k eta hw,
    projectiveCoordinateEntropy_waterScale]
  rfl

/-- **Exact projective Gaussian rate--distortion identity.**  The canonical
water allocation attains the Gaussian rate minimum on every pivot fibre. -/
theorem projectiveCanonicalWaterEntropy_isGaussianRateDistortionMinimum
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (k : Fin d)
    (hw : ∀ j, 0 < w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta0 : 0 < eta) :
    ProjectiveGaussianDistortionFeasible w k eta
        (projectiveCanonicalGaussianDistortion w k eta) ∧
      projectiveGaussianRateCost w k
          (projectiveCanonicalGaussianDistortion w k eta) =
        projectiveCanonicalWaterEntropy w eta k ∧
      ∀ D, ProjectiveGaussianDistortionFeasible w k eta D →
        projectiveCanonicalWaterEntropy w eta k ≤
          projectiveGaussianRateCost w k D := by
  refine ⟨projectiveCanonicalGaussianDistortion_feasible
      hd w k hw hmass heta0,
    projectiveGaussianRateCost_canonicalDistortion w k eta hw, ?_⟩
  intro D hD
  exact projectiveCanonicalWaterEntropy_le_gaussianRateCost
    w k hw hmass D hD

/-- Gaussian rate--distortion after optimizing the projective pivot. -/
noncomputable def projectiveGaussianRateDistortionMinimum
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (eta : ℝ) : ℝ :=
  projectiveCanonicalWaterEntropyMinimum hd w eta

/-- The projective rate--distortion value is attained, and it is below the
cost of every feasible distortion packet on every pivot fibre. -/
theorem exists_projectiveGaussianRateDistortion_minimizer
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ)
    (hw : ∀ j, 0 < w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta0 : 0 < eta) :
    ∃ k : Fin d, ∃ D : Fin d → ℝ,
      ProjectiveGaussianDistortionFeasible w k eta D ∧
      projectiveGaussianRateCost w k D =
        projectiveGaussianRateDistortionMinimum hd w eta ∧
      ∀ l : Fin d, ∀ E : Fin d → ℝ,
        ProjectiveGaussianDistortionFeasible w l eta E →
          projectiveGaussianRateDistortionMinimum hd w eta ≤
            projectiveGaussianRateCost w l E := by
  obtain ⟨k, hk⟩ :=
    exists_projectiveCanonicalWaterEntropy_minimizingPivot hd w eta
  let D := projectiveCanonicalGaussianDistortion w k eta
  refine ⟨k, D,
    projectiveCanonicalGaussianDistortion_feasible
      hd w k hw hmass heta0, ?_, ?_⟩
  · rw [projectiveGaussianRateCost_canonicalDistortion w k eta hw,
      hk]
    rfl
  · intro l E hE
    calc
      projectiveGaussianRateDistortionMinimum hd w eta =
          projectiveCanonicalWaterEntropyMinimum hd w eta := rfl
      _ ≤ projectiveCanonicalWaterEntropy w eta l :=
        projectiveCanonicalWaterEntropyMinimum_le hd w eta l
      _ ≤ projectiveGaussianRateCost w l E :=
        projectiveCanonicalWaterEntropy_le_gaussianRateCost
          w l hw hmass E hE

/-- A feasible distortion packet attaining the lighter-mode binary cost. -/
def binaryProjectiveGaussianDistortion (c eta : ℝ) : Fin 2 → ℝ :=
  fun i ↦ if i = 0 then 1 - c else eta

theorem binaryProjectiveWeights_pos
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∀ i, 0 < binaryProjectiveWeights c i := by
  intro i
  fin_cases i <;> simp [binaryProjectiveWeights] <;> linarith

theorem binaryProjectiveGaussianDistortion_feasible
    {c eta : ℝ} (heta0 : 0 < eta) (hetac : eta ≤ c)
    (hc1 : c < 1) :
    ProjectiveGaussianDistortionFeasible
      (binaryProjectiveWeights c) 0 eta
      (binaryProjectiveGaussianDistortion c eta) := by
  constructor
  · intro j
    fin_cases j <;>
      simp [binaryProjectiveGaussianDistortion] <;> linarith
  constructor
  · intro j
    fin_cases j
    · simp [binaryProjectiveGaussianDistortion, binaryProjectiveWeights]
    · simp [binaryProjectiveGaussianDistortion, binaryProjectiveWeights,
        hetac]
  · simp [Fin.sum_univ_two, binaryProjectiveGaussianDistortion]

theorem binary_projectiveGaussianRateCost_ge
    {c eta : ℝ} (heta0 : 0 < eta) (hceta : eta < c)
    (hc : c ≤ 1 / 2) (k : Fin 2) (D : Fin 2 → ℝ)
    (hD : ProjectiveGaussianDistortionFeasible
      (binaryProjectiveWeights c) k eta D) :
    (1 / 2 : ℝ) * Real.log (c / eta) ≤
      projectiveGaussianRateCost (binaryProjectiveWeights c) k D := by
  fin_cases k
  · have hD1eta : D 1 ≤ eta := by
      simpa [Fin.sum_univ_two] using hD.2.2
    have hratio : c / eta ≤ c / D 1 :=
      div_le_div_of_nonneg_left (le_trans heta0.le hceta.le)
        (hD.1 1) hD1eta
    have hlog : Real.log (c / eta) ≤ Real.log (c / D 1) :=
      Real.log_le_log (div_pos (heta0.trans hceta) heta0) hratio
    simpa [projectiveGaussianRateCost, Fin.sum_univ_two,
      binaryProjectiveWeights] using
      (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 1 / 2))
  · have hD0eta : D 0 ≤ eta := by
      simpa [Fin.sum_univ_two] using hD.2.2
    have hratio1 : c / eta ≤ c / D 0 :=
      div_le_div_of_nonneg_left (le_trans heta0.le hceta.le)
        (hD.1 0) hD0eta
    have hcother : c ≤ 1 - c := by linarith
    have hratio2 : c / D 0 ≤ (1 - c) / D 0 :=
      (div_le_div_iff_of_pos_right (hD.1 0)).2 hcother
    have hlog : Real.log (c / eta) ≤ Real.log ((1 - c) / D 0) :=
      Real.log_le_log (div_pos (heta0.trans hceta) heta0)
        (hratio1.trans hratio2)
    simpa [projectiveGaussianRateCost, Fin.sum_univ_two,
      binaryProjectiveWeights] using
      (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 1 / 2))

/-- **Exact binary projective rate--distortion value.** -/
theorem binary_projectiveGaussianRateDistortionMinimum
    {c eta : ℝ} (heta0 : 0 < eta) (hceta : eta < c)
    (hc : c ≤ 1 / 2) :
    projectiveGaussianRateDistortionMinimum (by norm_num)
        (binaryProjectiveWeights c) eta =
      (1 / 2 : ℝ) * Real.log (c / eta) := by
  have hc0 : 0 < c := heta0.trans hceta
  have hc1 : c < 1 := by linarith
  have hw := binaryProjectiveWeights_pos hc0 hc1
  have hD := binaryProjectiveGaussianDistortion_feasible
    heta0 hceta.le hc1
  apply le_antisymm
  · calc
      projectiveGaussianRateDistortionMinimum (by norm_num)
          (binaryProjectiveWeights c) eta =
          projectiveCanonicalWaterEntropyMinimum (by norm_num)
            (binaryProjectiveWeights c) eta := rfl
      _ ≤ projectiveCanonicalWaterEntropy
          (binaryProjectiveWeights c) eta 0 :=
        projectiveCanonicalWaterEntropyMinimum_le
          (by norm_num) (binaryProjectiveWeights c) eta 0
      _ ≤ projectiveGaussianRateCost (binaryProjectiveWeights c) 0
          (binaryProjectiveGaussianDistortion c eta) :=
        projectiveCanonicalWaterEntropy_le_gaussianRateCost
          (binaryProjectiveWeights c) 0 hw
          (sum_binaryProjectiveWeights c)
          (binaryProjectiveGaussianDistortion c eta) hD
      _ = (1 / 2 : ℝ) * Real.log (c / eta) := by
        simp [projectiveGaussianRateCost, Fin.sum_univ_two,
          binaryProjectiveWeights, binaryProjectiveGaussianDistortion]
  · obtain ⟨k, D, hD', hcost, _hglobal⟩ :=
      exists_projectiveGaussianRateDistortion_minimizer
        (by norm_num) (binaryProjectiveWeights c) hw
        (sum_binaryProjectiveWeights c) heta0
    have hlower := binary_projectiveGaussianRateCost_ge
      heta0 hceta hc k D hD'
    rw [hcost] at hlower
    exact hlower

/-- **Minimax recurrence--rate-distortion law.**  The least worst-spectrum
pure-state Floquet recurrence deadline has logarithm equal, up to explicit
dimension-only costs, to the minimum Gaussian rate--distortion value after
projective gauge removal. -/
theorem universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ j, 0 < w j) (hmass : ∑ j, w j = 1)
    (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    projectiveGaussianRateDistortionMinimum (by omega) w eta -
        (Real.pi / 4) * (d - 1 : ℕ) - Real.log (2 * (d : ℝ)) <
      Real.log (universalWeightedFloquetFidelityRecurrenceTime
        hd w (fun j ↦ (hw j).le) hmass eta heta0 heta1 : ℝ) ∧
    Real.log (universalWeightedFloquetFidelityRecurrenceTime
        hd w (fun j ↦ (hw j).le) hmass eta heta0 heta1 : ℝ) ≤
      projectiveGaussianRateDistortionMinimum (by omega) w eta +
        (d - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := by
  simpa only [projectiveGaussianRateDistortionMinimum] using
    universalWeightedFloquetFidelityRecurrenceTime_entropySandwich
    hd w (fun j ↦ (hw j).le) hmass eta heta0 heta1

/-- Finite constant-free form of the recurrence--rate-distortion law. -/
theorem universalWeightedFloquetFidelityRecurrenceTime_rateDistortionNormalized
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ j, 0 < w j) (hmass : ∑ j, w j = 1)
    {eta eps : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hR : 0 < projectiveGaussianRateDistortionMinimum (by omega) w eta)
    (hlower : projectiveWaterLowerCarrierCost d ≤
      eps * projectiveGaussianRateDistortionMinimum (by omega) w eta)
    (hupper : projectiveWaterUpperCarrierCost d ≤
      eps * projectiveGaussianRateDistortionMinimum (by omega) w eta) :
    1 - eps <
        Real.log (universalWeightedFloquetFidelityRecurrenceTime
          hd w (fun j ↦ (hw j).le) hmass eta heta0 heta1 : ℝ) /
          projectiveGaussianRateDistortionMinimum (by omega) w eta ∧
      Real.log (universalWeightedFloquetFidelityRecurrenceTime
          hd w (fun j ↦ (hw j).le) hmass eta heta0 heta1 : ℝ) /
          projectiveGaussianRateDistortionMinimum (by omega) w eta ≤
        1 + eps := by
  simpa only [universalWeightedFloquetFidelityRecurrenceTime,
    projectiveGaussianRateDistortionMinimum] using
    universalProjectiveWeightedCoherenceTime_normalized
      hd w (fun j ↦ (hw j).le) hmass heta0 heta1 hR hlower hupper

end RHTower
