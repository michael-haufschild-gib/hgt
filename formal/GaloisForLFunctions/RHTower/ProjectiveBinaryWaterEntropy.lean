import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherenceMinimax

/-!
# Binary separation of hard support and projective water entropy

The two-level packet `(1-c,c)` already separates hard effective support from
the actual weighted recurrence cost.  When `0 < eta < c ≤ 1/2`, both
coordinates are required at defect `eta`, while the exact water scale is
`eta⁻¹` and its projective entropy is `(1/2) log (c/eta)`.
-/

noncomputable section

namespace RHTower

/-- The ordered two-level probability packet `(1-c,c)`. -/
def binaryProjectiveWeights (c : ℝ) : Fin 2 → ℝ :=
  fun i ↦ if i = 0 then 1 - c else c

theorem binaryProjectiveWeights_nonneg
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ i, 0 ≤ binaryProjectiveWeights c i := by
  intro i
  fin_cases i <;> simp [binaryProjectiveWeights] <;> linarith

@[simp] theorem sum_binaryProjectiveWeights (c : ℝ) :
    ∑ i, binaryProjectiveWeights c i = 1 := by
  simp [Fin.sum_univ_two, binaryProjectiveWeights]

theorem binaryProjectiveWaterMass_zero
    {c eta : ℝ} (hetac : eta ≤ c) :
    projectiveWaterMass (binaryProjectiveWeights c) 0 eta⁻¹ = eta := by
  simp [projectiveWaterMass, Fin.sum_univ_two, binaryProjectiveWeights,
    min_eq_right hetac]

theorem binaryProjectiveWaterMass_one
    {c eta : ℝ} (hetaOther : eta ≤ 1 - c) :
    projectiveWaterMass (binaryProjectiveWeights c) 1 eta⁻¹ = eta := by
  simp [projectiveWaterMass, Fin.sum_univ_two, binaryProjectiveWeights,
    min_eq_right hetaOther]

theorem binaryProjectiveWaterEntropyAt_zero
    {c eta : ℝ} (heta0 : 0 < eta) (hetac : eta ≤ c) :
    projectiveWaterEntropyAt (binaryProjectiveWeights c) 0 eta⁻¹ =
      (1 / 2 : ℝ) * Real.log (c / eta) := by
  have hratio : 1 ≤ eta⁻¹ * c := (one_le_inv_mul₀ heta0).2 hetac
  have hratio' : 1 ≤ c / eta := by
    simpa only [inv_mul_eq_div] using hratio
  simp [projectiveWaterEntropyAt, Fin.sum_univ_two, binaryProjectiveWeights,
    max_eq_right hratio', inv_mul_eq_div]

theorem binaryProjectiveWaterEntropyAt_one
    {c eta : ℝ} (heta0 : 0 < eta) (hetaOther : eta ≤ 1 - c) :
    projectiveWaterEntropyAt (binaryProjectiveWeights c) 1 eta⁻¹ =
      (1 / 2 : ℝ) * Real.log ((1 - c) / eta) := by
  have hratio : 1 ≤ eta⁻¹ * (1 - c) :=
    (one_le_inv_mul₀ heta0).2 hetaOther
  have hratio' : 1 ≤ (1 - c) / eta := by
    simpa only [inv_mul_eq_div] using hratio
  simp [projectiveWaterEntropyAt, Fin.sum_univ_two, binaryProjectiveWeights,
    max_eq_right hratio', inv_mul_eq_div]

/-- Exact two-level minimax clock law.  This is the finite separation theorem
used in the paper: the continuous water entropy, rather than support
cardinality, is the recurrence invariant. -/
theorem binaryUniversalProjectiveWeightedCoherenceTime_entropySandwich
    {c eta : ℝ} (heta0 : 0 < eta) (hetac : eta < c)
    (hc : c ≤ 1 / 2) :
    (1 / 2 : ℝ) * Real.log (c / eta) - Real.pi / 4 - Real.log 4 <
      Real.log (universalProjectiveWeightedCoherenceTime
        (by norm_num) (binaryProjectiveWeights c)
        (binaryProjectiveWeights_nonneg (le_trans heta0.le hetac.le)
          (by linarith))
        (sum_binaryProjectiveWeights c) eta heta0 (by linarith) : ℝ) ∧
    Real.log (universalProjectiveWeightedCoherenceTime
        (by norm_num) (binaryProjectiveWeights c)
        (binaryProjectiveWeights_nonneg (le_trans heta0.le hetac.le)
          (by linarith))
        (sum_binaryProjectiveWeights c) eta heta0 (by linarith) : ℝ) ≤
      (1 / 2 : ℝ) * Real.log (c / eta) +
        Real.log projectivePhaseResolutionConstant := by
  let w : Fin 2 → ℝ := binaryProjectiveWeights c
  have hc0 : 0 ≤ c := le_trans heta0.le hetac.le
  have hc1 : c ≤ 1 := by linarith
  have hw : ∀ i, 0 ≤ w i := binaryProjectiveWeights_nonneg hc0 hc1
  have hmass : ∑ i, w i = 1 := sum_binaryProjectiveWeights c
  have heta1 : eta ≤ 1 := by linarith
  have hetaOther : eta ≤ 1 - c := by linarith
  let H : ℝ := (1 / 2 : ℝ) * Real.log (c / eta)
  let Tmin : ℕ := universalProjectiveWeightedCoherenceTime
    (by norm_num) w hw hmass eta heta0 heta1
  have hdeadline : IsUniversalProjectiveWeightedCoherenceDeadline w eta Tmin :=
    universalProjectiveWeightedCoherenceTime_isDeadline
      (by norm_num) w hw hmass eta heta0 heta1
  have hentropy : ∀ k : Fin 2,
      H ≤ projectiveWaterEntropyAt w k eta⁻¹ := by
    intro k
    fin_cases k
    · change H ≤ projectiveWaterEntropyAt w 0 eta⁻¹
      simp only [H, w]
      rw [binaryProjectiveWaterEntropyAt_zero heta0 hetac.le]
    · change H ≤ projectiveWaterEntropyAt w 1 eta⁻¹
      rw [binaryProjectiveWaterEntropyAt_one heta0 hetaOther]
      have hcOther : c ≤ 1 - c := by linarith
      have hdiv : c / eta ≤ (1 - c) / eta :=
        (div_le_div_iff_of_pos_right heta0).2 hcOther
      have hlog : Real.log (c / eta) ≤ Real.log ((1 - c) / eta) :=
        Real.log_le_log (div_pos (heta0.trans hetac) heta0) hdiv
      simp only [H]
      linarith
  have hlower := projectiveWaterEntropy_sub_cost_lt_log_deadline
    (d := 2) (T := Tmin) (by norm_num) w hw hmass heta0.le heta1
    (fun _ ↦ eta⁻¹) (fun _ ↦ inv_pos.mpr heta0)
    (fun _ ↦ by simp [heta0.ne']) hentropy hdeadline
  have hlevel0 : projectiveWaterMass w 0 eta⁻¹ = eta := by
    simpa only [w] using binaryProjectiveWaterMass_zero hetac.le
  obtain ⟨T, hTdeadline, hTupper⟩ :=
    exists_universalProjectiveWeightedCoherenceDeadline_waterScale
      w 0 hw hmass (inv_pos.mpr heta0) hlevel0
  have hminle : Tmin ≤ T :=
    universalProjectiveWeightedCoherenceTime_le_of_deadline
      (by norm_num) w hw hmass eta heta0 heta1 hTdeadline
  have hTminPos : 0 < (Tmin : ℝ) := by
    exact_mod_cast universalProjectiveWeightedCoherenceTime_pos
      (by norm_num) w hw hmass eta heta0 heta1
  have hTpos : 0 < (T : ℝ) := by
    exact lt_of_lt_of_le hTminPos (by exact_mod_cast hminle)
  have hlogle : Real.log (Tmin : ℝ) ≤ Real.log (T : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hTminPos hTpos (by exact_mod_cast hminle)
  have hwater0 : projectiveWaterEntropyAt w 0 eta⁻¹ = H := by
    simpa only [w, H] using
      binaryProjectiveWaterEntropyAt_zero heta0 hetac.le
  constructor
  · norm_num at hlower
    simpa only [H, Tmin, w] using hlower
  · have : Real.log (Tmin : ℝ) ≤
        H + Real.log projectivePhaseResolutionConstant := by
      calc
        Real.log (Tmin : ℝ) ≤ Real.log (T : ℝ) := hlogle
        _ ≤ projectiveWaterEntropyAt w 0 eta⁻¹ +
              (2 - 1 : ℕ) * Real.log projectivePhaseResolutionConstant := hTupper
        _ = H + Real.log projectivePhaseResolutionConstant := by
          rw [hwater0]
          norm_num
    simpa only [H, Tmin, w] using this

/-- Neither singleton carries mass `1-eta`; the hard effective support is two. -/
def BinaryNeedsBothCoordinates (c eta : ℝ) : Prop :=
  1 - c < 1 - eta ∧ c < 1 - eta

theorem scaledBinary_needsBothCoordinates
    {q eta : ℝ} (heta0 : 0 < eta) (hq : 1 < q)
    (hqeta : q * eta ≤ 1 / 2) :
    BinaryNeedsBothCoordinates (q * eta) eta := by
  constructor
  · have : eta < q * eta := by nlinarith
    linarith
  · have hetaHalf : eta < 1 / 2 := by nlinarith
    linarith

/-- A family with hard effective support two but a defect-independent water
entropy `(1/2) log q`. -/
theorem scaledBinaryUniversalProjectiveWeightedCoherenceTime_entropySandwich
    {q eta : ℝ} (heta0 : 0 < eta) (hq : 1 < q)
    (hqeta : q * eta ≤ 1 / 2) :
    (1 / 2 : ℝ) * Real.log q - Real.pi / 4 - Real.log 4 <
      Real.log (universalProjectiveWeightedCoherenceTime
        (by norm_num) (binaryProjectiveWeights (q * eta))
        (binaryProjectiveWeights_nonneg (mul_nonneg (by linarith) heta0.le)
          (by linarith))
        (sum_binaryProjectiveWeights (q * eta)) eta heta0
          (by nlinarith [mul_pos (sub_pos.mpr hq) heta0]) : ℝ) ∧
    Real.log (universalProjectiveWeightedCoherenceTime
        (by norm_num) (binaryProjectiveWeights (q * eta))
        (binaryProjectiveWeights_nonneg (mul_nonneg (by linarith) heta0.le)
          (by linarith))
        (sum_binaryProjectiveWeights (q * eta)) eta heta0
          (by nlinarith [mul_pos (sub_pos.mpr hq) heta0]) : ℝ) ≤
      (1 / 2 : ℝ) * Real.log q +
        Real.log projectivePhaseResolutionConstant := by
  have hetalt : eta < q * eta := by nlinarith
  have h := binaryUniversalProjectiveWeightedCoherenceTime_entropySandwich
    heta0 hetalt hqeta
  have hratio : q * eta / eta = q := by field_simp
  rwa [hratio] at h

end RHTower
