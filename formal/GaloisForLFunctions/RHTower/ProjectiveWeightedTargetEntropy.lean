import GaloisForLFunctions.RHTower.ProjectiveWaterFillingOptimizer

/-!
# Entropy bound for weighted projective coherence targets

The water level controls not only the deterministic recurrence ceiling but
also the Haar size of the same weighted coherence target.  This file proves
the coordinatewise Laplace envelope needed for the matching avoidance bound.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The one-circle chord Laplace transform never exceeds one at a
nonnegative parameter. -/
theorem circleChordExponentialMoment_le_one
    {u : ℝ} (hu : 0 ≤ u) :
    circleChordExponentialMoment u ≤ 1 := by
  rw [circleChordExponentialMoment]
  have hfcont : Continuous (fun z : UnitAddCircle ↦
      Real.exp (-u * ‖fourier 1 z - 1‖ ^ 2)) := by
    fun_prop
  have hfint : Integrable (fun z : UnitAddCircle ↦
      Real.exp (-u * ‖fourier 1 z - 1‖ ^ 2)) := by
    rw [← integrableOn_univ]
    exact ContinuousOn.integrableOn_compact isCompact_univ hfcont.continuousOn
  have hone : Integrable (fun _z : UnitAddCircle ↦ (1 : ℝ)) := integrable_const 1
  calc
    (∫ z : UnitAddCircle,
        Real.exp (-u * ‖fourier 1 z - 1‖ ^ 2)) ≤
        ∫ _z : UnitAddCircle, (1 : ℝ) := by
      apply integral_mono_ae hfint hone
      exact Filter.Eventually.of_forall fun z ↦
        Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (sq_nonneg _))
    _ = 1 := by
      rw [integral_const]
      rw [measureReal_def, UnitAddCircle.measure_univ]
      norm_num

/-- At the Chernoff scale `π λ / 16`, one weighted circle coordinate is
bounded by the exponential of minus its water-filling entropy contribution. -/
theorem circleChordExponentialMoment_waterEnvelope
    {a lam : ℝ} (ha : 0 ≤ a) (hlam : 0 < lam) :
    circleChordExponentialMoment ((Real.pi / 16) * lam * a) ≤
      Real.exp (-(1 / 2 : ℝ) * Real.log (max 1 (lam * a))) := by
  by_cases h : lam * a ≤ 1
  · rw [max_eq_left h, Real.log_one, mul_zero, Real.exp_zero]
    exact circleChordExponentialMoment_le_one
      (mul_nonneg (mul_nonneg (by positivity) hlam.le) ha)
  · have hy : 1 < lam * a := lt_of_not_ge h
    have ha0 : 0 < a := by
      by_contra ha0
      have : a = 0 := le_antisymm (le_of_not_gt ha0) ha
      subst a
      norm_num at hy
    have hu : 0 < (Real.pi / 16) * lam * a := by positivity
    have hgauss := circleChordExponentialMoment_le_gaussian hu
    have hinside :
        Real.pi / (16 * ((Real.pi / 16) * lam * a)) =
          (lam * a)⁻¹ := by
      field_simp [Real.pi_ne_zero, hlam.ne', ha0.ne']
    rw [hinside] at hgauss
    have hy0 : 0 < lam * a := mul_pos hlam ha0
    have hsqrt :
        Real.sqrt ((lam * a)⁻¹) =
          Real.exp (-(1 / 2 : ℝ) * Real.log (lam * a)) := by
      rw [Real.sqrt_inv]
      have hroot :
          Real.sqrt (lam * a) =
            Real.exp (Real.log (lam * a) / 2) := by
        rw [← Real.log_sqrt hy0.le,
          Real.exp_log (Real.sqrt_pos.mpr hy0)]
      rw [hroot, ← Real.exp_neg]
      congr 1
      ring
    rw [max_eq_right hy.le]
    rw [hsqrt] at hgauss
    exact hgauss

/-- Product form of the weighted water-filling Laplace envelope. -/
theorem prod_circleChordExponentialMoment_waterEnvelope
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) {lam : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hlam : 0 < lam) :
    (∏ j, if j = k then 1 else
        circleChordExponentialMoment ((Real.pi / 16) * lam * w j)) ≤
      Real.exp (-projectiveWaterEntropyAt w k lam) := by
  have hprod :
      (∏ j, if j = k then 1 else
          circleChordExponentialMoment ((Real.pi / 16) * lam * w j)) ≤
        ∏ j, if j = k then 1 else
          Real.exp (-(1 / 2 : ℝ) *
            Real.log (max 1 (lam * w j))) := by
    apply Finset.prod_le_prod
    · intro j _hj
      by_cases hjk : j = k
      · simp [hjk]
      · simp only [hjk, ↓reduceIte]
        exact circleChordExponentialMoment_nonneg _
    · intro j _hj
      by_cases hjk : j = k
      · simp [hjk]
      · simp only [hjk, ↓reduceIte]
        exact circleChordExponentialMoment_waterEnvelope (hw j) hlam
  calc
    (∏ j, if j = k then 1 else
        circleChordExponentialMoment ((Real.pi / 16) * lam * w j)) ≤
        ∏ j, if j = k then 1 else
          Real.exp (-(1 / 2 : ℝ) *
            Real.log (max 1 (lam * w j))) := hprod
    _ = Real.exp (-projectiveWaterEntropyAt w k lam) := by
      have hfactor (j : Fin d) :
          (if j = k then 1 else
              Real.exp (-(1 / 2 : ℝ) *
                Real.log (max 1 (lam * w j)))) =
            Real.exp (if j = k then 0 else
              -(1 / 2 : ℝ) * Real.log (max 1 (lam * w j))) := by
        by_cases hjk : j = k <;> simp [hjk]
      rw [show
        (∏ j, if j = k then 1 else
            Real.exp (-(1 / 2 : ℝ) *
              Real.log (max 1 (lam * w j)))) =
          ∏ j, Real.exp (if j = k then 0 else
            -(1 / 2 : ℝ) * Real.log (max 1 (lam * w j))) by
          apply Finset.prod_congr rfl
          intro j _hj
          exact hfactor j]
      rw [← Real.exp_sum]
      rw [projectiveWaterEntropyAt]
      congr 1
      calc
        (∑ j, if j = k then 0 else
            -(1 / 2 : ℝ) * Real.log (max 1 (lam * w j))) =
            ∑ j, (-(1 / 2 : ℝ)) *
              (if j = k then 0 else
                Real.log (max 1 (lam * w j))) := by
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hjk : j = k <;> simp [hjk]
        _ = (-(1 / 2 : ℝ)) *
            ∑ j, if j = k then 0 else
              Real.log (max 1 (lam * w j)) := by
          rw [Finset.mul_sum]
        _ = -((1 / 2 : ℝ) *
            ∑ j, if j = k then 0 else
              Real.log (max 1 (lam * w j))) := by ring

/-- A family of positive water scales with a common entropy floor gives an
explicit Haar bound for the full weighted projective coherence target.  The
same scale appears in the Chernoff cost and in the coordinate entropy; no
equal-weight or active-support hypothesis is used. -/
theorem measureReal_torusProjectiveWeightedCoherenceTarget_waterEntropy_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η H : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (lam : Fin d → ℝ) (hlam : ∀ k, 0 < lam k)
    (hbudget : ∀ k, lam k * η ≤ (d - 1 : ℕ))
    (hentropy : ∀ k, H ≤ projectiveWaterEntropyAt w k (lam k)) :
    volume.real (torusProjectiveWeightedCoherenceTarget w η) ≤
      (d : ℝ) * Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) := by
  have hbase := measureReal_torusProjectiveWeightedCoherenceTarget_le
    w hw hmass hη0 hη1 (fun k ↦ (Real.pi / 16) * lam k)
    (fun k ↦ mul_pos (div_pos Real.pi_pos (by norm_num)) (hlam k))
  have hterm : ∀ k : Fin d,
      Real.exp (4 * ((Real.pi / 16) * lam k) * η) *
          (∏ j, if j = k then 1 else
            circleChordExponentialMoment
              ((Real.pi / 16) * lam k * w j)) ≤
        Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) := by
    intro k
    have hprod := prod_circleChordExponentialMoment_waterEnvelope
      w k (hw := hw) (hlam k)
    have hcost :
        4 * ((Real.pi / 16) * lam k) * η ≤
          (Real.pi / 4) * (d - 1 : ℕ) := by
      have hpi : 0 ≤ Real.pi / 4 := by positivity
      have hscaled := mul_le_mul_of_nonneg_left (hbudget k) hpi
      convert hscaled using 1 <;> ring
    calc
      Real.exp (4 * ((Real.pi / 16) * lam k) * η) *
          (∏ j, if j = k then 1 else
            circleChordExponentialMoment
              ((Real.pi / 16) * lam k * w j)) ≤
          Real.exp (4 * ((Real.pi / 16) * lam k) * η) *
            Real.exp (-projectiveWaterEntropyAt w k (lam k)) := by
        exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = Real.exp (4 * ((Real.pi / 16) * lam k) * η -
            projectiveWaterEntropyAt w k (lam k)) := by
        rw [← Real.exp_add]
        congr 1
      _ ≤ Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) := by
        apply Real.exp_le_exp.mpr
        exact sub_le_sub hcost (hentropy k)
  calc
    volume.real (torusProjectiveWeightedCoherenceTarget w η) ≤
        ∑ k, Real.exp (4 * ((Real.pi / 16) * lam k) * η) *
          ∏ j, if j = k then 1 else
            circleChordExponentialMoment
              ((Real.pi / 16) * lam k * w j) := hbase
    _ ≤ ∑ _k : Fin d,
        Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) := by
      exact Finset.sum_le_sum fun k _hk ↦ hterm k
    _ = (d : ℝ) * Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-- The exact water-mass equation automatically supplies the active-coordinate
budget used by the preceding Haar theorem. -/
theorem measureReal_torusProjectiveWeightedCoherenceTarget_waterLevel_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η H : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (lam : Fin d → ℝ) (hlam : ∀ k, 0 < lam k)
    (hlevel : ∀ k, projectiveWaterMass w k (lam k) = η)
    (hentropy : ∀ k, H ≤ projectiveWaterEntropyAt w k (lam k)) :
    volume.real (torusProjectiveWeightedCoherenceTarget w η) ≤
      (d : ℝ) * Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) := by
  exact measureReal_torusProjectiveWeightedCoherenceTarget_waterEntropy_le
    w hw hmass hη0 hη1 lam hlam
      (fun k ↦ waterLevel_mul_eta_le_card_sub_one
        w k (hlam k) (hlevel k)) hentropy

end RHTower
