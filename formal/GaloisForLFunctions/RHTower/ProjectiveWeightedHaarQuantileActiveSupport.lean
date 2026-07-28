import GaloisForLFunctions.RHTower.ProjectiveWeightedFloquetRecurrence

/-!
# Haar quantiles and selected-support projective recurrence

The coarse minimax floor discards two pieces of information already present
in the weighted Haar argument: the measure of all early-return phase packets
and the pivot-specific canonical water scale.  The first half of this file
retains both.

The constructive ceiling can also ignore a chosen tail instead of resolving
every nonpivot coordinate.  The tail pays its exact worst-case amplitude loss,
while only selected coordinates pay product-box resolution.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-! ## Exact Haar water budget -/

/-- Pivot-resolved Haar budget at the canonical water scales. -/
def projectiveCanonicalHaarWaterBudget {d : ℕ}
    (w : Fin d → ℝ) (η : ℝ) : ℝ :=
  ∑ k, Real.exp (
    (Real.pi / 4) * (projectiveCanonicalWaterLevel w k η * η) -
      projectiveCanonicalWaterEntropy w η k)

theorem projectiveCanonicalHaarWaterBudget_pos
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (η : ℝ) :
    0 < projectiveCanonicalHaarWaterBudget w η := by
  rw [projectiveCanonicalHaarWaterBudget]
  exact Finset.sum_pos'
    (fun k _hk ↦ (Real.exp_pos _).le)
    ⟨⟨0, hd⟩, Finset.mem_univ _, Real.exp_pos _⟩

/-- The weighted projective target is bounded by the exact sum of its
pivot-specific canonical water envelopes. -/
theorem measureReal_torusProjectiveWeightedCoherenceTarget_canonicalHaarWater_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η : ℝ} (hη1 : η ≤ 1) :
    volume.real (torusProjectiveWeightedCoherenceTarget w η) ≤
      projectiveCanonicalHaarWaterBudget w η := by
  let lam : Fin d → ℝ := fun k ↦ projectiveCanonicalWaterLevel w k η
  have hbase := measureReal_torusProjectiveWeightedCoherenceTarget_le
    w hw hmass hη1 (fun k ↦ (Real.pi / 16) * lam k)
    (fun k ↦ mul_pos (by positivity) (projectiveCanonicalWaterLevel_pos w k η))
  have hterm : ∀ k : Fin d,
      Real.exp (4 * ((Real.pi / 16) * lam k) * η) *
          (∏ j, if j = k then 1 else
            circleChordExponentialMoment
              ((Real.pi / 16) * lam k * w j)) ≤
        Real.exp ((Real.pi / 4) * (lam k * η) -
          projectiveCanonicalWaterEntropy w η k) := by
    intro k
    have hprod := prod_circleChordExponentialMoment_waterEnvelope
      w k (hw := hw) (projectiveCanonicalWaterLevel_pos w k η)
    calc
      Real.exp (4 * ((Real.pi / 16) * lam k) * η) *
          (∏ j, if j = k then 1 else
            circleChordExponentialMoment
              ((Real.pi / 16) * lam k * w j)) ≤
          Real.exp (4 * ((Real.pi / 16) * lam k) * η) *
            Real.exp (-projectiveWaterEntropyAt w k (lam k)) := by
        exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = Real.exp ((Real.pi / 4) * (lam k * η) -
          projectiveCanonicalWaterEntropy w η k) := by
        rw [← Real.exp_add]
        simp only [projectiveCanonicalWaterEntropy]
        congr 1
        ring
  calc
    volume.real (torusProjectiveWeightedCoherenceTarget w η) ≤
        ∑ k, Real.exp (4 * ((Real.pi / 16) * lam k) * η) *
          ∏ j, if j = k then 1 else
            circleChordExponentialMoment
              ((Real.pi / 16) * lam k * w j) := hbase
    _ ≤ ∑ k, Real.exp ((Real.pi / 4) * (lam k * η) -
          projectiveCanonicalWaterEntropy w η k) :=
      Finset.sum_le_sum fun k _hk ↦ hterm k
    _ = projectiveCanonicalHaarWaterBudget w η := by
      rw [projectiveCanonicalHaarWaterBudget]

/-- **Haar-quantile recurrence law.**  The fraction of phase packets hitting
the weighted recurrence target through the first `N` clocks is at most `N`
times the exact canonical Haar water budget. -/
theorem measureReal_torusProjectiveWeightedCoherenceHitUnion_canonicalHaarWater_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η : ℝ} (hη1 : η ≤ 1) :
    volume.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
      (N : ℝ) * projectiveCanonicalHaarWaterBudget w η := by
  exact (measureReal_torusProjectiveWeightedCoherenceHitUnion_le w N η).trans
    (mul_le_mul_of_nonneg_left
      (measureReal_torusProjectiveWeightedCoherenceTarget_canonicalHaarWater_le
        w hw hmass hη1)
      (Nat.cast_nonneg N))

theorem measurableSet_torusProjectiveWeightedCoherenceHitUnion
    {d : ℕ} (w : Fin d → ℝ) (N : ℕ) (η : ℝ) :
    MeasurableSet (torusProjectiveWeightedCoherenceHitUnion w N η) := by
  rw [torusProjectiveWeightedCoherenceHitUnion]
  apply MeasurableSet.iUnion
  intro n
  exact (measurableSet_torusProjectiveWeightedCoherenceTarget w η).preimage
    (Measure.measurePreserving_zsmul
      (G := Fin d → UnitAddCircle) volume (by omega)).measurable

/-- Complement form of the Haar quantile: this much Haar mass avoids the
recurrence target through every positive clock up to `N`. -/
theorem one_sub_canonicalHaarWaterBudget_le_measureReal_avoidance
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η : ℝ} (hη1 : η ≤ 1) :
    1 - (N : ℝ) * projectiveCanonicalHaarWaterBudget w η ≤
      volume.real
        (torusProjectiveWeightedCoherenceHitUnion w N η)ᶜ := by
  rw [measureReal_compl
    (measurableSet_torusProjectiveWeightedCoherenceHitUnion w N η),
    measureReal_torus_univ]
  exact sub_le_sub_left
    (measureReal_torusProjectiveWeightedCoherenceHitUnion_canonicalHaarWater_le
      w hw hmass N hη1)
    1

theorem one_sub_alpha_le_measureReal_avoidance_of_canonicalHaarWaterBudget
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η α : ℝ} (hη1 : η ≤ 1)
    (hbudget :
      (N : ℝ) * projectiveCanonicalHaarWaterBudget w η ≤ α) :
    1 - α ≤ volume.real
      (torusProjectiveWeightedCoherenceHitUnion w N η)ᶜ := by
  exact (sub_le_sub_left hbudget 1).trans
    (one_sub_canonicalHaarWaterBudget_le_measureReal_avoidance
      w hw hmass N hη1)

/-- The previous full-support target budget is the worst-pivot envelope of
the exact canonical Haar water budget. -/
theorem projectiveCanonicalHaarWaterBudget_le_projectiveWaterTargetBudget
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    {η : ℝ} (hη1 : η ≤ 1) :
    projectiveCanonicalHaarWaterBudget w η ≤
      projectiveWaterTargetBudget d
        (projectiveCanonicalWaterEntropyMinimum (by omega) w η) := by
  let H : ℝ := projectiveCanonicalWaterEntropyMinimum (by omega) w η
  have hterm : ∀ k : Fin d,
      Real.exp ((Real.pi / 4) *
          (projectiveCanonicalWaterLevel w k η * η) -
          projectiveCanonicalWaterEntropy w η k) ≤
        Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) := by
    intro k
    apply Real.exp_le_exp.mpr
    apply sub_le_sub
    · exact mul_le_mul_of_nonneg_left
        (projectiveCanonicalWaterLevel_mul_eta_le_card_sub_one
          hd w k hη1)
        (by positivity)
    · exact projectiveCanonicalWaterEntropyMinimum_le
        (by omega) w η k
  calc
    projectiveCanonicalHaarWaterBudget w η =
        ∑ k, Real.exp ((Real.pi / 4) *
          (projectiveCanonicalWaterLevel w k η * η) -
          projectiveCanonicalWaterEntropy w η k) := rfl
    _ ≤ ∑ _k : Fin d,
        Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) :=
      Finset.sum_le_sum fun k _hk ↦ hterm k
    _ = projectiveWaterTargetBudget d H := by
      rw [projectiveWaterTargetBudget]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-! ## Selected-support constructive recurrence -/

/-- Total nonpivot weight whose phases will not be synchronized. -/
def projectiveDiscardedWeight {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (A : Finset (Fin d)) : ℝ :=
  ∑ i, if i = k ∨ i ∈ A then 0 else w i

/-- Coordinate resolution one off the selected set, and the usual anisotropic
resolution on it. -/
def projectiveSelectedPhaseResolution {d : ℕ}
    (A : Finset (Fin d)) (k : Fin d) (x : Fin d → ℝ) (i : Fin d) : ℕ :=
  if i ∈ A then projectivePhaseResolution k x i else 1

/-- Water entropy carried only by selected coordinates. -/
def projectiveSelectedCoordinateEntropy {d : ℕ}
    (A : Finset (Fin d)) (x : Fin d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, if i ∈ A then Real.log (x i) else 0

/-- Total amplitude defect assigned to a selected reciprocal profile. -/
def projectiveSelectedWaterDefect {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (A : Finset (Fin d))
    (x : Fin d → ℝ) : ℝ :=
  ∑ i, if i = k then 0 else
    if i ∈ A then w i / x i else 2 * w i

/-- Selected coordinates pay reciprocal quadratic distortion; every
discarded coordinate pays its exact worst-case amplitude loss `2 w_i`. -/
def ProjectiveSelectedWaterFeasible {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (A : Finset (Fin d))
    (η : ℝ) (x : Fin d → ℝ) : Prop :=
  k ∉ A ∧
    (∀ i, 1 ≤ x i) ∧
    projectiveSelectedWaterDefect w k A x ≤ η

theorem projectiveSelectedWaterDefect_eq_selected_add_discarded
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (A : Finset (Fin d))
    (x : Fin d → ℝ) (hkA : k ∉ A) :
    projectiveSelectedWaterDefect w k A x =
      (∑ i, if i ∈ A then w i / x i else 0) +
        2 * projectiveDiscardedWeight w k A := by
  rw [projectiveSelectedWaterDefect, projectiveDiscardedWeight,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hik : i = k
  · subst i
    simp [hkA]
  · by_cases hiA : i ∈ A <;> simp [hik, hiA]

theorem projectiveSelectedPhaseResolution_pos
    {d : ℕ} (A : Finset (Fin d)) (k : Fin d) (x : Fin d → ℝ)
    (hx : ∀ i, 1 ≤ x i) (i : Fin d) :
    0 < projectiveSelectedPhaseResolution A k x i := by
  by_cases hiA : i ∈ A
  · rw [projectiveSelectedPhaseResolution, if_pos hiA]
    exact projectivePhaseResolution_pos k x hx i
  · simp [projectiveSelectedPhaseResolution, hiA]

/-- Defect supplied by the selected rounded resolutions. -/
def projectiveSelectedRoundedDefect {d : ℕ}
    (w : Fin d → ℝ) (k : Fin d) (A : Finset (Fin d))
    (x : Fin d → ℝ) : ℝ :=
  ∑ i, if i = k then 0 else if i ∈ A then
    w i * ((2 * Real.pi /
      (projectiveSelectedPhaseResolution A k x i : ℝ)) ^ 2 / 2)
    else 2 * w i

theorem projectiveSelectedRoundedDefect_le_waterDefect
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d) (A : Finset (Fin d))
    (x : Fin d → ℝ) (hx : ∀ i, 1 ≤ x i)
    (hw : ∀ i, 0 ≤ w i) :
    projectiveSelectedRoundedDefect w k A x ≤
      projectiveSelectedWaterDefect w k A x := by
  rw [projectiveSelectedRoundedDefect, projectiveSelectedWaterDefect]
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hik : i = k
  · simp [hik]
  · by_cases hiA : i ∈ A
    · simp only [hik, hiA, ↓reduceIte, projectiveSelectedPhaseResolution]
      simpa only [hik, ↓reduceIte] using
        projectivePhaseResolution_defect_le_reciprocal
          k x w hx hw i
    · simp [hik, hiA]

/-- Hybrid phase floor: selected coordinates use quadratic approximation,
whereas every discarded unit phasor is bounded only by real part `-1`. -/
theorem nonnegative_weighted_phaseSum_norm_floor_of_selected_approximation
    {d : ℕ} (n : ℕ) (ω w : Fin d → ℝ)
    (A : Finset (Fin d)) (k : Fin d) (Q : Fin d → ℕ)
    (r : Fin d → ℤ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1)
    (hphase : ∀ i, i ∈ A →
      |(n : ℝ) * (ω i - ω k) - 2 * Real.pi * r i| ≤
        2 * Real.pi / (Q i : ℝ)) :
    1 - (∑ i, if i = k then 0 else if i ∈ A then
        w i * ((2 * Real.pi / (Q i : ℝ)) ^ 2 / 2)
      else 2 * w i) ≤
      ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ))‖ := by
  let e : Fin d → ℝ := fun i ↦ 2 * Real.pi / (Q i : ℝ)
  let c : Fin d → ℝ := fun i ↦
    if i = k then 1 else if i ∈ A then 1 - e i ^ 2 / 2 else -1
  have he : ∀ i, 0 ≤ e i := by
    intro i
    dsimp only [e]
    positivity
  have hterm : ∀ i : Fin d,
      c i * w i ≤
        ((w i : ℂ) * Complex.exp
          (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ))).re := by
    intro i
    by_cases hik : i = k
    · subst i
      simp [c]
    · by_cases hiA : i ∈ A
      · have hcos :=
          one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real
            ((n : ℝ) * (ω i - ω k)) (e i) (r i) (he i)
            (by simpa only [e] using hphase i hiA)
        simpa only [c, hik, hiA, ↓reduceIte, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
          sub_zero, mul_comm] using
            mul_le_mul_of_nonneg_right hcos (hw i)
      · have hcos : -1 ≤
            (Complex.exp (Complex.I *
              (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ))).re := by
          rw [show Complex.I *
              (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ) =
            ((((n : ℝ) * (ω i - ω k) : ℝ) : ℂ) * Complex.I) by ring,
            Complex.exp_ofReal_mul_I_re]
          exact Real.neg_one_le_cos _
        simpa only [c, hik, hiA, ↓reduceIte, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
          sub_zero, mul_comm] using
            mul_le_mul_of_nonneg_right hcos (hw i)
  calc
    1 - (∑ i, if i = k then 0 else if i ∈ A then
        w i * ((2 * Real.pi / (Q i : ℝ)) ^ 2 / 2)
      else 2 * w i) =
        ∑ i, c i * w i := by
      rw [← hmass, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hik : i = k
      · subst i
        simp [c]
      · by_cases hiA : i ∈ A <;> simp [c, e, hik, hiA] <;> ring
    _ ≤ ∑ i, ((w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ))).re :=
      Finset.sum_le_sum fun i _hi ↦ hterm i
    _ = (∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ))).re := by
      exact (Complex.re_sum (s := Finset.univ)
        (fun i ↦ (w i : ℂ) * Complex.exp
          (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ)))).symm
    _ ≤ ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ))‖ :=
      Complex.re_le_norm _

/-- **Selected-support projective recurrence.**  Only the chosen coordinates
are synchronized.  The remaining tail contributes its exact worst-case
amplitude defect and no product-box dimension. -/
theorem exists_projective_nonnegative_weighted_phaseSum_recurrence_selected
    {d : ℕ} (ω w : Fin d → ℝ) (A : Finset (Fin d)) (k : Fin d)
    {η : ℝ} (x : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hx : ProjectiveSelectedWaterFeasible w k A η x) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ ∏ i, projectiveSelectedPhaseResolution A k x i ∧
      1 - η ≤
        ‖∑ i, (w i : ℂ) * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ := by
  let Q : Fin d → ℕ := projectiveSelectedPhaseResolution A k x
  have hQ : ∀ i, 0 < Q i :=
    projectiveSelectedPhaseResolution_pos A k x hx.2.1
  obtain ⟨n, hn0, hnQ, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_anisotropic
      (fun i ↦ ω i - ω k) Q hQ
  have hfloor :=
    nonnegative_weighted_phaseSum_norm_floor_of_selected_approximation
      n ω w A k Q r hw hmass (fun i _hiA ↦ hr i)
  have hrounded :
      projectiveSelectedRoundedDefect w k A x ≤ η :=
    (projectiveSelectedRoundedDefect_le_waterDefect
      w k A x hx.2.1 hw).trans hx.2.2
  refine ⟨n, hn0, hnQ, ?_⟩
  calc
    1 - η ≤ 1 - projectiveSelectedRoundedDefect w k A x :=
      sub_le_sub_left hrounded 1
    _ ≤ ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ))‖ := by
      simpa only [projectiveSelectedRoundedDefect, Q] using hfloor
    _ = ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ :=
      norm_weighted_phaseSum_sub_pivot n ω w k

/-- A feasible selected profile is a universal deadline at its selected
resolution product. -/
theorem isUniversalProjectiveWeightedCoherenceDeadline_of_selectedFeasible
    {d : ℕ} (w : Fin d → ℝ) (A : Finset (Fin d)) (k : Fin d)
    {η : ℝ} (x : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hx : ProjectiveSelectedWaterFeasible w k A η x) :
    IsUniversalProjectiveWeightedCoherenceDeadline w η
      (∏ i, projectiveSelectedPhaseResolution A k x i) := by
  intro ω
  exact exists_projective_nonnegative_weighted_phaseSum_recurrence_selected
    ω w A k x hw hmass hx

/-- The selected resolution product pays one rounding constant per selected
coordinate, not per support coordinate. -/
theorem log_prod_projectiveSelectedPhaseResolution_le
    {d : ℕ} (A : Finset (Fin d)) (k : Fin d) (x : Fin d → ℝ)
    (hkA : k ∉ A) (hx : ∀ i, 1 ≤ x i) :
    Real.log
        ((∏ i, projectiveSelectedPhaseResolution A k x i : ℕ) : ℝ) ≤
      projectiveSelectedCoordinateEntropy A x +
        (A.card : ℕ) * Real.log projectivePhaseResolutionConstant := by
  have hQpos : ∀ i, 0 < projectiveSelectedPhaseResolution A k x i :=
    projectiveSelectedPhaseResolution_pos A k x hx
  have hterm : ∀ i : Fin d,
      Real.log (projectiveSelectedPhaseResolution A k x i : ℝ) ≤
        if i ∈ A then
          (1 / 2 : ℝ) * Real.log (x i) +
            Real.log projectivePhaseResolutionConstant
        else 0 := by
    intro i
    by_cases hiA : i ∈ A
    · have hik : i ≠ k := fun hik ↦ hkA (hik ▸ hiA)
      simp only [hiA, ↓reduceIte, projectiveSelectedPhaseResolution]
      have hxi : 0 < x i := lt_of_lt_of_le zero_lt_one (hx i)
      have hQi : 0 < (projectivePhaseResolution k x i : ℝ) :=
        Nat.cast_pos.mpr (projectivePhaseResolution_pos k x hx i)
      have hright :
          0 < projectivePhaseResolutionConstant * Real.sqrt (x i) := by
        exact mul_pos projectivePhaseResolutionConstant_pos
          (Real.sqrt_pos.mpr hxi)
      have hlog := Real.strictMonoOn_log.monotoneOn
        (show (projectivePhaseResolution k x i : ℝ) ∈ Set.Ioi 0 from hQi)
        (show projectivePhaseResolutionConstant * Real.sqrt (x i) ∈
          Set.Ioi 0 from hright)
        (projectivePhaseResolution_cast_upper k x hx i hik)
      rw [Real.log_mul projectivePhaseResolutionConstant_pos.ne'
          (Real.sqrt_pos.mpr hxi).ne',
        Real.log_sqrt hxi.le] at hlog
      nlinarith
    · simp [projectiveSelectedPhaseResolution, hiA]
  have hcastProd :
      (((∏ i, projectiveSelectedPhaseResolution A k x i : ℕ) : ℕ) : ℝ) =
        ∏ i, (projectiveSelectedPhaseResolution A k x i : ℝ) := by
    norm_num
  rw [hcastProd, Real.log_prod (fun i _hi ↦
    (Nat.cast_ne_zero.mpr (hQpos i).ne'))]
  calc
    (∑ i, Real.log
      (projectiveSelectedPhaseResolution A k x i : ℝ)) ≤
        ∑ i, if i ∈ A then
          (1 / 2 : ℝ) * Real.log (x i) +
            Real.log projectivePhaseResolutionConstant
        else 0 :=
      Finset.sum_le_sum fun i _hi ↦ hterm i
    _ = projectiveSelectedCoordinateEntropy A x +
        (A.card : ℕ) * Real.log projectivePhaseResolutionConstant := by
      rw [projectiveSelectedCoordinateEntropy]
      have hsplit :
          (∑ i, if i ∈ A then
              (1 / 2 : ℝ) * Real.log (x i) +
                Real.log projectivePhaseResolutionConstant
            else 0) =
            (∑ i, (1 / 2 : ℝ) *
              (if i ∈ A then Real.log (x i) else 0)) +
            ∑ i, (if i ∈ A then
              Real.log projectivePhaseResolutionConstant else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hiA : i ∈ A <;> simp [hiA]
      rw [hsplit, ← Finset.mul_sum]
      congr 1
      simp

/-- **Active-dimension recurrence ceiling.**  A feasible selected profile
supplies a universal deadline whose logarithmic implementation cost is linear
only in the selected coordinate count. -/
theorem exists_universalProjectiveWeightedCoherenceDeadline_of_selectedFeasible
    {d : ℕ} (w : Fin d → ℝ) (A : Finset (Fin d)) (k : Fin d)
    {η : ℝ} (x : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hx : ProjectiveSelectedWaterFeasible w k A η x) :
    ∃ T : ℕ,
      IsUniversalProjectiveWeightedCoherenceDeadline w η T ∧
      Real.log (T : ℝ) ≤ projectiveSelectedCoordinateEntropy A x +
        (A.card : ℕ) * Real.log projectivePhaseResolutionConstant := by
  refine ⟨∏ i, projectiveSelectedPhaseResolution A k x i,
    isUniversalProjectiveWeightedCoherenceDeadline_of_selectedFeasible
      w A k x hw hmass hx, ?_⟩
  exact log_prod_projectiveSelectedPhaseResolution_le
    A k x hx.1 hx.2.1

/-- Pure-state Floquet form of the active-dimension recurrence ceiling. -/
theorem exists_universalWeightedFloquetFidelityDeadline_of_selectedFeasible
    {d : ℕ} (w : Fin d → ℝ) (A : Finset (Fin d)) (k : Fin d)
    {η : ℝ} (x : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hη1 : η ≤ 1)
    (hx : ProjectiveSelectedWaterFeasible w k A η x) :
    ∃ T : ℕ,
      IsUniversalWeightedFloquetFidelityDeadline w η T ∧
      Real.log (T : ℝ) ≤ projectiveSelectedCoordinateEntropy A x +
        (A.card : ℕ) * Real.log projectivePhaseResolutionConstant := by
  obtain ⟨T, hdeadline, hlog⟩ :=
    exists_universalProjectiveWeightedCoherenceDeadline_of_selectedFeasible
      w A k x hw hmass hx
  exact ⟨T,
    (isUniversalWeightedFloquetFidelityDeadline_iff w hη1).mpr hdeadline,
    hlog⟩

end RHTower
