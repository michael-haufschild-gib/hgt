import GaloisForLFunctions.RHTower.ProjectiveWeightedTargetEntropy
import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceAvoidance

/-!
# Weighted projective coherence avoidance

This file turns the reverse-water-filling Haar estimate into a deterministic
minimax obstruction.  Integer multiplication preserves Haar measure, so a
finite union bound constructs one real frequency packet avoiding weighted
near-coherence until the reciprocal target-volume scale.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Initial positive-clock hits of a weighted projective coherence target. -/
def torusProjectiveWeightedCoherenceHitUnion {d : ℕ}
    (w : Fin d → ℝ) (N : ℕ) (η : ℝ) :
    Set (Fin d → UnitAddCircle) :=
  ⋃ n : Fin N,
    (fun x : Fin d → UnitAddCircle ↦ ((n.1 + 1 : ℕ) : ℤ) • x) ⁻¹'
      torusProjectiveWeightedCoherenceTarget w η

theorem continuous_torusProjectiveWeightedCoherenceAmplitude
    {d : ℕ} (w : Fin d → ℝ) :
    Continuous (fun x : Fin d → UnitAddCircle ↦
      ‖projectiveWeightedPhaseAmplitude w
        (fun j ↦ fourier 1 (x j))‖) := by
  unfold projectiveWeightedPhaseAmplitude
  fun_prop

theorem measurableSet_torusProjectiveWeightedCoherenceTarget
    {d : ℕ} (w : Fin d → ℝ) (η : ℝ) :
    MeasurableSet (torusProjectiveWeightedCoherenceTarget w η) := by
  rw [torusProjectiveWeightedCoherenceTarget]
  exact measurableSet_le measurable_const
    (continuous_torusProjectiveWeightedCoherenceAmplitude w).measurable

/-- Every nonzero integer clock preserves the Haar measure of the weighted
target. -/
theorem measureReal_torusProjectiveWeightedCoherenceTarget_zsmul_preimage
    {d : ℕ} (w : Fin d → ℝ) (η : ℝ) {n : ℤ} (hn : n ≠ 0) :
    volume.real ((fun x : Fin d → UnitAddCircle ↦ n • x) ⁻¹'
        torusProjectiveWeightedCoherenceTarget w η) =
      volume.real (torusProjectiveWeightedCoherenceTarget w η) := by
  have hmp := Measure.measurePreserving_zsmul
    (G := Fin d → UnitAddCircle) volume hn
  simp only [measureReal_def]
  rw [← Measure.map_apply hmp.measurable
    (measurableSet_torusProjectiveWeightedCoherenceTarget w η), hmp.map_eq]

/-- Union bound for the first `N` weighted coherence hits. -/
theorem measureReal_torusProjectiveWeightedCoherenceHitUnion_le
    {d : ℕ} (w : Fin d → ℝ) (N : ℕ) (η : ℝ) :
    volume.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
      (N : ℝ) *
        volume.real (torusProjectiveWeightedCoherenceTarget w η) := by
  calc
    volume.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
        ∑ n : Fin N,
          volume.real ((fun x : Fin d → UnitAddCircle ↦
            ((n.1 + 1 : ℕ) : ℤ) • x) ⁻¹'
              torusProjectiveWeightedCoherenceTarget w η) := by
      exact measureReal_iUnion_fintype_le _
    _ = ∑ _n : Fin N,
        volume.real (torusProjectiveWeightedCoherenceTarget w η) := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact
        measureReal_torusProjectiveWeightedCoherenceTarget_zsmul_preimage
          w η (by omega)
    _ = (N : ℝ) *
        volume.real (torusProjectiveWeightedCoherenceTarget w η) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-- The explicit target budget selected by a common projective entropy
floor. -/
def projectiveWaterTargetBudget (d : ℕ) (H : ℝ) : ℝ :=
  (d : ℝ) * Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H)

theorem projectiveWaterTargetBudget_pos
    {d : ℕ} (hd : 0 < d) (H : ℝ) :
    0 < projectiveWaterTargetBudget d H := by
  rw [projectiveWaterTargetBudget]
  positivity

/-- Reverse-water-filling target estimate propagated through the first `N`
integer clocks. -/
theorem measureReal_torusProjectiveWeightedCoherenceHitUnion_waterEntropy_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η H : ℝ} (hη1 : η ≤ 1)
    (lam : Fin d → ℝ) (hlam : ∀ k, 0 < lam k)
    (hscaleBudget : ∀ k, lam k * η ≤ (d - 1 : ℕ))
    (hentropy : ∀ k, H ≤ projectiveWaterEntropyAt w k (lam k)) :
    volume.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
      (N : ℝ) * projectiveWaterTargetBudget d H := by
  calc
    volume.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
        (N : ℝ) *
          volume.real (torusProjectiveWeightedCoherenceTarget w η) :=
      measureReal_torusProjectiveWeightedCoherenceHitUnion_le w N η
    _ ≤ (N : ℝ) * projectiveWaterTargetBudget d H := by
      exact mul_le_mul_of_nonneg_left
        (by
          simpa only [projectiveWaterTargetBudget] using
            measureReal_torusProjectiveWeightedCoherenceTarget_waterEntropy_le
              w hw hmass hη1 lam hlam hscaleBudget hentropy)
        (Nat.cast_nonneg N)

/-- Below the water-entropy budget, some torus packet avoids weighted
coherence at every positive clock through `N`. -/
theorem exists_torus_phase_avoiding_projectiveWeightedCoherence_until
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η H : ℝ} (hη1 : η ≤ 1)
    (lam : Fin d → ℝ) (hlam : ∀ k, 0 < lam k)
    (hscaleBudget : ∀ k, lam k * η ≤ (d - 1 : ℕ))
    (hentropy : ∀ k, H ≤ projectiveWaterEntropyAt w k (lam k))
    (hbudget : (N : ℝ) * projectiveWaterTargetBudget d H < 1) :
    ∃ x : Fin d → UnitAddCircle, ∀ n : Fin N,
      ‖projectiveWeightedPhaseAmplitude w (fun j ↦
        fourier 1 (((n.1 + 1 : ℕ) : ℤ) • x j))‖ < 1 - η := by
  have hhit :
      volume.real (torusProjectiveWeightedCoherenceHitUnion w N η) < 1 :=
    (measureReal_torusProjectiveWeightedCoherenceHitUnion_waterEntropy_le
      w hw hmass N hη1 lam hlam hscaleBudget hentropy).trans_lt hbudget
  have hexists : ∃ x : Fin d → UnitAddCircle,
      x ∉ torusProjectiveWeightedCoherenceHitUnion w N η := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set (Fin d → UnitAddCircle)) ⊆
        torusProjectiveWeightedCoherenceHitUnion w N η := fun x _hx ↦ h x
    have hmeasure :
        volume.real (Set.univ : Set (Fin d → UnitAddCircle)) ≤
          volume.real (torusProjectiveWeightedCoherenceHitUnion w N η) :=
      measureReal_mono hsub
    rw [measureReal_torus_univ] at hmeasure
    exact (not_lt_of_ge hmeasure) hhit
  obtain ⟨x, hx⟩ := hexists
  refine ⟨x, fun n ↦ ?_⟩
  have hnot : ((fun y : Fin d → UnitAddCircle ↦
      ((n.1 + 1 : ℕ) : ℤ) • y) x) ∉
        torusProjectiveWeightedCoherenceTarget w η := by
    intro hn
    apply hx
    rw [torusProjectiveWeightedCoherenceHitUnion, Set.mem_iUnion]
    exact ⟨n, hn⟩
  rw [torusProjectiveWeightedCoherenceTarget, Set.mem_setOf_eq] at hnot
  simpa only [Pi.smul_apply] using lt_of_not_ge hnot

/-- Real-frequency form of weighted finite-time avoidance. -/
theorem exists_real_frequency_avoiding_projectiveWeightedCoherence_until
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η H : ℝ} (hη1 : η ≤ 1)
    (lam : Fin d → ℝ) (hlam : ∀ k, 0 < lam k)
    (hscaleBudget : ∀ k, lam k * η ≤ (d - 1 : ℕ))
    (hentropy : ∀ k, H ≤ projectiveWaterEntropyAt w k (lam k))
    (hbudget : (N : ℝ) * projectiveWaterTargetBudget d H < 1) :
    ∃ ω : Fin d → ℝ, ∀ n : Fin N,
      ‖∑ j, (w j : ℂ) * Complex.exp (Complex.I *
        ((((n.1 + 1 : ℕ) : ℝ) * ω j : ℝ) : ℂ))‖ < 1 - η := by
  obtain ⟨x, hx⟩ :=
    exists_torus_phase_avoiding_projectiveWeightedCoherence_until
      w hw hmass N hη1 lam hlam hscaleBudget hentropy hbudget
  refine ⟨fun j ↦ torusRealFrequency (x j), fun n ↦ ?_⟩
  simpa only [projectiveWeightedPhaseAmplitude,
    exp_torusRealFrequency_eq_fourier_zsmul] using hx n

/-- A universal weighted coherence deadline. -/
def IsUniversalProjectiveWeightedCoherenceDeadline {d : ℕ}
    (w : Fin d → ℝ) (η : ℝ) (N : ℕ) : Prop :=
  ∀ ω : Fin d → ℝ, ∃ n : ℕ, 0 < n ∧ n ≤ N ∧
    1 - η ≤ ‖∑ j, (w j : ℂ) * Complex.exp
      (Complex.I * ((((n : ℝ) * ω j : ℝ) : ℂ)))‖

theorem IsUniversalProjectiveWeightedCoherenceDeadline.mono
    {d N M : ℕ} {w : Fin d → ℝ} {η : ℝ}
    (h : IsUniversalProjectiveWeightedCoherenceDeadline w η N)
    (hNM : N ≤ M) :
    IsUniversalProjectiveWeightedCoherenceDeadline w η M := by
  intro ω
  obtain ⟨n, hn0, hnN, hncoh⟩ := h ω
  exact ⟨n, hn0, hnN.trans hNM, hncoh⟩

/-- Every integer below the water-entropy Haar budget fails to be a universal
deadline. -/
theorem not_isUniversalProjectiveWeightedCoherenceDeadline_of_waterBudget
    {d N : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η H : ℝ} (hη1 : η ≤ 1)
    (lam : Fin d → ℝ) (hlam : ∀ k, 0 < lam k)
    (hscaleBudget : ∀ k, lam k * η ≤ (d - 1 : ℕ))
    (hentropy : ∀ k, H ≤ projectiveWaterEntropyAt w k (lam k))
    (hbudget : (N : ℝ) * projectiveWaterTargetBudget d H < 1) :
    ¬ IsUniversalProjectiveWeightedCoherenceDeadline w η N := by
  obtain ⟨ω, hω⟩ :=
    exists_real_frequency_avoiding_projectiveWeightedCoherence_until
      w hw hmass N hη1 lam hlam hscaleBudget hentropy hbudget
  intro hdeadline
  obtain ⟨n, hn0, hnN, hncoh⟩ := hdeadline ω
  have hnlt : n - 1 < N := by omega
  let k : Fin N := ⟨n - 1, hnlt⟩
  have hkval : k.1 + 1 = n := by dsimp only [k]; omega
  have havoid := hω k
  rw [hkval] at havoid
  exact (not_lt_of_ge hncoh) havoid

/-- Reciprocal target volume is a strict logarithmic floor for every
universal weighted deadline. -/
theorem neg_log_two_mul_projectiveWaterTargetBudget_lt_log_deadline
    {d T : ℕ} (hd : 0 < d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η H : ℝ} (hη1 : η ≤ 1)
    (lam : Fin d → ℝ) (hlam : ∀ k, 0 < lam k)
    (hscaleBudget : ∀ k, lam k * η ≤ (d - 1 : ℕ))
    (hentropy : ∀ k, H ≤ projectiveWaterEntropyAt w k (lam k))
    (hdeadline : IsUniversalProjectiveWeightedCoherenceDeadline w η T) :
    -Real.log (2 * projectiveWaterTargetBudget d H) < Real.log (T : ℝ) := by
  let B : ℝ := projectiveWaterTargetBudget d H
  have hB : 0 < B := projectiveWaterTargetBudget_pos hd H
  let N : ℕ := ⌊1 / (2 * B)⌋₊
  have hfloor : (N : ℝ) ≤ 1 / (2 * B) := by
    exact Nat.floor_le (by positivity)
  have hNB : (N : ℝ) * B < 1 := by
    have hhalf : (N : ℝ) * B ≤ 1 / 2 := by
      calc
        (N : ℝ) * B ≤ (1 / (2 * B)) * B :=
          mul_le_mul_of_nonneg_right hfloor hB.le
        _ = 1 / 2 := by field_simp [hB.ne']
    linarith
  have hnot : ¬ IsUniversalProjectiveWeightedCoherenceDeadline w η N :=
    not_isUniversalProjectiveWeightedCoherenceDeadline_of_waterBudget
      w hw hmass hη1 lam hlam hscaleBudget hentropy (by
        simpa only [B] using hNB)
  have hNT : N < T := by
    by_contra hTN
    push Not at hTN
    exact hnot (hdeadline.mono hTN)
  have hreal : 1 / (2 * B) < (T : ℝ) := by
    have hfloorlt : 1 / (2 * B) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hsucc : N + 1 ≤ T := by omega
    exact hfloorlt.trans_le (by exact_mod_cast hsucc)
  have hleftmem : 1 / (2 * B) ∈ Set.Ioi (0 : ℝ) := by
    change 0 < 1 / (2 * B)
    positivity
  have hrightmem : (T : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    have : 0 < T := lt_of_le_of_lt (Nat.zero_le N) hNT
    change 0 < (T : ℝ)
    exact_mod_cast this
  have hlog := Real.strictMonoOn_log hleftmem hrightmem hreal
  rw [one_div, Real.log_inv] at hlog
  simpa only [B] using hlog

/-- Exact expansion of the weighted Haar floor. -/
theorem neg_log_two_mul_projectiveWaterTargetBudget_eq
    {d : ℕ} (hd : 0 < d) (H : ℝ) :
    -Real.log (2 * projectiveWaterTargetBudget d H) =
      H - (Real.pi / 4) * (d - 1 : ℕ) - Real.log (2 * (d : ℝ)) := by
  rw [projectiveWaterTargetBudget]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [show 2 * ((d : ℝ) *
      Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H)) =
      (2 * (d : ℝ)) *
        Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) by ring,
    Real.log_mul (mul_ne_zero (by norm_num) hd0) (Real.exp_ne_zero _),
    Real.log_exp]
  ring

/-- **Weighted projective entropy floor.**  Every universal deadline lies
strictly above the reverse-water-filling entropy minus the explicit extensive
Haar cost. -/
theorem projectiveWaterEntropy_sub_cost_lt_log_deadline
    {d T : ℕ} (hd : 0 < d) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    {η H : ℝ} (hη1 : η ≤ 1)
    (lam : Fin d → ℝ) (hlam : ∀ k, 0 < lam k)
    (hscaleBudget : ∀ k, lam k * η ≤ (d - 1 : ℕ))
    (hentropy : ∀ k, H ≤ projectiveWaterEntropyAt w k (lam k))
    (hdeadline : IsUniversalProjectiveWeightedCoherenceDeadline w η T) :
    H - (Real.pi / 4) * (d - 1 : ℕ) - Real.log (2 * (d : ℝ)) <
      Real.log (T : ℝ) := by
  rw [← neg_log_two_mul_projectiveWaterTargetBudget_eq hd H]
  exact neg_log_two_mul_projectiveWaterTargetBudget_lt_log_deadline
    hd w hw hmass hη1 lam hlam hscaleBudget hentropy hdeadline

end RHTower
