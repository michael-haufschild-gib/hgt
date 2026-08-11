import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Norming-face fusion mechanics

A finite generated packet in a real normed space has a positive fusion defect: total marked norm
minus the norm of the fused resultant. Hahn--Banach identifies this defect with the least total
residual against one dual calibrator. Vanishing is equivalent to existence of a common norming
functional. Refinement and linear observation obey exact conservation identities.

In finite dimension, Helly's theorem implies every failure of common calibration has a witness of
cardinality at most dual dimension plus one. All results are unconditional and independent of RH.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators
open Set

noncomputable section

variable {ι κ V W : Type*}

/-- Sum of norms of source-marked generated effects. -/
def fusionEnvelopeOn [SeminormedAddCommGroup V] (s : Finset ι) (v : ι → V) : ℝ :=
  ∑ i ∈ s, ‖v i‖

/-- Coherently fused resultant of a generated packet. -/
def fusionResultantOn [SeminormedAddCommGroup V] (s : Finset ι) (v : ι → V) : V :=
  ∑ i ∈ s, v i

/-- Generated envelope minus norm of coherently fused execution. -/
def fusionDefectOn [SeminormedAddCommGroup V] (s : Finset ι) (v : ι → V) : ℝ :=
  fusionEnvelopeOn s v - ‖fusionResultantOn s v‖

/-- Failure of one dual calibrator to norm one generated effect. -/
def calibrationResidual [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : StrongDual ℝ V) (x : V) : ℝ :=
  ‖x‖ - φ x

/-- Total calibration residual on a finite packet. -/
def calibrationResidualSumOn [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (v : ι → V) (φ : StrongDual ℝ V) : ℝ :=
  ∑ i ∈ s, calibrationResidual φ (v i)

/-- One contractive functional simultaneously norms every effect in a packet. -/
def IsCommonCalibratorOn [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (v : ι → V) (φ : StrongDual ℝ V) : Prop :=
  ‖φ‖ ≤ 1 ∧ ∀ i ∈ s, φ (v i) = ‖v i‖

/-- Norming face of one effect in the closed dual unit ball. -/
def normingFace [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) : Set (StrongDual ℝ V) :=
  {φ | ‖φ‖ ≤ 1 ∧ φ x = ‖x‖}

/-- A contractive real functional never exceeds the norm of its input. -/
theorem calibrator_apply_le [NormedAddCommGroup V] [NormedSpace ℝ V]
    {φ : StrongDual ℝ V} (hφ : ‖φ‖ ≤ 1) (x : V) :
    φ x ≤ ‖x‖ := by
  calc
    φ x ≤ |φ x| := le_abs_self _
    _ = ‖φ x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Every local calibration residual is nonnegative. -/
theorem calibrationResidual_nonneg [NormedAddCommGroup V] [NormedSpace ℝ V]
    {φ : StrongDual ℝ V} (hφ : ‖φ‖ ≤ 1) (x : V) :
    0 ≤ calibrationResidual φ x := by
  exact sub_nonneg.mpr (calibrator_apply_le hφ x)

/-- Hahn--Banach supplies a calibrator whose total residual is exactly fusion defect. -/
theorem exists_calibrator_attains_fusionDefect [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (v : ι → V) :
    ∃ φ : StrongDual ℝ V, ‖φ‖ ≤ 1 ∧
      calibrationResidualSumOn s v φ = fusionDefectOn s v := by
  obtain ⟨φ, hφ, hattain⟩ := exists_dual_vector'' ℝ (fusionResultantOn s v)
  refine ⟨φ, hφ, ?_⟩
  simp only [calibrationResidualSumOn, calibrationResidual, fusionDefectOn, fusionEnvelopeOn,
    fusionResultantOn, Finset.sum_sub_distrib]
  rw [← map_sum]
  have hattain' : φ (∑ i ∈ s, v i) = ‖∑ i ∈ s, v i‖ := by
    simpa [fusionResultantOn] using hattain
  rw [hattain']

/-- No contractive calibrator has total residual below fusion defect. -/
theorem fusionDefect_le_calibrationResidualSum [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (v : ι → V) {φ : StrongDual ℝ V} (hφ : ‖φ‖ ≤ 1) :
    fusionDefectOn s v ≤ calibrationResidualSumOn s v φ := by
  simp only [calibrationResidualSumOn, calibrationResidual, fusionDefectOn, fusionEnvelopeOn,
    fusionResultantOn, Finset.sum_sub_distrib]
  rw [← map_sum]
  exact sub_le_sub_left (calibrator_apply_le hφ (∑ i ∈ s, v i)) _

/-- Fusion defect is nonnegative. -/
theorem fusionDefect_nonneg [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (v : ι → V) : 0 ≤ fusionDefectOn s v := by
  obtain ⟨φ, hφ, heq⟩ := exists_calibrator_attains_fusionDefect s v
  rw [← heq]
  exact Finset.sum_nonneg fun i hi => calibrationResidual_nonneg hφ (v i)

/-- Perfect fusion is equivalent to existence of one common norming calibrator. -/
theorem fusionDefect_eq_zero_iff_exists_commonCalibrator
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (v : ι → V) :
    fusionDefectOn s v = 0 ↔ ∃ φ : StrongDual ℝ V, IsCommonCalibratorOn s v φ := by
  constructor
  · intro hzero
    obtain ⟨φ, hφ, heq⟩ := exists_calibrator_attains_fusionDefect s v
    refine ⟨φ, hφ, ?_⟩
    have hsum : calibrationResidualSumOn s v φ = 0 := heq.trans hzero
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => calibrationResidual_nonneg hφ (v i))).mp hsum
    intro i hi
    exact (sub_eq_zero.mp (hall i hi)).symm
  · rintro ⟨φ, hφ, hnorms⟩
    have hphi : φ (fusionResultantOn s v) = fusionEnvelopeOn s v := by
      simp only [fusionResultantOn, fusionEnvelopeOn, map_sum]
      exact Finset.sum_congr rfl hnorms
    have hlower : fusionEnvelopeOn s v ≤ ‖fusionResultantOn s v‖ := by
      rw [← hphi]
      exact calibrator_apply_le hφ _
    have hupper : ‖fusionResultantOn s v‖ ≤ fusionEnvelopeOn s v := by
      exact norm_sum_le _ _
    exact sub_eq_zero.mpr (le_antisymm hlower hupper)

/-- Every effect has a nonempty norming face. -/
theorem normingFace_nonempty [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) :
    (normingFace x).Nonempty := by
  obtain ⟨φ, hφ, hx⟩ := exists_dual_vector'' ℝ x
  exact ⟨φ, hφ, hx⟩

/-- Norming faces are convex. -/
theorem normingFace_convex [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) :
    Convex ℝ (normingFace x) := by
  intro φ hφ ψ hψ a b ha hb hab
  constructor
  · have hballφ : φ ∈ Metric.closedBall (0 : StrongDual ℝ V) 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hφ.1
    have hballψ : ψ ∈ Metric.closedBall (0 : StrongDual ℝ V) 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hψ.1
    have hmem := (convex_closedBall (0 : StrongDual ℝ V) 1)
      hballφ hballψ ha hb hab
    simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
  · simp only [add_apply, smul_apply, hφ.2, hψ.2, smul_eq_mul]
    rw [← add_mul]
    simp [hab]

/-- In finite dimension, the continuous dual has the same dimension as the source space. -/
theorem strongDual_finrank_eq [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    Module.finrank ℝ (StrongDual ℝ V) = Module.finrank ℝ V := by
  calc
    Module.finrank ℝ (StrongDual ℝ V) =
        Module.finrank ℝ (Module.Dual ℝ V) :=
      (LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap :
        Module.Dual ℝ V ≃ₗ[ℝ] StrongDual ℝ V)).symm
    _ = Module.finrank ℝ V := Subspace.dual_finrank_eq

/-- If every packet of at most dual dimension plus one admits a common calibrator, then the whole
packet does. -/
theorem exists_commonCalibrator_of_small [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (s : Finset ι) (v : ι → V)
    (hsmall : ∀ t ⊆ s,
      t.card ≤ Module.finrank ℝ (StrongDual ℝ V) + 1 →
      ∃ φ : StrongDual ℝ V, IsCommonCalibratorOn t v φ) :
    ∃ φ : StrongDual ℝ V, IsCommonCalibratorOn s v φ := by
  have hinter : (⋂ i ∈ s, normingFace (v i)).Nonempty := by
    apply Convex.helly_theorem' (𝕜 := ℝ)
    · intro i hi
      exact normingFace_convex (v i)
    · intro t hts hcard
      obtain ⟨φ, hφ, hnorms⟩ := hsmall t hts hcard
      refine ⟨φ, ?_⟩
      exact Set.mem_iInter₂.mpr fun i hi => ⟨hφ, hnorms i hi⟩
  obtain ⟨φ, hφ⟩ := hinter
  have hmem : ∀ i ∈ s, φ ∈ normingFace (v i) := by
    intro i hi
    exact Set.mem_iInter₂.mp hφ i hi
  by_cases hs : s.Nonempty
  · obtain ⟨i, hi⟩ := hs
    exact ⟨φ, (hmem i hi).1, fun j hj => (hmem j hj).2⟩
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    exact hsmall s (Finset.Subset.rfl) (by simp [hsempty])

/-- Finite-dimensional fusion is completely tested by packets of at most dual dimension plus
one. -/
theorem fusionDefect_eq_zero_of_smallPackets [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (s : Finset ι) (v : ι → V)
    (hsmall : ∀ t ⊆ s,
      t.card ≤ Module.finrank ℝ (StrongDual ℝ V) + 1 →
      fusionDefectOn t v = 0) :
    fusionDefectOn s v = 0 := by
  rw [fusionDefect_eq_zero_iff_exists_commonCalibrator]
  apply exists_commonCalibrator_of_small s v
  intro t hts hcard
  rw [← fusionDefect_eq_zero_iff_exists_commonCalibrator]
  exact hsmall t hts hcard

/-- Primal-dimension form of the finite calibration witness theorem. -/
theorem fusionDefect_eq_zero_of_smallPackets_primal
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Finset ι) (v : ι → V)
    (hsmall : ∀ t ⊆ s,
      t.card ≤ Module.finrank ℝ V + 1 → fusionDefectOn t v = 0) :
    fusionDefectOn s v = 0 := by
  apply fusionDefect_eq_zero_of_smallPackets s v
  intro t hts hcard
  apply hsmall t hts
  simpa [strongDual_finrank_eq] using hcard

/-- Every minimally defective packet has cardinality at most dual dimension plus one. -/
theorem minimallyDefective_card_le_finrank_add_one
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Finset ι) (v : ι → V)
    (hdef : 0 < fusionDefectOn s v)
    (hproper : ∀ t ⊆ s, t ≠ s → fusionDefectOn t v = 0) :
    s.card ≤ Module.finrank ℝ (StrongDual ℝ V) + 1 := by
  by_contra hcard
  have hsmall : ∀ t ⊆ s,
      t.card ≤ Module.finrank ℝ (StrongDual ℝ V) + 1 →
      fusionDefectOn t v = 0 := by
    intro t hts htcard
    apply hproper t hts
    intro hts_eq
    subst t
    exact hcard htcard
  have hzero := fusionDefect_eq_zero_of_smallPackets s v hsmall
  exact (ne_of_gt hdef) hzero

/-- Primal-dimension bound for a minimally defective packet. -/
theorem minimallyDefective_card_le_finrank_add_one_primal
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Finset ι) (v : ι → V)
    (hdef : 0 < fusionDefectOn s v)
    (hproper : ∀ t ⊆ s, t ≠ s → fusionDefectOn t v = 0) :
    s.card ≤ Module.finrank ℝ V + 1 := by
  simpa [strongDual_finrank_eq] using
    minimallyDefective_card_le_finrank_add_one s v hdef hproper

/-- Minimal obstruction arity gives an explicit lower bound on calibration dimension. -/
theorem minimallyDefective_pred_card_le_finrank
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Finset ι) (v : ι → V)
    (hdef : 0 < fusionDefectOn s v)
    (hproper : ∀ t ⊆ s, t ≠ s → fusionDefectOn t v = 0) :
    s.card - 1 ≤ Module.finrank ℝ V := by
  have hbound := minimallyDefective_card_le_finrank_add_one_primal s v hdef hproper
  omega

/-- Norm lost by a linear observer on one effect. -/
def normLoss [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) (x : V) : ℝ := ‖x‖ - ‖T x‖

/-- Exact exchange between source fusion defect, observed defect, and separate versus aggregate
norm loss. -/
theorem fusionDefect_observer_exchange [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) (s : Finset ι) (v : ι → V) :
    fusionDefectOn s v - fusionDefectOn s (fun i => T (v i)) =
      (∑ i ∈ s, normLoss T (v i)) - normLoss T (fusionResultantOn s v) := by
  simp only [fusionDefectOn, fusionEnvelopeOn, fusionResultantOn, normLoss]
  rw [← map_sum]
  rw [Finset.sum_sub_distrib]
  ring

/-- Disjoint union of two generated packets. -/
def sumPacket [NormedAddCommGroup V] (v : ι → V) (w : κ → V) : ι ⊕ κ → V
  | Sum.inl i => v i
  | Sum.inr j => w j

/-- Binary refinement conservation: local block defects plus defect between block resultants equal
the defect of the unfused packet. -/
theorem fusionDefect_binary_refinement [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] [Fintype κ] (v : ι → V) (w : κ → V) :
    fusionDefectOn Finset.univ (sumPacket v w) =
      fusionDefectOn Finset.univ v + fusionDefectOn Finset.univ w +
        (‖fusionResultantOn Finset.univ v‖ + ‖fusionResultantOn Finset.univ w‖ -
          ‖fusionResultantOn Finset.univ v + fusionResultantOn Finset.univ w‖) := by
  simp only [fusionDefectOn, fusionEnvelopeOn, fusionResultantOn, sumPacket,
    Fintype.sum_sum_type]
  ring

end


end GaloisForLFunctions.HTGeometry
