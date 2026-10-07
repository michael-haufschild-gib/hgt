import GaloisForLFunctions.RHTower.WeilBoundaryIntegerCountingRigidity
import Mathlib.MeasureTheory.Measure.Sub

/-!
# The integer atomic floor of the canonical Weil measure

The floor of every actual singleton mass defines a dominated integer-valued atomic submeasure.
Its complement is a positive measure with every atom below one. Exact subtraction is proved on
finite-mass measurable sets by restricting before invoking finite measure cancellation. No
atomicity, discreteness, or total-mass assumption on the canonical source is supplied.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace RHTower.WeilSpectral

/-- Integer part of the actual canonical singleton mass. -/
def quantizationIntegerWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (r : ℝ) : ℕ :=
  ⌊(boundaryMeasure hW).real {r}⌋₊

/-- The canonical integer atomic floor, with no atomicity assumption on the source. -/
def quantizationIntegerMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : Measure ℝ :=
  Measure.sum fun r : ℝ => (quantizationIntegerWeight hW r : ℝ≥0∞) • Measure.dirac r

/-- Positive residual measure after removal of the actual integer atomic floor. -/
def quantizationResidualMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : Measure ℝ :=
  boundaryMeasure hW - quantizationIntegerMeasure hW

theorem quantizationIntegerWeight_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (r : ℝ) :
    (quantizationIntegerWeight hW r : ℝ≥0∞) ≤ boundaryMeasure hW {r} := by
  calc
    (quantizationIntegerWeight hW r : ℝ≥0∞) =
        ENNReal.ofReal (quantizationIntegerWeight hW r : ℝ) := by simp
    _ ≤ ENNReal.ofReal ((boundaryMeasure hW).real {r}) :=
      ENNReal.ofReal_le_ofReal (Nat.floor_le ENNReal.toReal_nonneg)
    _ ≤ boundaryMeasure hW {r} := ENNReal.ofReal_toReal_le

theorem quantizationIntegerMeasure_apply {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : Set ℝ} (hs : MeasurableSet s) :
    quantizationIntegerMeasure hW s =
      ∑' r : ℝ, ((s.indicator (quantizationIntegerWeight hW) r : ℕ) : ℝ≥0∞) := by
  classical
  rw [quantizationIntegerMeasure, Measure.sum_apply _ hs]
  apply tsum_congr
  intro r
  by_cases hr : r ∈ s <;> simp [Measure.smul_apply, hr]

theorem quantizationIntegerMeasure_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    quantizationIntegerMeasure hW ≤ boundaryMeasure hW := by
  classical
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [quantizationIntegerMeasure_apply hW hs, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  calc
    ∑ r ∈ F, ((s.indicator (quantizationIntegerWeight hW) r : ℕ) : ℝ≥0∞) ≤
        ∑ r ∈ F, (boundaryMeasure hW).restrict s {r} := by
      apply Finset.sum_le_sum
      intro r _
      by_cases hr : r ∈ s
      · simpa [Measure.restrict_apply (measurableSet_singleton r),
          singleton_inter_of_mem hr, hr] using quantizationIntegerWeight_le hW r
      · simp [hr, Measure.restrict_apply (measurableSet_singleton r),
          singleton_inter_of_notMem hr]
    _ = (boundaryMeasure hW).restrict s (F : Set ℝ) := sum_measure_singleton
    _ ≤ (boundaryMeasure hW).restrict s univ := measure_mono (subset_univ _)
    _ = boundaryMeasure hW s := by simp

theorem quantizationIntegerMeasure_singleton {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (r : ℝ) :
    quantizationIntegerMeasure hW {r} = (quantizationIntegerWeight hW r : ℝ≥0∞) :=
  Measure.sum_smul_dirac_singleton

/-- Finite source mass forces a finite sum of natural-valued atomic weights. -/
theorem quantizationIntegerMeasure_nat {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : Set ℝ} (hs : MeasurableSet s) (hfin : boundaryMeasure hW s ≠ ∞) :
    ∃ n : ℕ, quantizationIntegerMeasure hW s = n := by
  classical
  let f : ℝ → ℕ := s.indicator (quantizationIntegerWeight hW)
  have hf : ∑' r : ℝ, (f r : ℝ≥0∞) ≠ ∞ := by
    rw [← quantizationIntegerMeasure_apply hW hs]
    exact ne_top_of_le_ne_top hfin (quantizationIntegerMeasure_le hW s)
  have hF : (Function.support f).Finite := by
    apply (ENNReal.finite_const_le_of_tsum_ne_top hf (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)).subset
    intro r hr
    change (1 : ℝ≥0∞) ≤ (f r : ℝ≥0∞)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
  refine ⟨∑ r ∈ hF.toFinset, f r, ?_⟩
  rw [quantizationIntegerMeasure_apply hW hs]
  change (∑' r : ℝ, (f r : ℝ≥0∞)) = ((∑ r ∈ hF.toFinset, f r : ℕ) : ℝ≥0∞)
  rw [tsum_eq_sum (s := hF.toFinset)]
  · simp
  · intro r hr
    have hz : f r = 0 := by simpa using hr
    simp [hz]

theorem quantizationResidualMeasure_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    quantizationResidualMeasure hW ≤ boundaryMeasure hW := Measure.sub_le

/-- The subtraction identity is paid locally, where the integer floor is finite. -/
theorem quantizationResidualMeasure_add_integer {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : Set ℝ} (hs : MeasurableSet s) (hfin : boundaryMeasure hW s ≠ ∞) :
    quantizationResidualMeasure hW s + quantizationIntegerMeasure hW s = boundaryMeasure hW s := by
  let μ := boundaryMeasure hW
  let κ := quantizationIntegerMeasure hW
  have hκfin : κ s ≠ ∞ := ne_top_of_le_ne_top hfin (quantizationIntegerMeasure_le hW s)
  letI : IsFiniteMeasure (κ.restrict s) := ⟨by simpa using hκfin.lt_top⟩
  have heq : μ.restrict s - κ.restrict s + κ.restrict s = μ.restrict s :=
    Measure.sub_add_cancel_of_le (Measure.restrict_mono subset_rfl (quantizationIntegerMeasure_le hW))
  have h := congrArg (fun ν : Measure ℝ => ν univ) heq
  rw [← Measure.restrict_sub_eq_restrict_sub_restrict hs] at h
  simpa only [Measure.add_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    quantizationResidualMeasure, μ, κ] using h

theorem quantization_real_mass_decomposition {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : Set ℝ} (hs : MeasurableSet s) (hfin : boundaryMeasure hW s ≠ ∞) :
    (boundaryMeasure hW).real s = (quantizationResidualMeasure hW).real s +
      (quantizationIntegerMeasure hW).real s := by
  have hνfin := ne_top_of_le_ne_top hfin (quantizationResidualMeasure_le hW s)
  have hκfin := ne_top_of_le_ne_top hfin (quantizationIntegerMeasure_le hW s)
  unfold Measure.real
  rw [← quantizationResidualMeasure_add_integer hW hs hfin, ENNReal.toReal_add hνfin hκfin]

theorem quantization_boundaryMeasure_Icc_ne_top {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (a b : ℝ) : boundaryMeasure hW (Icc a b) ≠ ∞ :=
  ne_top_of_le_ne_top (boundaryMeasure_Ioo_ne_top hW (a - 1) (b + 1))
    (measure_mono (by intro r hr; exact ⟨by linarith [hr.1], by linarith [hr.2]⟩))

theorem quantizationIntegerMeasure_Ioc_nat {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (a b : ℝ) : ∃ n : ℕ, quantizationIntegerMeasure hW (Ioc a b) = n :=
  quantizationIntegerMeasure_nat hW measurableSet_Ioc
    (ne_top_of_le_ne_top (quantization_boundaryMeasure_Icc_ne_top hW a b)
      (measure_mono Ioc_subset_Icc_self))

theorem quantizationResidualMeasure_atom_lt_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (r : ℝ) : (quantizationResidualMeasure hW).real {r} < 1 := by
  have hfin : boundaryMeasure hW {r} ≠ ∞ :=
    ne_top_of_le_ne_top (quantization_boundaryMeasure_Icc_ne_top hW r r)
      (measure_mono (by simp))
  have h := quantization_real_mass_decomposition hW (measurableSet_singleton r) hfin
  have hf := Nat.lt_floor_add_one ((boundaryMeasure hW).real {r})
  have heq : (quantizationIntegerMeasure hW).real {r} = (quantizationIntegerWeight hW r : ℝ) := by
    simp [Measure.real, quantizationIntegerMeasure_singleton]
  rw [heq] at h
  dsimp only [quantizationIntegerWeight] at h
  linarith

end RHTower.WeilSpectral
