import GaloisForLFunctions.HTGeometry.PositiveMeasureExtremeRays
import GaloisForLFunctions.HTGeometry.HausdorffCDDMeasureSource

/-!
# Extreme rays of the CDD source cone

The source cone of the higher-spin CDD phase is the cone of finite positive measures on `[0,1]`, so
its extreme rays are exactly the positive point masses.  Under the phase transform a point mass of
weight `w` at `y` is the elementary paired-shell phase `w·K(y,θ)`, and the endpoint `y = 0` is the
ordinary `T T̄` dressing `exp(8 i w sinh θ)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The zero shell of the source space. -/
def hausdorffZeroShell : HausdorffSourceSpace := ⟨0, by constructor <;> norm_num⟩

@[simp] theorem hausdorffZeroShell_coe : ((hausdorffZeroShell : HausdorffSourceSpace) : ℝ) = 0 :=
  rfl

theorem hausdorffAtomSource_eq_smul (w : ℝ≥0) (y : HausdorffSourceSpace) :
    hausdorffAtomSource w y = (w : ℝ≥0∞) • Measure.dirac y := rfl

/-- **Every positive point source spans an extreme ray.** -/
theorem isExtremeRayMeasure_hausdorffAtomSource {w : ℝ≥0} (hw : w ≠ 0)
    (y : HausdorffSourceSpace) : IsExtremeRayMeasure (hausdorffAtomSource w y) := by
  rw [hausdorffAtomSource_eq_smul]
  exact isExtremeRayMeasure_smul_dirac (by simpa using hw) (by simp) y

/-- **Classification of the extreme rays of the CDD source cone.**  A finite positive source spans
an extreme ray exactly when it is a positive point mass. -/
theorem isExtremeRayMeasure_iff_hausdorffAtomSource (nu : Measure HausdorffSourceSpace)
    [IsFiniteMeasure nu] :
    IsExtremeRayMeasure nu ↔
      ∃ (w : ℝ≥0) (y : HausdorffSourceSpace), w ≠ 0 ∧ nu = hausdorffAtomSource w y := by
  constructor
  · intro hex
    obtain ⟨y, c, hc, hc', hnu⟩ := exists_smul_dirac_of_isExtremeRayMeasure hex
    refine ⟨c.toNNReal, y, ?_, ?_⟩
    · simpa [ENNReal.toNNReal_eq_zero_iff, hc'] using hc
    · rw [hausdorffAtomSource_eq_smul, ENNReal.coe_toNNReal hc']
      exact hnu
  · rintro ⟨w, y, hw, rfl⟩
    exact isExtremeRayMeasure_hausdorffAtomSource hw y

/-- **Extreme source rays are elementary paired-shell phase rays.** -/
theorem exists_shell_hausdorffCDDPhase_of_isExtremeRayMeasure (nu : Measure HausdorffSourceSpace)
    [IsFiniteMeasure nu] (hex : IsExtremeRayMeasure nu) :
    ∃ (w : ℝ≥0) (y : HausdorffSourceSpace), w ≠ 0 ∧
      ∀ θ : ℝ, hausdorffCDDPhase nu θ = (w : ℝ) * cddPhaseKernel (y : ℝ) θ := by
  obtain ⟨w, y, hw, rfl⟩ := (isExtremeRayMeasure_iff_hausdorffAtomSource nu).1 hex
  exact ⟨w, y, hw, fun θ => hausdorffCDDPhase_atom w y θ⟩

/-- **The zero-shell extreme ray is the ordinary `T T̄` dressing.**  Its phase is `8 w sinh θ`. -/
theorem hausdorffCDDPhase_zeroShell (w : ℝ≥0) (θ : ℝ) :
    hausdorffCDDPhase (hausdorffAtomSource w hausdorffZeroShell) θ =
      8 * (w : ℝ) * Real.sinh θ := by
  rw [hausdorffCDDPhase_atom w hausdorffZeroShell θ, hausdorffZeroShell_coe,
    cddPhaseKernel_zero]
  ring

/-- The unitary factor of the zero-shell ray is exactly the ordinary `T T̄` CDD factor. -/
theorem exp_I_hausdorffCDDPhase_zeroShell (w : ℝ≥0) (θ : ℝ) :
    Complex.exp (Complex.I *
        (hausdorffCDDPhase (hausdorffAtomSource w hausdorffZeroShell) θ : ℂ)) =
      Complex.exp (Complex.I * ((8 * (w : ℝ) * Real.sinh θ : ℝ) : ℂ)) := by
  rw [hausdorffCDDPhase_zeroShell]

/-- A finite positive combination of point sources. -/
noncomputable def hausdorffFiniteAtomicSource {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0)
    (y : ι → HausdorffSourceSpace) : Measure HausdorffSourceSpace :=
  ∑ i ∈ s, hausdorffAtomSource (w i) (y i)

instance {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0) (y : ι → HausdorffSourceSpace) :
    IsFiniteMeasure (hausdorffFiniteAtomicSource s w y) := by
  unfold hausdorffFiniteAtomicSource
  classical
  induction s using Finset.induction with
  | empty => simpa using (inferInstance : IsFiniteMeasure (0 : Measure HausdorffSourceSpace))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact @MeasureTheory.isFiniteMeasureAdd _ _ _ _ inferInstance ih

/-- **Finite atomic sources are finite positive shell-germ sums.** -/
theorem hausdorffCDDPhase_finiteAtomicSource {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0)
    (y : ι → HausdorffSourceSpace) (θ : ℝ) :
    hausdorffCDDPhase (hausdorffFiniteAtomicSource s w y) θ =
      ∑ i ∈ s, (w i : ℝ) * cddPhaseKernel ((y i : HausdorffSourceSpace) : ℝ) θ := by
  classical
  unfold hausdorffFiniteAtomicSource
  induction s using Finset.induction with
  | empty => simp [hausdorffCDDPhase]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      haveI : IsFiniteMeasure (∑ i ∈ s, hausdorffAtomSource (w i) (y i)) := by
        infer_instance
      rw [hausdorffCDDPhase_add, hausdorffCDDPhase_atom]

end GaloisForLFunctions.HTGeometry
