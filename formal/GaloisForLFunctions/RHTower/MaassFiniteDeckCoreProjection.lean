import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreStripEnergy
import GaloisForLFunctions.HTGeometry.LpBoundedSmulMultiplier

/-!
# Finite-deck core cutoff projection

The finite chart core defines a contractive `L²` cutoff.  Its squared norm is
exactly the mass on the finite core, so the grid approximation estimate can be
transported into the completed form domain through continuous operators.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The finite grid core is measurable because it is a finite union of measurable
fundamental-domain cells. -/
theorem measurableSet_fdUpperChartGridCore {M K : ℕ} (a c hx hy : ℝ) :
    MeasurableSet (fdUpperChartGridCore (M := M) (K := K) a c hx hy) := by
  unfold fdUpperChartGridCore
  apply MeasurableSet.iUnion
  intro i
  exact ModularGroup.isClosed_fd.measurableSet.inter
    (measurableSet_upperChartGridCell a c hx hy i)

/-- Scalar cutoff for a finite chart core. -/
def finiteGridCoreCutoff {M K : ℕ} (a c hx hy : ℝ) (z : ℍ) : ℂ :=
  Set.indicator (fdUpperChartGridCore (M := M) (K := K) a c hx hy) (fun _ => 1) z

theorem measurable_finiteGridCoreCutoff {M K : ℕ} (a c hx hy : ℝ) :
    Measurable (finiteGridCoreCutoff (M := M) (K := K) a c hx hy) := by
  exact Measurable.indicator measurable_const
    (measurableSet_fdUpperChartGridCore a c hx hy)

theorem norm_finiteGridCoreCutoff_le_one {M K : ℕ} (a c hx hy : ℝ) (z : ℍ) :
    ‖finiteGridCoreCutoff (M := M) (K := K) a c hx hy z‖ ≤ 1 := by
  by_cases hz : z ∈ fdUpperChartGridCore (M := M) (K := K) a c hx hy <;>
    simp [finiteGridCoreCutoff, hz]

/-- Contractive projection onto the finite chart core. -/
def finiteGridCoreProjection {N M K : ℕ} (a c hx hy : ℝ) :
    DeckL2 N →L[ℂ] DeckL2 N :=
  MeasureTheory.lpBoundedSmulCLM (p := 2) (μ := cellMeasure) (H := DeckSpace N)
    (measurable_finiteGridCoreCutoff (M := M) (K := K) a c hx hy) (by positivity)
    (norm_finiteGridCoreCutoff_le_one (M := M) (K := K) a c hx hy)

/-- The core projection's norm is exactly the finite-core `L²` mass. -/
theorem normSq_finiteGridCoreProjection_toDeckL2 {N M K : ℕ} (a c hx hy : ℝ)
    (F : ℍ → DeckSpace N) (hF : MemLp F 2 cellMeasure) :
    ‖finiteGridCoreProjection (N := N) (M := M) (K := K) a c hx hy
      (toDeckL2 F hF)‖ ^ 2 =
      ∫ z in fdUpperChartGridCore (M := M) (K := K) a c hx hy, ‖F z‖ ^ 2 := by
  rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  have hproj :
      ((finiteGridCoreProjection (N := N) (M := M) (K := K) a c hx hy
        (toDeckL2 F hF) : DeckL2 N) : ℍ → DeckSpace N) =ᵐ[cellMeasure]
        fun z => finiteGridCoreCutoff (M := M) (K := K) a c hx hy z •
          ((toDeckL2 F hF : DeckL2 N) : ℍ → DeckSpace N) z := by
    exact MeasureTheory.lpBoundedSmulCLM_coeFn (p := 2) (μ := cellMeasure)
      (H := DeckSpace N) (measurable_finiteGridCoreCutoff (M := M) (K := K) a c hx hy) (by positivity)
      (norm_finiteGridCoreCutoff_le_one (M := M) (K := K) a c hx hy) (toDeckL2 F hF)
  have hFae := MemLp.coeFn_toLp hF
  calc
    (∫ z, ‖((finiteGridCoreProjection (N := N) (M := M) (K := K) a c hx hy
      (toDeckL2 F hF) : DeckL2 N) : ℍ → DeckSpace N) z‖ ^ 2 ∂cellMeasure) =
        ∫ z, ‖finiteGridCoreCutoff (M := M) (K := K) a c hx hy z • F z‖ ^ 2
          ∂cellMeasure := by
      apply integral_congr_ae
      filter_upwards [hproj, hFae] with z hp hFz
      rw [hp]
      change ‖finiteGridCoreCutoff (M := M) (K := K) a c hx hy z •
        (MemLp.toLp F hF : ℍ → DeckSpace N) z‖ ^ 2 = _
      rw [hFz]
    _ = ∫ z in ModularGroup.fd,
        ‖finiteGridCoreCutoff (M := M) (K := K) a c hx hy z • F z‖ ^ 2 := by rfl
    _ = ∫ z in ModularGroup.fd,
        (fdUpperChartGridCore (M := M) (K := K) a c hx hy).indicator
          (fun z => ‖F z‖ ^ 2) z := by
      apply setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet
      intro z hz
      by_cases hcore : z ∈ fdUpperChartGridCore (M := M) (K := K) a c hx hy <;>
        simp [finiteGridCoreCutoff, hcore]
    _ = ∫ z in fdUpperChartGridCore (M := M) (K := K) a c hx hy, ‖F z‖ ^ 2 := by
      rw [MeasureTheory.setIntegral_indicator]
      · have hsubset : fdUpperChartGridCore (M := M) (K := K) a c hx hy ⊆
            ModularGroup.fd := by
          intro z hz
          change z ∈ ⋃ i : Fin K × Fin M,
            ModularGroup.fd ∩ upperChartGridCell a c hx hy i at hz
          rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
          exact hzi.1
        rw [Set.inter_eq_right.mpr hsubset]
      · exact measurableSet_fdUpperChartGridCore a c hx hy

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
