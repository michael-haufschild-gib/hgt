import GaloisForLFunctions.BiScaleUncertainty.DivisorGradientClosure
import GaloisForLFunctions.BiScaleUncertainty.DivisorGridClosedRange

/-!
# Physical energy completion and exact trace recovery

The completed domain is an explicit closed subspace of cell currents. Synthesis
is isometric and its physical range is exactly the closure of old interpolants.
Cumulative traces recover old data precisely when they belong to ℓ².
-/

noncomputable section
open Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

abbrev DivisorEnergyData (d : ℕ) (D : Set ℕ) := divisorCellSpace d D

def divisorEnergyExtension (d : ℕ) (D : Set ℕ) : DivisorEnergyData d D →ₗᵢ[ℝ] Velocity :=
  unitCellSynthesis.comp (divisorCellSpace d D).subtypeₗᵢ

theorem divisorEnergyExtension_apply (d : ℕ) (D : Set ℕ) (w : DivisorEnergyData d D) :
    divisorEnergyExtension d D w = unitCellSynthesis w.1 := rfl

theorem divisorEnergyExtension_energy (d : ℕ) (D : Set ℕ) (w : DivisorEnergyData d D) :
    ‖divisorEnergyExtension d D w‖^2 = ∑' k, (w.1 k)^2 := by
  rw [(divisorEnergyExtension d D).norm_map]
  exact norm_sq_traceData w.1

theorem primitive_divisorEnergyExtension (d : ℕ) (D : Set ℕ)
    (w : DivisorEnergyData d D) (n : ℕ) :
    primitive (divisorEnergyExtension d D w) n = cellPrefixL n w.1 :=
  primitive_unitCellSynthesis n w.1

theorem log_divisorEnergyExtension (d : ℕ) (D : Set ℕ)
    (w : DivisorEnergyData d D) (k : ℕ) :
    logPrimitive (divisorEnergyExtension d D w) (Real.log ((k : ℝ)+1)) =
      cellPrefixL (k+1) w.1 := log_unitCellSynthesis k w.1

def divisorCompletedTrace (d : ℕ) (D : Set ℕ) (w : DivisorEnergyData d D) (k : ℕ) : ℝ :=
  cellPrefixL (k+1) w.1

theorem divisorCompletedTrace_off (d : ℕ) (D : Set ℕ) (w : DivisorEnergyData d D)
    (k : ℕ) (hk : ¬ divisorGridActive d D k) : divisorCompletedTrace d D w k = 0 :=
  w.2 k hk

theorem divisorCompletedTrace_zero (d : ℕ) (D : Set ℕ) (w : DivisorEnergyData d D) :
    divisorCompletedTrace d D w 0 = w.1 0 := by
  simp only [divisorCompletedTrace, cellPrefixL_succ, cellPrefixL_zero, zero_add]

theorem divisorCompletedTrace_succ (d : ℕ) (D : Set ℕ) (w : DivisorEnergyData d D) (k : ℕ) :
    divisorCompletedTrace d D w (k+1) - divisorCompletedTrace d D w k = w.1 (k+1) := by
  unfold divisorCompletedTrace
  rw [cellPrefixL_succ]
  ring

theorem range_divisorEnergyExtension (d : ℕ) (D : Set ℕ) :
    Set.range (divisorEnergyExtension d D) = unitCellSynthesis '' (divisorCellSpace d D) := by
  ext q
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1, w.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

theorem isClosed_range_divisorEnergyExtension (d : ℕ) (D : Set ℕ) :
    IsClosed (Set.range (divisorEnergyExtension d D)) :=
  (divisorEnergyExtension d D).isometry.isUniformInducing.isComplete_range.isClosed

/-- Exact closure in the full physical L² space, with cellular membership retained. -/
theorem closure_range_divisorGridExtension (d : ℕ) (D : Set ℕ) :
    closure (Set.range (divisorGridExtension d D)) = Set.range (divisorEnergyExtension d D) := by
  have he : Set.range (divisorGridExtension d D) =
      unitCellSynthesis '' ((divisorGradient d D).range : Set TraceData) := by
    ext q
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨divisorGradient d D v, ⟨v, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
  rw [he, unitCellSynthesis.isometry.isClosedEmbedding.closure_image_eq,
    range_divisorEnergyExtension]
  change unitCellSynthesis '' ((divisorGradient d D).range.topologicalClosure : Set TraceData) = _
  rw [divisorGradient_closure]

/-- Orthogonal projection constructs admitted data from every ambient cell current. -/
def divisorEnergyProducer (d : ℕ) (D : Set ℕ) (w : TraceData) : DivisorEnergyData d D :=
  ⟨(divisorCellSpace d D).starProjection w, Submodule.starProjection_apply_mem _ _⟩

theorem divisorEnergyProducer_error (d : ℕ) (D : Set ℕ) (w : TraceData) :
    ‖divisorEnergyExtension d D (divisorEnergyProducer d D w)‖^2 +
      ‖w - (divisorEnergyProducer d D w).1‖^2 = ‖w‖^2 := by
  rw [(divisorEnergyExtension d D).norm_map]
  change ‖(divisorCellSpace d D).starProjection w‖^2 +
    ‖w - (divisorCellSpace d D).starProjection w‖^2 = ‖w‖^2
  simpa only [Submodule.starProjection_orthogonal_val] using
    (Submodule.norm_sq_eq_add_norm_sq_starProjection w (divisorCellSpace d D)).symm

theorem divisorEnergyProducer_energy_le (d : ℕ) (D : Set ℕ) (w : TraceData) :
    ‖divisorEnergyExtension d D (divisorEnergyProducer d D w)‖^2 ≤ ‖w‖^2 := by
  have he := divisorEnergyProducer_error d D w
  linarith only [he, sq_nonneg ‖w - (divisorEnergyProducer d D w).1‖]

theorem divisorEnergy_recovery_iff (d : ℕ) (D : Set ℕ) (w : DivisorEnergyData d D) :
    divisorEnergyExtension d D w ∈ Set.range (divisorGridExtension d D) ↔
      Memℓp (divisorCompletedTrace d D w) 2 := by
  constructor
  · rintro ⟨v, hv⟩
    have he : traceGradient v.1 = w.1 := unitCellSynthesis.injective hv
    have ht : divisorCompletedTrace d D w = (v.1 : ℕ → ℝ) := by
      funext k
      rw [divisorCompletedTrace, ← he, cellPrefixL_gradient]
    rw [ht]
    exact lp.memℓp v.1
  · intro hw
    let v : TraceData := ⟨divisorCompletedTrace d D w, hw⟩
    have hv : v ∈ divisorGridDataSpace d D := by
      rw [mem_divisorGridDataSpace_iff]
      exact divisorCompletedTrace_off d D w
    refine ⟨⟨v, hv⟩, ?_⟩
    change unitCellSynthesis (traceGradient v) = unitCellSynthesis w.1
    rw [traceGradient_of_prefix w.1 v (fun _ => rfl)]

/-- Completion changes no data exactly in the uniformly bounded-run regime. -/
theorem divisorEnergy_all_recoverable_iff (d : ℕ) (D : Set ℕ) :
    (∀ w : DivisorEnergyData d D, Memℓp (divisorCompletedTrace d D w) 2) ↔
      divisorGridBoundedRuns d D := by
  rw [← divisorGrid_closed_range_iff, ← closure_eq_iff_isClosed]
  rw [closure_range_divisorGridExtension]
  constructor
  · intro h
    apply Set.Subset.antisymm
    · rintro _ ⟨w, rfl⟩
      exact (divisorEnergy_recovery_iff d D w).mpr (h w)
    · rw [← closure_range_divisorGridExtension]
      exact subset_closure
  · intro he w
    apply (divisorEnergy_recovery_iff d D w).mp
    rw [← he]
    exact ⟨w, rfl⟩

theorem divisorEnergy_escape_exists (d : ℕ) (D : Set ℕ)
    (h : ¬ divisorGridBoundedRuns d D) :
    ∃ w : DivisorEnergyData d D, ¬ Memℓp (divisorCompletedTrace d D w) 2 := by
  classical
  by_contra hn
  apply h ((divisorEnergy_all_recoverable_iff d D).mp ?_)
  intro w
  by_contra hw
  exact hn ⟨w, hw⟩

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
