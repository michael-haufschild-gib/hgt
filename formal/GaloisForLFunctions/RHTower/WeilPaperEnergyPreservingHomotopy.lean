import GaloisForLFunctions.RHTower.WeilPaperNativeConvexGeometry
import Mathlib.Topology.Homotopy.Basic

/-!
# Energy-preserving strong deformation to real native laws

Convex interpolation from a law to its realification is a continuous homotopy.
It preserves full energy at every time and fixes the real-test image pointwise.
-/

open MeasureTheory Set Topology
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- Every point in the real-test image is fixed by intrinsic realification. -/
@[simp] theorem paperNativeRealification_of_mem_range (μ : Set.range paperNativeRealification) :
    paperNativeRealification μ.1 = μ.1 := by
  rcases μ with ⟨μ, ν, rfl⟩
  exact paperNativeRealification_idempotent ν

/-- Realification as a continuous map onto its actual real-test image. -/
def paperNativeRealificationRetraction :
    C(Set.range spectralRepresentingMeasure, Set.range paperNativeRealification) :=
  ⟨fun μ => ⟨paperNativeRealification μ, Set.mem_range_self μ⟩,
    continuous_paperNativeRealification.subtype_mk _⟩

@[simp] theorem paperNativeRealificationRetraction_coe
    (μ : Set.range paperNativeRealification) : paperNativeRealificationRetraction μ.1 = μ :=
  Subtype.ext (paperNativeRealification_of_mem_range μ)

/-- A continuous deformation of every native law to its real-test representative. -/
def paperNativeRealificationHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (Set.range spectralRepresentingMeasure))
      ⟨paperNativeRealification, continuous_paperNativeRealification⟩ where
  toFun p := paperNativeConvexCombination p.2 (paperNativeRealification p.2) p.1
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact tendsto_paperNativeConvexCombination
      (continuous_snd.tendsto p)
      ((continuous_paperNativeRealification.comp continuous_snd).tendsto p)
      (continuous_fst.tendsto p)
  map_zero_left μ := paperNativeConvexCombination_zero μ (paperNativeRealification μ)
  map_one_left μ := paperNativeConvexCombination_one μ (paperNativeRealification μ)

/-- Every intermediate law has exactly the original full energy. -/
theorem paperNativeRealificationHomotopy_energy
    (t : Set.Icc (0 : ℝ) 1) (μ : Set.range spectralRepresentingMeasure) :
    paperNativeSpectralEnergy (paperNativeRealificationHomotopy (t, μ)) =
      paperNativeSpectralEnergy μ := by
  change paperNativeSpectralEnergy
    (paperNativeConvexCombination μ (paperNativeRealification μ) t) = _
  rw [paperNativeSpectralEnergy_convexCombination, paperNativeSpectralEnergy_realification]
  ring

/-- Laws in the real-test image remain stationary for the whole deformation. -/
theorem paperNativeRealificationHomotopy_fixed
    (t : Set.Icc (0 : ℝ) 1) (μ : Set.range paperNativeRealification) :
    paperNativeRealificationHomotopy (t, μ.1) = μ.1 := by
  change paperNativeConvexCombination μ.1 (paperNativeRealification μ.1) t = _
  rw [paperNativeRealification_of_mem_range, paperNativeConvexCombination_self]

/-- There is a strong deformation to real native laws preserving every full-energy level. -/
theorem exists_energy_preserving_strong_realification_homotopy :
    ∃ H : ContinuousMap.Homotopy (ContinuousMap.id (Set.range spectralRepresentingMeasure))
      ⟨paperNativeRealification, continuous_paperNativeRealification⟩,
      (∀ t μ, paperNativeSpectralEnergy (H (t, μ)) = paperNativeSpectralEnergy μ) ∧
      ∀ t (μ : Set.range paperNativeRealification), H (t, μ.1) = μ.1 :=
  ⟨paperNativeRealificationHomotopy, paperNativeRealificationHomotopy_energy,
    paperNativeRealificationHomotopy_fixed⟩

end RHTower.WeilWorkPBAP
