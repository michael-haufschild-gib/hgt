import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CapacityPolarHorizon
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CofinalInverseCapacityHilbert
import Mathlib

/-!
# The relation-valued face of the capacity-polar horizon

A real Hilbert port tower carries an increasing capacity chart on its finite-dimensional output.
The polar sector of that chart is the set of bounded-capacity directions, and its collapse kernel
is the multivalued part of the closed graph.  The two are orthogonal complements, so the output
splits as an orthogonal direct sum of a finite-cost sector and a vertical ambiguity sector.
-/

open Filter GaloisForLFunctions.HTGeometry
open scoped Topology RealInnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

section RealStage

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable (T : X →ₗ.[ℝ] Y) (S : Submodule ℝ X) (hS : S ≤ T.domain) [FiniteDimensional ℝ S]

theorem portGram_symm_real (z w : Y) :
    ⟪portGram T S hS z, w⟫ = ⟪z, portGram T S hS w⟫ := by
  have h1 := inner_portCoLift_portCoLift T S hS z w
  have h2 := inner_portCoLift_portCoLift T S hS w z
  have h3 : ⟪portGram T S hS z, w⟫ = ⟪w, portGram T S hS z⟫ := real_inner_comm w _
  rw [h3, ← h2, ← h1]
  exact real_inner_comm _ _

theorem portGram_nonneg_real (z : Y) : 0 ≤ ⟪portGram T S hS z, z⟫ := by
  have hnn : (0:ℝ) ≤ portCapacity T S hS z := by
    simp only [portCapacity]
    positivity
  rw [portCapacity_eq] at hnn
  rw [← real_inner_comm (portGram T S hS z) z]
  simpa using hnn

theorem portGram_pos_real (hs : PortFilling T S) (z : Y) (hz : z ≠ 0) :
    0 < ⟪portGram T S hS z, z⟫ := by
  refine lt_of_le_of_ne (portGram_nonneg_real T S hS z) fun hcon => hz ?_
  have hzero : ⟪z, portGram T S hS z⟫ = 0 := by
    rw [real_inner_comm]
    exact hcon.symm
  have hcap : portCapacity T S hS z = 0 := by
    rw [portCapacity_eq]
    simpa using hzero
  have hnorm : ‖((portCoLift T S hS z : T.domain) : X)‖ = 0 := by
    simp only [portCapacity] at hcap
    nlinarith [norm_nonneg ((portCoLift T S hS z : T.domain) : X)]
  have hcl : portCoLift T S hS z = 0 := Subtype.ext (by rwa [norm_eq_zero] at hnorm)
  have hg : portGram T S hS z = 0 := by rw [portGram_apply, hcl, T.map_zero]
  exact portGram_injective T S hS hs (by rw [hg, map_zero])

theorem portGram_mono_real (z : Y) {S' : Submodule ℝ X} (hS' : S' ≤ T.domain)
    [FiniteDimensional ℝ S'] (hSS : S ≤ S') :
    ⟪portGram T S hS z, z⟫ ≤ ⟪portGram T S' hS' z, z⟫ := by
  have h := portCapacity_mono T S hS hS' hSS z
  rw [portCapacity_eq, portCapacity_eq] at h
  rw [← real_inner_comm (portGram T S hS z) z, ← real_inner_comm (portGram T S' hS' z) z]
  simpa using h

end RealStage

section Bridge

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable {T : X →ₗ.[ℝ] Y}

namespace HilbertPortTower

variable (P : HilbertPortTower T)

/-- The capacity chart carried by a real Hilbert port tower. -/
noncomputable def capacityChart : CapacityChart Y where
  gram := fun n => portGram T (P.stage (P.base + n)) (P.toPortTower.stage_le _)
  gram_symm := fun _ z w => portGram_symm_real T _ _ z w
  gram_pos := fun n z hz =>
    portGram_pos_real T _ _ (P.toPortTower.filling_add n) z hz
  gram_mono := fun z _ _ hkl =>
    portGram_mono_real T _ _ z (P.toPortTower.stage_le _)
      (P.mono (Nat.add_le_add_left hkl _))

@[simp] theorem capacityChart_gram (n : ℕ) : P.capacityChart.gram n = P.gram n := rfl

theorem capacityChart_cometric (n : ℕ) : P.capacityChart.cometric n = P.invGram n := by
  ext y
  refine portGram_injective T (P.stage (P.base + n)) (P.toPortTower.stage_le _)
    (P.toPortTower.filling_add n) ?_
  have h1 : P.capacityChart.gram n (P.capacityChart.cometric n y) = y :=
    P.capacityChart.gram_cometric n y
  have h2 : portGram T (P.stage (P.base + n)) (P.toPortTower.stage_le _) (P.invGram n y) = y :=
    portGram_portInvGram T _ _ (P.toPortTower.filling_add n) y
  rw [h2]
  exact h1

theorem capacityChart_cometricLimit : P.capacityChart.cometricLimit = P.limitInvGram := by
  ext y
  refine tendsto_nhds_unique (P.capacityChart.tendsto_cometricLimit y) ?_
  exact (P.tendsto_limitInvGram y).congr fun n => by rw [P.capacityChart_cometric n]

/-- **Relation-valued horizon.**  The multivalued part of the closed graph is the orthogonal
complement of the bounded-capacity sector. -/
theorem multivaluedHorizon_eq_orthogonal_boundedCapacity :
    multivaluedHorizon T = ((P.capacityChart.boundedCapacitySubmodule)ᗮ : Set Y) := by
  rw [P.multivaluedHorizon_eq_ker, CapacityChart.boundedCapacitySubmodule,
    Submodule.orthogonal_orthogonal, P.capacityChart_cometricLimit]

/-- **Exhaustive orthogonal split.**  The output is the orthogonal direct sum of the bounded
capacity sector and the vertical fibre. -/
theorem isCompl_boundedCapacity_horizon :
    IsCompl P.capacityChart.boundedCapacitySubmodule (LinearMap.ker P.limitInvGram) := by
  have h := P.capacityChart.isCompl_boundedCapacity
  rwa [P.capacityChart_cometricLimit] at h

end HilbertPortTower

end Bridge

end HTGeometry.ConstraintMotiveRelativity
