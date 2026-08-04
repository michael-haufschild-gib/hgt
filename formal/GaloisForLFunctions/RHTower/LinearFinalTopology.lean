import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order

/-!
# Final topological-module topology of linear stages

For an algebraic module presented by linear maps from topological modules, the
plain final topology need not make addition visibly continuous.  The correct
categorical object in topological modules is the finest topology for which
addition and scalar multiplication are continuous and every stage map is
continuous.  This file constructs that topology and proves its exact universal
property for linear maps.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

universe uR uI uE uV uW

section

variable (R : Type uR) [Semiring R] [TopologicalSpace R]
variable {ι : Type uI} (E : ι → Type uE)
variable [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]
variable [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)]
variable [∀ i, ContinuousSMul R (E i)]
variable (V : Type uV) [AddCommMonoid V] [Module R V]
variable (stage : ∀ i, E i →ₗ[R] V)

/-- Topologies on the recipient which make it a topological module and make
every presentation stage continuous. -/
def linearFinalAdmissibleTopologies : Set (TopologicalSpace V) :=
  {t | @ContinuousAdd V t inferInstance ∧
    @ContinuousSMul R V inferInstance inferInstance t ∧
    ∀ i, @Continuous (E i) V inferInstance t (stage i)}

/-- Finest topological-module topology receiving every linear stage
continuously. -/
@[reducible]
def linearFinalTopology : TopologicalSpace V :=
  sInf (linearFinalAdmissibleTopologies R E V stage)

/-- Addition remains continuous in the final topological-module topology. -/
theorem linearFinalTopology_continuousAdd :
    @ContinuousAdd V (linearFinalTopology R E V stage) inferInstance := by
  apply continuousAdd_sInf
  intro t ht
  exact ht.1

/-- Scalar multiplication remains continuous in the final
topological-module topology. -/
theorem linearFinalTopology_continuousSMul :
    @ContinuousSMul R V inferInstance inferInstance
      (linearFinalTopology R E V stage) := by
  apply continuousSMul_sInf
  intro t ht
  exact ht.2.1

/-- Every presentation stage is continuous into the final topology. -/
theorem linearFinalTopology_stage_continuous (i : ι) :
    @Continuous (E i) V inferInstance
      (linearFinalTopology R E V stage) (stage i) := by
  rw [linearFinalTopology, continuous_sInf_rng]
  intro t ht
  exact ht.2.2 i

variable {W : Type uW} [AddCommMonoid W] [Module R W]
variable (tW : TopologicalSpace W)
variable (hWadd : @ContinuousAdd W tW inferInstance)
variable (hWsmul : @ContinuousSMul R W inferInstance inferInstance tW)

/-- **Linear universal property.** A linear map out of the final
topological-module topology is continuous exactly when its restriction to
every stage is continuous. -/
theorem linearFinalTopology_continuous_iff
    (hWadd : @ContinuousAdd W tW inferInstance)
    (hWsmul : @ContinuousSMul R W inferInstance inferInstance tW)
    (g : V →ₗ[R] W) :
    @Continuous V W (linearFinalTopology R E V stage) tW g ↔
      ∀ i, @Continuous (E i) W inferInstance tW (g.comp (stage i)) := by
  letI : TopologicalSpace V := linearFinalTopology R E V stage
  letI : TopologicalSpace W := tW
  letI : ContinuousAdd W := hWadd
  letI : ContinuousSMul R W := hWsmul
  constructor
  · intro hg i
    exact hg.comp (linearFinalTopology_stage_continuous R E V stage i)
  · intro hstage
    rw [continuous_iff_le_induced]
    apply sInf_le
    refine ⟨continuousAdd_induced g, continuousSMul_induced g, ?_⟩
    intro i
    rw [continuous_induced_rng]
    change Continuous (g.comp (stage i))
    exact hstage i

end

end GaloisForLFunctions.RHTower
