import GaloisForLFunctions.RHTower.ArithmeticFormationRecurrenceDescentFusion
import GaloisForLFunctions.RHTower.IntegralCofinalTateGammaBaseChange
import GaloisForLFunctions.HTGeometry.SourceMarkedExactnessCompletion

/-!
# Integral curved Tate formation-properness index

Literal finite Meyer--Tate Xi formation states are exact and their landings converge pointwise in
the Hilbert graph norm to the completed Xi vertical boundary. Pointwise convergence nevertheless
fails to preserve exactness off the critical line. Retaining one fixed source marker in the mixed
provenance topology gives the sharp completion law: the finite states converge to the physical
state exactly when the Gamma evaluation of the universal integral curved Tate determinant
vanishes.

The same index detects formation-completion birth, Roos escape, and failure of compact recurrence
descent. Thus the Laurent determinant is a completion-properness obstruction, not merely another
pointwise scalar receiver. No RH, critical-line, positivity, or integral-landing premise is used.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Target exactness flag: literal finite arithmetic graph is the boundary space and every graph
vector is an admissible cycle. -/
def deningerGammaSixFormationCompletionTargetFlag :
    ExFlag ℂ DeningerGammaSixCofinalSingularGraph :=
  boundaryExactnessFlag deningerGammaSixCofinalFiniteGraph

/-- Finite arithmetic formation landing of one fixed scalar source marker. -/
def deningerGammaSixXiFiniteFormationLanding
    (q : XiZeroCopy) (n : ℕ) :
    ℂ →ₗ[ℂ] DeningerGammaSixCofinalSingularGraph :=
  LinearMap.toSpanSingleton ℂ DeningerGammaSixCofinalSingularGraph
    (deningerGammaSixCofinalMeyerTateCompletedDifferential
      (deningerGammaSixCofinalXiGreenDegreeOneChain
        (⟨2, Nat.prime_two⟩ : Nat.Primes) q n))

/-- Physical landing of the same source marker into the completed Xi vertical boundary. -/
def deningerGammaSixXiPhysicalFormationLanding
    (q : XiZeroCopy) :
    ℂ →ₗ[ℂ] DeningerGammaSixCofinalSingularGraph :=
  LinearMap.toSpanSingleton ℂ DeningerGammaSixCofinalSingularGraph
    (deningerGammaSixCofinalXiGreenVerticalBoundary q)

/-- Source-marked exactness state of one finite Meyer--Tate formation stage. -/
def deningerGammaSixXiFiniteFormationState
    (q : XiZeroCopy) (n : ℕ) :
    SourceMarkedExFlag ℂ ℂ DeningerGammaSixCofinalSingularGraph where
  target := deningerGammaSixFormationCompletionTargetFlag
  landing := deningerGammaSixXiFiniteFormationLanding q n
  landing_mem_cycle _ := Submodule.mem_top

/-- Source-marked exactness state of the physical singular completion. -/
def deningerGammaSixXiPhysicalFormationState
    (q : XiZeroCopy) :
    SourceMarkedExFlag ℂ ℂ DeningerGammaSixCofinalSingularGraph where
  target := deningerGammaSixFormationCompletionTargetFlag
  landing := deningerGammaSixXiPhysicalFormationLanding q
  landing_mem_cycle _ := Submodule.mem_top

/-- Every finite source landing remains a literal finite arithmetic boundary. -/
theorem deningerGammaSixXiFiniteFormationLanding_mem_boundary
    (q : XiZeroCopy) (n : ℕ) (z : ℂ) :
    deningerGammaSixXiFiniteFormationLanding q n z ∈
      deningerGammaSixCofinalFiniteGraph := by
  rw [deningerGammaSixXiFiniteFormationLanding,
    LinearMap.toSpanSingleton_apply]
  apply deningerGammaSixCofinalFiniteGraph.smul_mem
  change deningerGammaSixCofinalMeyerTateCompletedDifferential
      (deningerGammaSixCofinalXiGreenDegreeOneChain
        (⟨2, Nat.prime_two⟩ : Nat.Primes) q n) ∈
    LinearMap.range deningerGammaSixCofinalFiniteGraphAdmission
  rw [deningerGammaSixCofinalXiGreenDegreeOneChain,
    deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom]
  exact ⟨_, rfl⟩

/-- Every finite source-marked formation state is escape-free. -/
theorem deningerGammaSixXiFiniteFormationState_escapeFree
    (q : XiZeroCopy) (n : ℕ) :
    EscapeFree (deningerGammaSixXiFiniteFormationState q n).landing
      (⊤ : Submodule ℂ ℂ)
      (deningerGammaSixXiFiniteFormationState q n).target.boundary := by
  intro y hy
  obtain ⟨z, _hz, rfl⟩ := Submodule.mem_map.mp hy
  exact deningerGammaSixXiFiniteFormationLanding_mem_boundary q n z

/-- Physical escape-freedom is exactly critical-line placement. -/
theorem deningerGammaSixXiPhysicalFormationState_escapeFree_iff
    (q : XiZeroCopy) :
    EscapeFree (deningerGammaSixXiPhysicalFormationState q).landing
      (⊤ : Submodule ℂ ℂ)
      (deningerGammaSixXiPhysicalFormationState q).target.boundary ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    apply (deningerGammaSixCofinalXiGreenVerticalBoundary_mem_finiteGraph_iff q).1
    have hmem := h (Submodule.mem_map_of_mem
      (show (1 : ℂ) ∈ (⊤ : Submodule ℂ ℂ) from Submodule.mem_top))
    simpa [deningerGammaSixXiPhysicalFormationState,
      deningerGammaSixXiPhysicalFormationLanding,
      deningerGammaSixFormationCompletionTargetFlag,
      LinearMap.toSpanSingleton_apply] using hmem
  · intro hline y hy
    obtain ⟨z, _hz, rfl⟩ := Submodule.mem_map.mp hy
    change deningerGammaSixXiPhysicalFormationLanding q z ∈
      deningerGammaSixCofinalFiniteGraph
    rw [deningerGammaSixXiPhysicalFormationLanding,
      LinearMap.toSpanSingleton_apply]
    exact deningerGammaSixCofinalFiniteGraph.smul_mem z
      ((deningerGammaSixCofinalXiGreenVerticalBoundary_mem_finiteGraph_iff q).2 hline)

/-- Pointwise Hilbert-graph convergence holds at every Xi grade, including off line. -/
theorem tendsto_deningerGammaSixXiFiniteFormationLanding
    (q : XiZeroCopy) (z : ℂ) :
    Tendsto (fun n => deningerGammaSixXiFiniteFormationLanding q n z)
      atTop (nhds (deningerGammaSixXiPhysicalFormationLanding q z)) := by
  simpa [deningerGammaSixXiFiniteFormationLanding,
    deningerGammaSixXiPhysicalFormationLanding,
    LinearMap.toSpanSingleton_apply] using
    (tendsto_deningerGammaSixCofinalMeyerTateCompletedDifferential_xiGreenChain
      (⟨2, Nat.prime_two⟩ : Nat.Primes) q).const_smul z

/-- Source-marked provenance convergence of the same finite stages is the critical-line law. -/
theorem deningerGammaSixXiFiniteFormationState_tendsto_iff
    (q : XiZeroCopy) :
    Tendsto (fun n => deningerGammaSixXiFiniteFormationState q n) atTop
        (nhds (deningerGammaSixXiPhysicalFormationState q)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hconv
    have hexact :
        EscapeFree (deningerGammaSixXiPhysicalFormationState q).landing
          (⊤ : Submodule ℂ ℂ)
          (deningerGammaSixXiPhysicalFormationState q).target.boundary :=
      SourceMarkedExFlag.escapeFree_of_tendsto
        (⊤ : Submodule ℂ ℂ) hconv
        (Filter.Eventually.of_forall fun n =>
          deningerGammaSixXiFiniteFormationState_escapeFree q n)
    exact (deningerGammaSixXiPhysicalFormationState_escapeFree_iff q).1 hexact
  · intro hline
    rw [SourceMarkedExFlag.tendsto_iff_eventually_survival_tests]
    intro z hz
    exfalso
    have hexact :=
      (deningerGammaSixXiPhysicalFormationState_escapeFree_iff q).2 hline
    exact hz (hexact (Submodule.mem_map_of_mem
      (show z ∈ (⊤ : Submodule ℂ ℂ) from Submodule.mem_top)))

/-- Gamma evaluation of the universal integral curved Tate determinant at the dyadic Xi grade. -/
def deningerXiIntegralCofinalFormationIndex (q : XiZeroCopy) : ℂ :=
  deningerIntegralGammaEvaluationComplex
    ((2 * (q.1 : ℂ).re - 1) * Real.log 2)
    (Matrix.det deningerIntegralRelativeReflectionDifferential)

/-- Exact radical of the integral formation-completion index. -/
theorem deningerXiIntegralCofinalFormationIndex_eq_zero_iff
    (q : XiZeroCopy) :
    deningerXiIntegralCofinalFormationIndex q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerXiIntegralCofinalFormationIndex,
    deningerIntegralRelativeReflection_determinant_evaluation,
    Complex.ofReal_eq_zero,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  constructor <;> intro h <;> nlinarith

/-- Completion index theorem: source-marked properness is precisely zero integral curvature. -/
theorem deningerGammaSixXiFiniteFormationState_tendsto_iff_index_zero
    (q : XiZeroCopy) :
    Tendsto (fun n => deningerGammaSixXiFiniteFormationState q n) atTop
        (nhds (deningerGammaSixXiPhysicalFormationState q)) ↔
      deningerXiIntegralCofinalFormationIndex q = 0 := by
  rw [deningerGammaSixXiFiniteFormationState_tendsto_iff,
    deningerXiIntegralCofinalFormationIndex_eq_zero_iff]

/-- Nonzero integral index is exactly birth of a new boundary under singular completion. -/
theorem
    deningerGammaSixXiGreenBoundary_mem_formationCompletionBoundary_iff_index_ne_zero
    (q : XiZeroCopy) :
    deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
        deningerGammaSixArithmeticFormationCompletionBoundary ↔
      deningerXiIntegralCofinalFormationIndex q ≠ 0 := by
  rw [deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff]
  exact (not_congr
    (deningerXiIntegralCofinalFormationIndex_eq_zero_iff q)).symm

/-- Compact recurrence descent is the zero-index phase of the same completion object. -/
theorem thetaXiPrimeModularCompactRecurrenceDescent_iff_index_zero
    (q : XiZeroCopy) :
    ThetaXiPrimeModularCompactRecurrenceDescent q ↔
      deningerXiIntegralCofinalFormationIndex q = 0 := by
  rw [thetaXiPrimeModularCompactRecurrenceDescent_iff,
    deningerXiIntegralCofinalFormationIndex_eq_zero_iff]

/-- Closed pointwise fusion of provenance properness, formation escape, and recurrence. -/
theorem deningerXiIntegralCofinalFormationIndex_fusion
    (q : XiZeroCopy) :
    (Tendsto (fun n => deningerGammaSixXiFiniteFormationState q n) atTop
        (nhds (deningerGammaSixXiPhysicalFormationState q)) ↔
      deningerXiIntegralCofinalFormationIndex q = 0) ∧
    (deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
        deningerGammaSixArithmeticFormationCompletionBoundary ↔
      deningerXiIntegralCofinalFormationIndex q ≠ 0) ∧
    (ThetaXiPrimeModularCompactRecurrenceDescent q ↔
      deningerXiIntegralCofinalFormationIndex q = 0) :=
  ⟨deningerGammaSixXiFiniteFormationState_tendsto_iff_index_zero q,
    deningerGammaSixXiGreenBoundary_mem_formationCompletionBoundary_iff_index_ne_zero q,
    thetaXiPrimeModularCompactRecurrenceDescent_iff_index_zero q⟩

/-- Universal provenance continuity of the literal finite formation states is exactly RH. -/
theorem forall_deningerGammaSixXiFiniteFormationState_tendsto_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      Tendsto (fun n => deningerGammaSixXiFiniteFormationState q n) atTop
        (nhds (deningerGammaSixXiPhysicalFormationState q))) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    rw [← xiArithmeticFormationCompletionBoundaryFree_iff_riemannHypothesis]
    intro q hboundary
    have hline :=
      (deningerGammaSixXiFiniteFormationState_tendsto_iff q).1 (h q)
    exact
      ((deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff q).1
        hboundary) hline
  · intro hRH q
    exact (deningerGammaSixXiFiniteFormationState_tendsto_iff q).2
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)

/-- Universal vanishing of the integral formation-completion index is exactly RH. -/
theorem forall_deningerXiIntegralCofinalFormationIndex_eq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, deningerXiIntegralCofinalFormationIndex q = 0) ↔
      RiemannHypothesis := by
  rw [← forall_deningerGammaSixXiFiniteFormationState_tendsto_iff_riemannHypothesis]
  exact forall_congr' fun q =>
    (deningerGammaSixXiFiniteFormationState_tendsto_iff_index_zero q).symm

end


end RHTower
