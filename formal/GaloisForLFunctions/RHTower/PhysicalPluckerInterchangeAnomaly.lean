import GaloisForLFunctions.HTGeometry.PurificationTransferInterchangeAnomaly
import GaloisForLFunctions.RHTower.IntegralNuclearScaleGermOrgans

/-!
# The interchange anomaly of the physical Plücker density

For the normalized physical-overlap Plücker density `T` and its marked unit purification `Ψ`
(`Tr_R |Ψ⟩⟨Ψ| = T`), the completion/closure square has anomaly
`𝒜_{ε,c}(T) = E_ε(cT) - c/(ε+c) T`, which is positive, tends strongly to `I - T`, and whose
boundary-corona germs satisfy the Poisson complement law
`‖[𝒜_{•,t²}] - [𝒜_{•,u²}]‖² + P(t,u) = 1`.  Fixing the theta germ `[𝒜_{•,1}]` selects `c = 1`,
and reflection invariance `[𝒜_{•,pᵃ}] = [𝒜_{•,p⁻ᵃ}]` forces `a = 0`.
-/

open Filter Topology
open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

/-- **(PBTIA.1)–(PBTIA.2).**  `0 ≤ T ≤ I`, and `P = |Ψ⟩⟨Ψ|` is a rank-one projection with
`Tr_R P = T`. -/
theorem physicalPlucker_canonicalSquare :
    normalizedPhysicalPluckerOperator.IsPositive ∧ (1 - normalizedPhysicalPluckerOperator).IsPositive ∧
      ‖pluckerPurification‖ = 1 ∧
      rankOne ℂ pluckerPurification pluckerPurification ∘L
          rankOne ℂ pluckerPurification pluckerPurification =
        rankOne ℂ pluckerPurification pluckerPurification ∧
      IsPartialTrace (rankOne ℂ pluckerPurification pluckerPurification)
        normalizedPhysicalPluckerOperator :=
  ⟨normalizedPhysicalPluckerOperator_isPositive,
    isPositive_one_sub_of_norm_le_one normalizedPhysicalPluckerOperator_isPositive
      norm_normalizedPhysicalPluckerOperator_lt_one.2.le,
    norm_pluckerPurification, rankOne_comp_rankOne_self_of_norm_eq_one norm_pluckerPurification,
    pluckerPurification_isPartialTrace⟩

/-- **(PBTIA.4)–(PBTIA.6).**  The two paths around the completion/closure square and their
defect. -/
theorem physicalInterchangeAnomaly_square {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    IsPartialTrace (c • rankOne ℂ pluckerPurification pluckerPurification)
        (c • normalizedPhysicalPluckerOperator) ∧
      IsPartialTrace (positiveBoundaryTransfer (c • rankOne ℂ pluckerPurification
          pluckerPurification) ε) ((c / (ε + c)) • normalizedPhysicalPluckerOperator) ∧
      interchangeAnomaly normalizedPhysicalPluckerOperator c ε =
        positiveBoundaryTransfer (c • normalizedPhysicalPluckerOperator) ε -
          (c / (ε + c)) • normalizedPhysicalPluckerOperator :=
  ⟨(isPartialTrace_completion_square norm_pluckerPurification pluckerPurification_isPartialTrace
      hc hε).1,
    (isPartialTrace_completion_square norm_pluckerPurification pluckerPurification_isPartialTrace
      hc hε).2, rfl⟩

/-- **Theorem PBTIA-A.**  The physical interchange anomaly is positive. -/
theorem physicalInterchangeAnomaly_isPositive {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    (interchangeAnomaly normalizedPhysicalPluckerOperator c ε).IsPositive :=
  interchangeAnomaly_isPositive normalizedPhysicalPluckerOperator_isPositive
    norm_normalizedPhysicalPluckerOperator_lt_one.2.le hc hε

/-- **(PBTIA.9).**  The physical residual tends to `T` in trace norm. -/
theorem tendsto_traceNorm_physicalResidual_sub {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε => traceNorm GammaSewnCriticalPhysicalPluckerHilbert
      ((c / (ε + c)) • normalizedPhysicalPluckerOperator - normalizedPhysicalPluckerOperator))
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_traceNorm_residual_sub _ hc

/-- **Theorem PBTIA-B, (PBTIA.12).**  The physical anomaly tends strongly to `I - T`. -/
theorem tendsto_physicalInterchangeAnomaly_apply {c : ℝ} (hc : 0 < c)
    (v : GammaSewnCriticalPhysicalPluckerHilbert) :
    Tendsto (fun ε => interchangeAnomaly normalizedPhysicalPluckerOperator c ε v) (𝓝[>] 0)
      (𝓝 (v - normalizedPhysicalPluckerOperator v)) :=
  tendsto_interchangeAnomaly_apply normalizedPhysicalPluckerOperator_isPositive
    normalizedPhysicalPluckerOperator_injective hc v

/-- The anomaly germ `[𝒜_{•,c}(T)]` of the physical density. -/
def physicalAnomalyGerm {c : ℝ} (hc : 0 < c) : BoundaryCorona GammaSewnCriticalPhysicalPluckerHilbert :=
  (anomalyHistory normalizedPhysicalPluckerOperator normalizedPhysicalPluckerOperator_isPositive
    normalizedPhysicalPluckerOperator_isCompact hc : BoundaryCorona _)

/-- **(PBTIA.13).**  `‖[𝒜_{•,c}] - [𝒜_{•,d}]‖ = |√c - √d|/(√c + √d)`. -/
theorem norm_physicalAnomalyGerm_sub {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ‖physicalAnomalyGerm hc - physicalAnomalyGerm hd‖ = |germContrast c d| :=
  norm_anomalyGerm_sub normalizedPhysicalPluckerOperator_isPositive
    normalizedPhysicalPluckerOperator_isCompact normalizedPhysicalPluckerOperator_injective
    not_finiteDimensional_pluckerHilbert hc hd

/-- **(PBTIA.16).**  Open anomaly distance squared plus closed Poisson overlap is one. -/
theorem norm_sq_physicalAnomalyGerm_add_poisson {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    ‖physicalAnomalyGerm (pow_pos ht 2) - physicalAnomalyGerm (pow_pos hu 2)‖ ^ 2 +
      poissonScaleHistoryGram t u = 1 := by
  rw [physicalAnomalyGerm, physicalAnomalyGerm,
    anomalyGerm_sub_eq_scaleGerm_sub normalizedPhysicalPluckerOperator_isPositive
      normalizedPhysicalPluckerOperator_isCompact]
  exact norm_sq_pluckerScaleGerm_add_poisson ht hu

/-- **(PBTIA.14), (PBTIA.20).**  The anomaly germ fixes the polarization; the theta germ selects
`c = 1`. -/
theorem physicalAnomalyGerm_eq_iff {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    physicalAnomalyGerm hc = physicalAnomalyGerm hd ↔ c = d :=
  anomalyGerm_eq_iff normalizedPhysicalPluckerOperator_isPositive
    normalizedPhysicalPluckerOperator_isCompact normalizedPhysicalPluckerOperator_injective
    not_finiteDimensional_pluckerHilbert hc hd

/-- **(PBTIA.17), (PBTIA.21).**  At a prime `p` the oriented anomaly distance of the direct and
reflected scales is `(pᵃ-1)/(pᵃ+1)`, and reflection invariance of the anomaly germ forces
`a = 0`. -/
theorem physicalAnomalyGerm_prime_reflection (p : Nat.Primes) (a : ℝ) :
    germContrast ((p : ℝ) ^ a) ((p : ℝ) ^ (-a)) = ((p : ℝ) ^ a - 1) / ((p : ℝ) ^ a + 1) ∧
      (physicalAnomalyGerm (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos : (0 : ℝ) < p) a) =
          physicalAnomalyGerm
            (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos : (0 : ℝ) < p) (-a)) ↔ a = 0) :=
  ⟨(germContrast_rpow_reflection (by exact_mod_cast p.2.pos) a).1,
    anomalyGerm_rpow_reflection_iff normalizedPhysicalPluckerOperator_isPositive
      normalizedPhysicalPluckerOperator_isCompact normalizedPhysicalPluckerOperator_injective
      not_finiteDimensional_pluckerHilbert (by exact_mod_cast p.2.one_lt) a⟩

end RHTower.HedenmalmThetaSource
