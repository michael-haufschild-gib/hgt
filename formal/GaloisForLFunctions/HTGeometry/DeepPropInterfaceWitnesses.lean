import GaloisForLFunctions.HTGeometry.InfiniteGeneratorSupportLaw
import GaloisForLFunctions.HTGeometry.ConstitutivePrimitiveExecutionGenesis
import GaloisForLFunctions.HTGeometry.ChronometricRegionLocalization
import GaloisForLFunctions.HTGeometry.OrderUnitSeminorm
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolUniversalMatrixField
import GaloisForLFunctions.HTGeometry.ConstraintLaplacian

/-!
# Deeper proposition-interface witnesses

These witnesses exercise the substantive structure of their interfaces: full-region unique
continuation, the Archimedean real order unit, and a universal free field whose complete selected
derivation jet is algebraically independent.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The empty site packet is reachable by the unique word of depth zero. -/
theorem generatorReachableAtDepth_empty
    {E V : Type*} [DecidableEq V] (generatorSupport : E → Finset V) :
    GeneratorReachableAtDepth generatorSupport ∅ 0 := by
  refine ⟨Fin.elim0, ?_⟩
  simp

/-- An empty admitted constraint forbids every positive primitive, hence gives every degree bound. -/
theorem primitiveDegreeBound_empty_constraint
    {α : Type*} [DecidableEq α] (D : ℕ) :
    PrimitiveDegreeBound ({∅} : Finset (Finset α)) D := by
  intro m a hp
  have hzero := hp.2.1 ∅ (by simp)
  simp at hzero
  omega

namespace ChronometricMetricField

/-- Restriction to the full event set has unique continuation. -/
theorem uniqueContinuation_univ
    {Event Tangent : Type*} [AddCommGroup Tangent] [Module ℝ Tangent] :
    UniqueContinuation (Set.univ : Set Event) Tangent := by
  intro g h hres
  apply ChronometricMetricField.ext
  funext x
  have hx := congrArg
    (fun k : ChronometricMetricField (Set.univ : Set Event) Tangent =>
      k.form ⟨x, Set.mem_univ x⟩) hres
  exact hx

end ChronometricMetricField

namespace OrderUnit

/-- The standard real order unit is Archimedean. -/
theorem isArchimedean_one_real : IsArchimedean (1 : ℝ) := by
  intro v hsmall
  by_contra hnot
  have hv : 0 < v := lt_of_not_ge hnot
  have hhalf := hsmall (v / 2) (half_pos hv)
  norm_num at hhalf
  linarith

end OrderUnit

/-- Identity symbols realize complete derivation independence in the universal matrix-shift field. -/
theorem derivationIndependentOver_universalMatrixIdentity
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    DerivationIndependentOver K
      (universalMatrixShiftDerivation (fun _ : ℕ => (1 : Matrix ι ι K)))
      (universalShiftAncestor (K := K) 0) := by
  apply (universalMatrixShift_derivationIndependentOver_iff
    (fun _ : ℕ => (1 : Matrix ι ι K))).2
  intro n
  simp

section ConstraintLaplacian

open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {ι : Type*} [Fintype ι]

/-- A family accepting every vector has a uniform precision gap: its transverse sector is zero. -/
theorem hasUniformPrecisionGap_of_jointSector_eq_top
    (U : ι → Submodule 𝕜 H) [∀ i, (U i).HasOrthogonalProjection]
    (hU : jointSector U = ⊤) : HasUniformPrecisionGap U := by
  refine ⟨1, zero_lt_one, fun x hx => ?_⟩
  have hx0 : x = 0 := by
    rw [hU, Submodule.top_orthogonal_eq_bot] at hx
    simpa using hx
  subst x
  simp [constraintEnergy]

/-- The universal observer family unconditionally realizes a uniform precision gap. -/
theorem hasUniformPrecisionGap_top_observers :
    HasUniformPrecisionGap (fun _ : ι => (⊤ : Submodule 𝕜 H)) := by
  apply hasUniformPrecisionGap_of_jointSector_eq_top
  simp [jointSector]

end ConstraintLaplacian

end GaloisForLFunctions.HTGeometry
