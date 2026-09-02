import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixCentralScalarRelationNoGo

/-!
# Fixed-reader rigidity for arbitrary Gamma-six relations

The central-scalar relation obstruction leaves open a target with non-scalar, noncommutative, or
partially defined dynamics.  None of that target machinery matters once the relation is required to
land at Route L's already fixed physical reader.

The universal theorem below does not assume a target operator at all.  It uses only one relation
point and one proposed covariant output.  If the reader descends through the relation's output
fibres, reads the proposed output with eigenvalue `v`, and is nonzero on the original class, then
the source scalar is exactly `v`.  Closedness, boundedness, topology, single-valuedness, and a total
target action are absent.

For the literal Gamma-six source and a fixed-reader value, `v = 1`; the Xi copy is therefore on the
critical line.  Hence singular, multivalued, operator-valued, and noncommutative target dynamics do
not evade the holonomy wall while the Burnol/Deninger reader remains a well-defined fixed quotient
reader.  A survivor must change reader holonomy, make vertical ambiguity physically readable, leave
real-linearity, or change domain/fibre.
-/

open Complex

namespace RHTower

noncomputable section

/-- Reader-level Schur rigidity for an arbitrary multivalued linear relation.  A nonzero descended
reader can carry one scalar-covariant source class only into the same reader eigencharacter. -/
theorem linearRelation_covariant_nonzero_reader_scalar_eq
    {𝕜 X Y : Type*} [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (R : Submodule 𝕜 (X × Y)) (tau : Y →ₗ[𝕜] 𝕜)
    (u v : 𝕜) (x : X) (y y' : Y)
    (hxy : (x, y) ∈ R)
    (hcov : (u • x, y') ∈ R)
    (hverticalReader : ∀ w, ((0 : X), w) ∈ R → tau w = 0)
    (hreaderCovariance : tau y' = v * tau y)
    (hread : tau y ≠ 0) :
    u = v := by
  have hcommon := R.smul_mem u hxy
  have hvertical : ((0 : X), y' - u • y) ∈ R := by
    simpa using R.sub_mem hcov hcommon
  have hzero := hverticalReader (y' - u • y) hvertical
  rw [map_sub, hreaderCovariance, map_smul] at hzero
  simp only [smul_eq_mul] at hzero
  have hfactor : (v - u) * tau y = 0 := by
    rw [sub_mul]
    exact hzero
  have hvu : v - u = 0 := (mul_eq_zero.mp hfactor).resolve_right hread
  exact (sub_eq_zero.mp hvu).symm

/-- **[L FIXED-READER RELATION ROUTE-CLASS KILL].**  Let an arbitrary real-linear relation carry
one literal Gamma-six source class to any proposed target output.  If the fixed physical reader is
well-defined on the relation quotient, unchanged on that output, and nonzero on the class, then the
Xi copy is on the critical line.  No target operator or regularity assumption is used. -/
theorem
    sourceHorizontalGammaSixPhysical_fixedReader_relation_nonzero_forces_criticalLine
    {X Y : Type*}
    [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (q : XiZeroCopy)
    (R : Submodule ℝ (X × Y))
    (tau : Y →ₗ[ℝ] ℝ)
    (x : X) (y y' : Y)
    (hxy : (x, y) ∈ R)
    (hcov : (sourceHorizontalGammaSixPhysicalHolonomy q • x, y') ∈ R)
    (hverticalReader : ∀ w, ((0 : X), w) ∈ R → tau w = 0)
    (hreaderInvariant : tau y' = tau y)
    (hread : tau y ≠ 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  apply (sourceHorizontalGammaSixPhysicalHolonomy_eq_one_iff q).1
  apply linearRelation_covariant_nonzero_reader_scalar_eq
    R tau (sourceHorizontalGammaSixPhysicalHolonomy q) 1 x y y'
    hxy hcov hverticalReader
  · simpa using hreaderInvariant
  · exact hread

end

end RHTower
