import GaloisForLFunctions.HTGeometry.DirichletTowerDichotomy
import GaloisForLFunctions.HTGeometry.PrimeResidueValuationAnalyticSuperselection

/-!
# The field of all finite-abscissa Dirichlet series is differential

The realized coefficient derivation preserves finite abscissa. Adjoining the Dirichlet
coordinate and taking field operations therefore gives a differential coefficient field.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance dirichletBaseDifferentialDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance dirichletBaseDifferentialAmbient : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential
local instance dirichletBaseDifferentialComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra
local instance dirichletBaseDifferentialInteger : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

theorem derivationClosed_dirZetaBase : DerivationClosed dirZetaBase := by
  intro x hx
  refine IntermediateField.adjoin_induction (F := ℂ)
    (p := fun y _ => y′ ∈ dirZetaBase) ?_ ?_ ?_ ?_ ?_ hx
  · rintro y (hy | ⟨f, rfl⟩)
    · rw [Set.mem_singleton_iff] at hy
      subst y
      rw [dirCoordMero_deriv]
      exact dirZetaBase.algebraMap_mem _
    · rw [deriv_finiteAbscissaLSeriesToUpperEndMero]
      exact lseries_mem_dirZetaBase _
  · intro c
    rw [deriv_complexConstant]
    exact zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]
    exact add_mem ha hb
  · intro a ha hda
    rw [Derivation.leibniz_inv, smul_eq_mul]
    exact mul_mem (neg_mem (pow_mem (inv_mem ha) 2)) hda
  · intro a b ha hb hda hdb
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem ha hdb) (mul_mem hb hda)

/-- The inherited derivation on the actual Dirichlet coefficient field. -/
abbrev dirZetaBaseDifferential : Differential dirZetaBase :=
  derivationClosedDifferential dirZetaBase derivationClosed_dirZetaBase

end

end GaloisForLFunctions.HTGeometry
