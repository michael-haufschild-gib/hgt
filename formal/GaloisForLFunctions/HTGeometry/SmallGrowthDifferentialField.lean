import GaloisForLFunctions.HTGeometry.SmallGrowthDerivative
import GaloisForLFunctions.HTGeometry.LocalizationDerivationMap
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialField

open Complex Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Ordinary differentiation on the global entire-function fraction field. -/
@[reducible]
noncomputable def entireFieldOneDifferential : Differential (EntireField ℂ) where
  deriv := fieldDirDerivation (1 : ℂ)

/-- Ordinary differentiation restricted to Nagoshi's small-growth field. -/
@[reducible]
noncomputable def smallGrowthDifferential : Differential SmallGrowthMeromorphicField where
  deriv :=
    { toLinearMap :=
        { toFun := fun x =>
            ⟨fieldDirDerivation (1 : ℂ) x.1,
              HasSmallGrowth.fieldDirDerivation_one x.2⟩
          map_add' := fun x y => Subtype.ext
            (map_add (fieldDirDerivation (1 : ℂ)) x.1 y.1)
          map_smul' := fun n x => Subtype.ext
            ((fieldDirDerivation (1 : ℂ)).map_smul n x.1) }
      map_one_eq_zero' := Subtype.ext
        (fieldDirDerivation (1 : ℂ)).map_one_eq_zero
      leibniz' := fun x y => Subtype.ext
        ((fieldDirDerivation (1 : ℂ)).leibniz x.1 y.1) }

@[simp]
theorem smallGrowthDifferential_apply (x : SmallGrowthMeromorphicField) :
    letI := smallGrowthDifferential
    x′ = ⟨fieldDirDerivation (1 : ℂ) x.1,
      HasSmallGrowth.fieldDirDerivation_one x.2⟩ := by
  rfl

/-- Restriction of an entire derivative to the upper end is the upper-end germ derivative. -/
theorem entireToUpperEndAnalytic_entireDirDeriv_one (a : entireSubring ℂ) :
    entireToUpperEndAnalytic (entireDirDeriv (1 : ℂ) a) =
      upperEndAnalyticDeriv (entireToUpperEndAnalytic a) := by
  apply Subtype.ext
  rw [upperEndAnalyticDeriv_coe, entireToUpperEndAnalytic_coe,
    entireToUpperEndAnalytic_coe]
  change (entireDirectionalDerivative (1 : ℂ) (a : ℂ → ℂ) :
      Germ upperEndFilter ℂ) =
    upperEndGermDeriv ((a : ℂ → ℂ) : Germ upperEndFilter ℂ)
  rw [upperEndGermDeriv_coe, smallGrowth_entireDirectionalDerivative_one]

/-- Global fraction-field differentiation commutes with restriction to upper-end meromorphic
germs. -/
theorem entireFieldToUpperEndMero_fieldDirDerivation_one (x : EntireField ℂ) :
    upperEndMeroFieldDifferential.deriv (entireFieldToUpperEndMero x) =
      entireFieldToUpperEndMero (fieldDirDerivation (1 : ℂ) x) := by
  symm
  apply localization_ringHom_derivation_commutes_of_base
    (M := nonZeroDivisors (entireSubring ℂ))
    (Dₛ := fieldDirDerivation (1 : ℂ))
    (Dₜ := upperEndMeroFieldDifferential.deriv)
    (phi := entireFieldToUpperEndMero)
  intro a
  rw [smallGrowth_fieldDirDerivation_algebraMap,
    entireFieldToUpperEndMero_algebraMap,
    entireFieldToUpperEndMero_algebraMap]
  letI : IsDomain upperEndAnalyticSubring := isDomain_upperEndAnalyticSubring
  letI : Differential upperEndMeroField := upperEndMeroFieldDifferential
  rw [show upperEndMeroFieldDifferential.deriv = Differential.deriv from rfl,
    upperEndMeroFieldDifferential_algebraMap,
    entireToUpperEndAnalytic_entireDirDeriv_one]

/-- The canonical upper-end realization is a differential algebra over the actual small-growth
differential field. -/
theorem smallGrowthDifferentialAlgebra :
    letI := smallGrowthDifferential
    letI : IsDomain upperEndAnalyticSubring := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    DifferentialAlgebra SmallGrowthMeromorphicField upperEndMeroField := by
  letI := smallGrowthDifferential
  letI : IsDomain upperEndAnalyticSubring := isDomain_upperEndAnalyticSubring
  letI := upperEndMeroFieldDifferential
  refine ⟨fun x => ?_⟩
  change upperEndMeroFieldDifferential.deriv
      (entireFieldToUpperEndMero x.1) =
    entireFieldToUpperEndMero (fieldDirDerivation (1 : ℂ) x.1)
  exact entireFieldToUpperEndMero_fieldDirDerivation_one x.1

end

end GaloisForLFunctions.HTGeometry
