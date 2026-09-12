import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexQuadratic
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexMixedQuadratic

/-!
# Polarization of the quadratic Einstein coefficient

The mixed quadratic Einstein variation evaluated twice on the same metric jet is definitionally
the quadratic variation of that jet.  Every scalar–scalar or vector–vector second-order source is
therefore the mixed coefficient with both slots equal, so the mixed component machinery applies
to same-sector products without a separate expansion.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet

variable {d : ℕ}

theorem MixedQuadratic.inverse_self (J K : CoordinateMetricTwoJet d ℂ) :
    MixedQuadratic.inverse J K K = Quadratic.inverse J K := rfl

theorem MixedQuadratic.inverseSpatial_self (J K : CoordinateMetricTwoJet d ℂ) (k : Fin d) :
    MixedQuadratic.inverseSpatial J K K k = Quadratic.inverseSpatial J K k := rfl

theorem MixedQuadratic.connection_self (J K : CoordinateMetricTwoJet d ℂ) (u i j : Fin d) :
    MixedQuadratic.connection J K K u i j = Quadratic.connection J K u i j := rfl

theorem MixedQuadratic.connectionSpatial_self (J K : CoordinateMetricTwoJet d ℂ) (k u i j : Fin d) :
    MixedQuadratic.connectionSpatial J K K k u i j = Quadratic.connectionSpatial J K k u i j := rfl

theorem MixedQuadratic.curvature_self (J K : CoordinateMetricTwoJet d ℂ) (u i k l : Fin d) :
    MixedQuadratic.curvature J K K u i k l = Quadratic.curvature J K u i k l := rfl

theorem MixedQuadratic.ricci_self (J K : CoordinateMetricTwoJet d ℂ) (i j : Fin d) :
    MixedQuadratic.ricci J K K i j = Quadratic.ricci J K i j := rfl

theorem MixedQuadratic.scalar_self (J K : CoordinateMetricTwoJet d ℂ) :
    MixedQuadratic.scalar J K K = Quadratic.scalar J K := rfl

/-- The same-jet mixed Einstein coefficient is the quadratic Einstein coefficient. -/
theorem MixedQuadratic.einstein_self (J K : CoordinateMetricTwoJet d ℂ) (i j : Fin d) :
    MixedQuadratic.einstein J K K i j = Quadratic.einstein J K i j := rfl

end GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet
