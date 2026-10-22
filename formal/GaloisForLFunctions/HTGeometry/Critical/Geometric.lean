/-
# Geometric sheets and full monodromy of the critical horizon

Bundles the field-theoretic monodromy of the critical horizon: the normal closure of the source field
over the observation field, the geometric sheets (observation-field embeddings of the source field)
and the Galois action on them. The submodules prove the action is faithful and transitive, that the
exact extension degree and sheet count equal the critical binomial multiplicity (valuative reduction
at the common-scale arc place is a bijection onto pure factorisations), that the action is primitive,
and that the geometric monodromy is the full symmetric group: over `ℂ` for `m, n >= 2`
(`criticalGeometricMonodromy_eq_top`) and over every algebraically closed characteristic-zero field
for all positive `m, n` (`criticalGeometricMonodromy_eq_top_charZero`). Alternative endgames via
Jordan's criterion and generation by transpositions are also recorded.
-/

import GaloisForLFunctions.HTGeometry.Critical.Geometric.DegreeExact
import GaloisForLFunctions.HTGeometry.Critical.Geometric.FieldPrimitivity
import GaloisForLFunctions.HTGeometry.Critical.Geometric.Monodromy
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyAllFields
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyDegreeTwo
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyFaithful
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyFull
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyJordan
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromySwapGeneration
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyTransitive
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalFibre
import GaloisForLFunctions.HTGeometry.Critical.Geometric.SheetArcReductionEquiv
import GaloisForLFunctions.HTGeometry.Critical.Geometric.SheetFibre
import GaloisForLFunctions.HTGeometry.Critical.Geometric.SheetOccupationEquiv
import GaloisForLFunctions.HTGeometry.Critical.Geometric.SheetUpperBound
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
