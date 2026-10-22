/-
# The critical observation field, coordinate ring and chart

Bundles the observation side of the critical horizon: the concrete source and observation function
fields inside the generic jet field, the polynomial observation coordinate ring and its marked chart
(a localization, hence integrally closed, over which all raw and reciprocal coordinates are integral),
the identification of the chart with a standard torus-affine chart `(G_m)^2 x A^(m+n-2)` and of its
complex points, and a nontrivial cyclic character for every nontrivial connected finite cover. It also
computes the observation Jacobian in raw differentials (identity block and rectangular Schur Toeplitz
block via `dY = -Y^2 dX`), its determinant and minors, the cotangent basis at the Schur place, and the
nonzero conormal direction of the branch divisor.
-/

import GaloisForLFunctions.HTGeometry.Critical.Observation.ChartRing
import GaloisForLFunctions.HTGeometry.Critical.Observation.ComplexPoints
import GaloisForLFunctions.HTGeometry.Critical.Observation.ConnectedCover
import GaloisForLFunctions.HTGeometry.Critical.Observation.ConormalBase
import GaloisForLFunctions.HTGeometry.Critical.Observation.CoordinateRing
import GaloisForLFunctions.HTGeometry.Critical.Observation.CotangentBasis
import GaloisForLFunctions.HTGeometry.Critical.Observation.Field
import GaloisForLFunctions.HTGeometry.Critical.Observation.JacobianBlocks
import GaloisForLFunctions.HTGeometry.Critical.Observation.JacobianDet
import GaloisForLFunctions.HTGeometry.Critical.Observation.JacobianMinor
import GaloisForLFunctions.HTGeometry.Critical.Observation.JacobianRecip
import GaloisForLFunctions.HTGeometry.Critical.Observation.TorusChartEquiv
