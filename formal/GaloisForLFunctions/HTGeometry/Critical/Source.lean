/-
# The critical source chart

Bundles the source chart of the critical horizon: the principal open of affine space in the raw
coordinates whose fraction field is the critical source field, its finite type and path-connected
complex points, its integrality and local miracle-flatness data over the observation chart, the
global Jacobian factorization and ramification divisor (unramified away from the Schur divisor), the
Schur prime in its presentation, and the explicit marked analytic coordinates. It constructs explicit
raw-coordinate source meridians around both marked torus divisors, the Kummer obstruction from the
two independent coordinate valuations, and the fact that, given full monodromy, any element of the
source field not in the observation field generates it.
-/

import GaloisForLFunctions.HTGeometry.Critical.Source.AnalyticProjectionCoordinates
import GaloisForLFunctions.HTGeometry.Critical.Source.BlockComplexPoints
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartAwaySchurUnramified
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartComplexPoints
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartFinite
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartFractionRing
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartIntegrality
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartJacobian
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartLocalization
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartMiracleFlatnessData
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartObservationTower
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartPresentationEquiv
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartSchurPrime
import GaloisForLFunctions.HTGeometry.Critical.Source.EscapeTransport
import GaloisForLFunctions.HTGeometry.Critical.Source.ExplicitMeridians
import GaloisForLFunctions.HTGeometry.Critical.Source.KummerObstruction
import GaloisForLFunctions.HTGeometry.Critical.Source.LowValuativeIntegrality
import GaloisForLFunctions.HTGeometry.Critical.Source.MeridianAssignments
import GaloisForLFunctions.HTGeometry.Critical.Source.PrimitiveGenerator
import GaloisForLFunctions.HTGeometry.Critical.Source.ReciprocalNumeratorCanonical
import GaloisForLFunctions.HTGeometry.Critical.Source.SubringIntegrality
