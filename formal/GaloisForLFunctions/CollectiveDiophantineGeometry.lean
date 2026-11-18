import GaloisForLFunctions.CollectiveDiophantineGeometry.AbsoluteValuesForceHeavyReturns
import GaloisForLFunctions.CollectiveDiophantineGeometry.BoundedCoordinateElimination
import GaloisForLFunctions.CollectiveDiophantineGeometry.CoordinateIntersectionRank
import GaloisForLFunctions.CollectiveDiophantineGeometry.CollectiveAuxiliaryConstruction
import GaloisForLFunctions.CollectiveDiophantineGeometry.CollectiveExtrapolation
import GaloisForLFunctions.CollectiveDiophantineGeometry.CollectiveLogarithmBound
import GaloisForLFunctions.CollectiveDiophantineGeometry.CollectiveRankDepth
import GaloisForLFunctions.CollectiveDiophantineGeometry.FiniteTimeReturnCounts
import GaloisForLFunctions.CollectiveDiophantineGeometry.FixedHeightPrimeMass
import GaloisForLFunctions.CollectiveDiophantineGeometry.HereditaryRankBounds
import GaloisForLFunctions.CollectiveDiophantineGeometry.OrthogonalUnimodularFrames
import GaloisForLFunctions.CollectiveDiophantineGeometry.RationalSimplexDeterminants
import GaloisForLFunctions.CollectiveDiophantineGeometry.ReciprocalRankBounds
import GaloisForLFunctions.CollectiveDiophantineGeometry.TwoSidedGapIteration
import GaloisForLFunctions.CollectiveDiophantineGeometry.WeightedCoordinateSeparation
import GaloisForLFunctions.CollectiveDiophantineGeometry.WeightedReturnCounts

/-!
# Collective Diophantine geometry of the prime logarithms

The programme studies growing families of prime phases and their returns.
Its two-sided gap theorem supplies the sign-free receiver: an absolute
prime-degree trace bound determines the zero width. Producing that bound
from collective phase arithmetic remains the central problem. The fixed-height
prime-mass law calibrates which logarithmic mass fractions can admit a
growing lower bound for returns.
Bounded integer dilations transfer heavy-return counts to absolute large-value
counts with constants independent of the number of prime coordinates.
Maximal-minor elimination bounds the rational span of integer near relations,
using only codimension plus one logarithms. Scalar coordinate slicing supplies
cardinality bounds and separates those counts from collective span control.
Collective integral auxiliaries retain every prime frequency while reducing
the jet dimension by the rank of the small-form family. Their explicit
parameters preserve this gain through the integer-kernel construction
and analytic extrapolation, yielding a simultaneous logarithm lower bound.
Its exponent has reciprocal-rank dependence and gives a uniform rank profile
for the whole approximation body.
Bounded integer elimination preserves the exact rational coordinate intersection,
with explicit height and value losses for an independent spanning family.
One arithmetic floor bounds every coordinate intersection by half its support
dimension. A minimum-weight coordinate basis and Hall matching then retain
half of any nonnegative prime weight on separated coordinates.
Injective coordinate projection and the Fejér window inequality turn that
profile into finite-time return-measure bounds, uniform in target phase and
dimension, with an explicit polynomial observation horizon.
Positive products of geometric kernels give weighted heavy-return counts,
with exponential decay in total mass divided by maximum coordinate weight.
-/
