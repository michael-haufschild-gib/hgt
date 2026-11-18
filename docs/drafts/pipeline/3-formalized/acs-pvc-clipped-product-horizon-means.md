# Cancellation over the horizon of a coprime prime product

For each ordinary prime p>F and v coprime to p with pv≤U, choose an arbitrary half-open interval of integer horizons. Retain the signed PVC weight g_D(v) W_R(⌊k/(pv)⌋) only on that interval. For U,R≥1 the resulting log-prime weighted sum S(k) satisfies, on every interval I,
$$
\left|\sum_{k\in I} S(k)\right|
 \ll (1+\operatorname{mass}(D+1))(1+\operatorname{mass}(R))(1+R^2)\,U^2(1+\log U).
$$
The constant is absolute and independent of all the endpoints.

For q=pv, the discrete mean of {k/(dq)}−½ is −1/(2dq). The corrected divisor stencil annihilates 1/d. The primitive of the remaining centered ramp ranges between −dq/8 and zero, so only the two incomplete periods contribute. The stencil has d≤128(128R²+1). Sum the bound over at most U/p complements per prime, use q≤U, and apply the reciprocal-prime estimate.

Lean declarations are [centeredPrimeWeight_horizon_interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/HorizonCancellation.lean) and [clippedPrimeProducts_interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ClippedProductMeans.lean).
