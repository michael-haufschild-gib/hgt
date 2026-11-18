# Cancellation over the horizon of a coprime prime product

For each ordinary prime p>F and v coprime to p with pv≤U, choose an arbitrary half-open interval of integer horizons. Retain the signed PVC weight g_D(v) W_R(⌊k/(pv)⌋) only on that interval. For U,R≥1 the resulting log-prime weighted sum S(k) satisfies, on every interval I,
$$
\left|\sum_{k\in I} S(k)\right|
 \ll (1+\operatorname{mass}(D+1))(1+\operatorname{mass}(R))(1+R^2)\,U^2(1+\log U).
$$
The constant is absolute and independent of all the endpoints.

For q=pv, the discrete mean of {k/(dq)}−½ is −1/(2dq). The corrected divisor stencil annihilates 1/d. The primitive of the remaining centered ramp ranges between −dq/8 and zero, so only the two incomplete periods contribute. The stencil has d≤128(128R²+1). Sum the bound over at most U/p complements per prime, use q≤U, and apply the reciprocal-prime estimate.

Lean declarations are [centeredPrimeWeight_horizon_interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/HorizonCancellation.lean) and [clippedPrimeProducts_interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ClippedProductMeans.lean).

At conductor \(n\), the first and second mesh differences of the signed spline cost \(O(n^{-3})\) and \(O(n^{-5})\). Abel summation through the common \(O(n^2)\) horizon therefore charges the clipped products \(O_{D,R}(U^2(1+\log U)/n^3)\), uniformly in their endpoints. For \(U\le n\lfloor\sqrt n\rfloor\) the entire contribution is \(O_{D,R}(1+\log U)\). [spline_three_quarter_product_bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheThreeQuarterProductWindow.lean)

At unit stencil cutoffs, a product \(q=pv\) occurs exactly for \(q\le k<\lceil q/2\rceil^2\). Write \(L\) for the common spline horizon, \(D_n\) for dyadic prime contact and \(T_n(U,M)\) for the reading restricted to \(q>U,\ v\le M\). Uniformly for \(n,U\ge1\) and \(M\ge0\),
\[
|D_n-T_n(U,M)|\ll(1+\log L)^6+\frac{U^2(1+\log U)}{n^3}+\frac{n(1+\log L)}{M+1}.
\]
The first cutoff uses the exact horizon interval. For the second, bounded coprime cofactor prefixes control the remaining quotient cells. [dyadicPrimeContact_capped_upper_product_tail](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheCompleteUpperProductTail.lean)
