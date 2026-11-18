# The square-generator product and the signed capped conductor prefix

Let \(P_N\) be the product of the ordinary-prime square generators through \(N\). Write \(R_n=T_n(n\lfloor\sqrt n\rfloor,n)\) for the original signed two-dilation reading restricted to coprime products \(pv>n\lfloor\sqrt n\rfloor\) with \(v\le n\). For every terminal \(N\ge1\),
\[
\left|\log P_N-\sum_{n=1}^N n^2R_n\right|\ll N^3(1+\log(2N))^6.
\]
The bound includes the final incomplete conductor interval. [squareGeneratorPrefix_capped_products](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/CappedConductorPrefixes.lean)

At conductor \(n\), the square-generator mesh and common prime window contribute \(O(n^2)\) to the logarithm. In the capped prime reading, the product cutoff costs \(O(1+\log n)\) since \((n\lfloor\sqrt n\rfloor)^2\le n^3\). The cofactor cutoff costs \(O(1+\log n)\) since its denominator is \(n+1\) and the spline horizon is \(O(n^2)\). The remaining contact error is \(O((1+\log(2n))^6)\) before multiplication by \(n^2\). The logarithm of the finite positive rational product is the sum of the logarithms. Summing the errors gives the stated transfer. [Joint cutoff](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheCompleteUpperProductTail.lean)
