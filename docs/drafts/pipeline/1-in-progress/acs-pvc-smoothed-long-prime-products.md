# The long coprime product on square conductors

**ACS × PVC · In progress.** Write x=n², L=3·windowEnd((2n+1)²+1), and
w(k)=2[2A(log(k/x))−A(log(k/(4x)))]/√k. The target is a uniform one-sided subpower bound on the ordinary-prime sum with this common cutoff.

**Arithmetic reduction.** For each k use D=⌊1+log k⌋ and R(k)=remainingPrimeProducts(D,D,k), with the quotient, coprimality and both deletions in that definition. An adjacent-octave pair isolating p=2t+1 acts on every row f at pN as −f(N). In the all-width error estimate the unit cofactor (V,W)=(0,1) directly gives θ(k)−k=R(k)+O(√k(1+log k)⁶). Thus the cofactor norm costs one at this step. The spline vanishes at L+1. Its density sum is O(1/n) by right-endpoint quadrature of its zero-mean profile. Partial summation therefore gives
[
 D_n=sum_{k=1}^L (w(k)-w(k+1))R(k)+O((1+log L)^6).
]
Here L≪n² and the first mesh difference is O(n⁻³).

**Product range.** At q=pv, the discrete mean of the divisor test {k/(dq)}−½ is −1/(2dq). The full stencil annihilates the reciprocal divisor weight, including both parity corrections. On any interval of k its primitive consequently has size O((1+mass(R))R²q). Lean verifies the interval bound in [HorizonCancellation](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/HorizonCancellation.lean). For products q≤U with independent horizon endpoints per pair, summing the primitive costs O((1+mass(D+1))(1+mass(R))R²U²(1+log U)). Partial summation against the first mesh difference costs O(n⁻³) because its successive difference is O(n⁻⁵). The resulting bound is logarithmic for fixed stencils through U=n⌊√n⌋. Here smoothing is in the prime-count horizon inside one conductor, with the original two dilations retained.

**Open estimate.** Isolate a band in the actual logarithmic-stencil row with these endpoints and bound the complementary signed sum. A bound on the whole reading of order xˢ for one 0<s<8999/24000 would improve the strip. Bounds for every s>0 would close it.
