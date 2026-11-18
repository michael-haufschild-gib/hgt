# The long coprime product on square conductors

**ACS × PVC · In progress.** Write x=n², L=3·windowEnd((2n+1)²+1), and
w(k)=2[2A(log(k/x))−A(log(k/(4x)))]/√k. The target is a uniform one-sided subpower bound on the ordinary-prime sum with this common cutoff.

**Arithmetic reduction.** For each k use D=⌊1+log k⌋ and R(k)=remainingPrimeProducts(D,D,k), with the quotient, coprimality and both deletions in that definition. An adjacent-octave pair isolating p=2t+1 acts on every row f at pN as −f(N). In the all-width error estimate the unit cofactor (V,W)=(0,1) directly gives θ(k)−k=R(k)+O(√k(1+log k)⁶). Thus the cofactor norm costs one at this step. The spline vanishes at L+1. Its density sum is O(1/n) by right-endpoint quadrature of its zero-mean profile. Partial summation therefore gives
[
 D_n=sum_{k=1}^L (w(k)-w(k+1))R(k)+O((1+log L)^6).
]
Here L≪n² and the first mesh difference is O(n⁻³).

**Product range.** At q=pv, the discrete mean of the divisor test {k/(dq)}−½ is −1/(2dq). The full stencil annihilates the reciprocal divisor weight, including both parity corrections. On any interval of k its primitive consequently has size O((1+mass(R))R²q). Lean verifies the interval bound in [HorizonCancellation](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/HorizonCancellation.lean). For products q≤U with independent horizon endpoints per pair, summing the primitive costs O((1+mass(D+1))(1+mass(R))R²U²(1+log U)). The [aggregate interval estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ClippedProductMeans.lean) is kernel-checked. Partial summation against the first mesh difference costs O(n⁻³) because its successive difference is O(n⁻⁵). The resulting bound is logarithmic for fixed stencils through U=n⌊√n⌋. Here smoothing is in the prime-count horizon inside one conductor, with the original two dilations retained.

**Complement.** The interval bound before specializing U is proportional to U²/x^(3/2). For a target xˢ this identifies the product scale x^(3/4+s/2), up to logarithms. In particular a 1/3 target points to products beyond x^(11/12). To remove the entire lower range, the coprime-row theorem also permits fixed D=R=1. Its original lower cutoff is O(√k); restoring those products costs O(√k(1+log k)) by the reciprocal-prime bound. On this full row each pair starts at k=pv. The unresolved estimate concerns the signed upper tail, including small complementary factors.

**Next cancellation test.** On the fixed-stencil upper tail pv>U, expand the outer quotient weight into jumps at jpv and sum the spline differences in k first. This leaves j≤L/U and the sampled spline at jpv. For each p,j, partial summation in v against the bounded coprime prefix of the inner jumps suggests a cost O(1/n), uniform in p,j. The resulting first-prime range p≤P would cost O(nP/U). This would reach P=x^(1/4) at square-root precision and P=x^(3/4) at the 1/3 target, up to logarithms. The larger first primes still require an estimate.

**Open estimate.** Bound the full complementary reading by O(xˢ) for one 0<s<8999/24000. Bounds for every s>0 would close the route.
