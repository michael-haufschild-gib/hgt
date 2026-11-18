# The long coprime product on square conductors

**ACS × PVC · In progress.** Write x=n², L=3·windowEnd((2n+1)²+1), and
w(k)=2[2A(log(k/x))−A(log(k/(4x)))]/√k. The target is a uniform one-sided subpower bound on the ordinary-prime sum with this common cutoff.

**Arithmetic reduction.** For each k use D=⌊1+log k⌋ and R(k)=remainingPrimeProducts(D,D,k), with the quotient, coprimality and both deletions in that definition. An adjacent-octave pair isolating p=2t+1 acts on every row f at pN as −f(N). In the all-width error estimate the unit cofactor (V,W)=(0,1) directly gives θ(k)−k=R(k)+O(√k(1+log k)⁶). The cofactor norm is one. Both statements are kernel-checked in [AdjacentLongProducts](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/AdjacentLongProducts.lean). The spline vanishes at L+1. Its density sum is O(1/n) by right-endpoint quadrature of its zero-mean profile. Partial summation therefore gives
$$
D_n=\sum_{k=1}^L (w(k)-w(k+1))R(k)+O((1+\log L)^6).
$$
Here L≪n² and the first mesh difference is O(n⁻³).

**Product range.** At q=pv, the discrete mean of the divisor test {k/(dq)}−½ is −1/(2dq). The full stencil annihilates the reciprocal divisor weight, including both parity corrections. On any interval of k its primitive consequently has size O((1+mass(R))R²q). Lean verifies the interval bound in [HorizonCancellation](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/HorizonCancellation.lean). For products q≤U with independent horizon endpoints per pair, summing the primitive costs O((1+mass(D+1))(1+mass(R))R²U²(1+log U)). The [aggregate interval estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ClippedProductMeans.lean) is kernel-checked. Partial summation against the first mesh difference costs O(n⁻³) because its successive difference is O(n⁻⁵). The resulting bound is logarithmic for fixed stencils through U=n⌊√n⌋. Here smoothing is in the prime-count horizon inside one conductor, with the original two dilations retained.

**Complement.** The interval bound before specializing U is proportional to U²/x^(3/2). For a target xˢ this identifies the product scale x^(3/4+s/2), up to logarithms. In particular a 1/3 target points to products beyond x^(11/12). To remove the entire lower range, the coprime-row theorem also permits fixed D=R=1. Its original lower cutoff is O(√k); restoring those products costs O(√k(1+log k)) by the reciprocal-prime bound. On this full row each pair starts at k=pv. The unresolved estimate concerns the signed upper tail, including small complementary factors.

**Two cutoffs.** At unit stencils a product q=pv is active precisely for q≤k<⌈q/2⌉². Cutting at q≤U costs O(U²(1+log U)/n³) in the spline. The existing large-complement estimate for v>M, applied with the same lower endpoint, costs O(n(1+log L)/(M+1)). The remaining range has p>U/M and outer quotient j≤L/(U+1). With U=n⌊√n⌋ and M=n both errors fit the logarithmic allowance. For a target x^(1/3), U near x^(11/12) and M near x^(1/6) leave primes above x^(3/4) and j of order at most x^(1/12), up to logarithms. The sharp cutoff and joint error are awaiting kernel verification.

**Open estimate.** Bound the full complementary reading by O(xˢ) for one 0<s<8999/24000. Bounds for every s>0 would close the route.

**Fixed-fibre test.** For a prime ℓ>4 the prime-multiple identity gives g₁(ℓ²)=−1. At n=ℓm the mesh satisfies wₙ(ℓ²j)=wₘ(j)/ℓ. Grouping horizon differences in blocks of ℓ² suggests that each fixed ℓ²-fibre separately carries −Dₘ/ℓ up to logarithmic error. The growing stencil deletes this fixed fibre once D≥ℓ².
