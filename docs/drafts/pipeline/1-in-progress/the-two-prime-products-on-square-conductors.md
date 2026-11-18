# The prime profile beyond the product-order bounds

For the reduced generator \(U/V\) of \(mD_n\), the numerator and denominator both have logarithmic order \(nm^2\) when \(m^2\ge Cn\). The remaining questions concern the leading coefficient, the sign change, and the transition at fixed \(m^2/n\). [Product-order theorem](../3-formalized/orders-of-the-reduced-square-prime-products.md)

**Sign of the continuous rows.** The autocorrelation is the convolution of eight unit boxes. Convolving a function that is nonnegative to the left of a cut and nonpositive to its right with one box preserves this order of signs. Once a moving interval has negative integral, shifting it right either puts it wholly beyond the cut or removes only nonnegative mass and adds only nonpositive mass. Starting with two translates of a single box with coefficients $2,-1$ therefore predicts a single change of sign across the long prime lags. The sign order on the discrete mesh requires a separate argument.

**Proposed common leading coefficient.** When $m/\sqrt n\to\infty$, divide both logarithms by $nm^2$. Their expected common limit is
\[
 2\int_0^\infty [2H(\log v)-H(\log(v/4))]_+\,\frac{dv}{\sqrt v}.
\]
The positive and negative parts have equal integral since dilating $v$ by four doubles $dv/\sqrt v$. The bounded-lag contacts contribute $O(m^2)$. Floor errors cost $O(n^2)$, uniformly in $m$. The unresolved comparison on the diagonal is $\log U-\log V\le O(n^2)$.

Replacing $(2n+1)^2$ by $4n^2$ costs $O(1)$ in the signed continuous prime sum. The dyadic profile at $n^2$ has an upper bound $O((n+1)^{2s})$ exactly when the zeta zero width is at most $s$, for $0\le s<1/2$. On the diagonal $|\log(U/V)|\ll n^{2+8999/12000}$. [Dyadic prime weight](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheDyadicPrimeWeightOfSquareConductors.lean)

**Endpoint on the degree mesh.** Write $b=(2n+1)^2$. For $n\ge3$ and $q>e^8 n^2$, the only possible contact is between the lowest and highest graphs. Their spline interiors meet at degrees $j$ satisfying $3er<j<3e^9rb/q$. The predicted last negative lag is therefore the strict cutoff $q<3e^9rb/(\lfloor3er\rfloor+1)$. The cutoff approaches $e^8b$ as $r$ grows. Within log distance $\eta$ of this endpoint there are only $O(r\eta+1)$ contributing degrees, each with harmonic weight at most $1/r$.

**Rounding at fixed scale.** For $m^2/n\to\tau>0$, the limiting unrounded row at $q=n^2v$ is
\[
 R_\tau(v)=2\tau\,[2H(\log v)-H(\log(v/4))]/\sqrt v.
\]
Its integral is zero. The proposed limit of $n^{-2}\log(U/V)$ is $-\int\{R_\tau(v)\}\,dv$. A strict negative upper bound only needs one interval where $-1/2<R_\tau<0$. Such intervals lie just inside the upper support endpoint. A fixed interval works simultaneously for $m^2/n$ in any compact positive range. Uniform mesh error and the prime number theorem would then give exponential decay of the generator for every prescribed constant multiple of $\sqrt n$, even where the numerator itself grows exponentially.

**At diagonal multiplicity.** Can the actual floors save $c n^2$ when $m=n$? On the outer band the normalized mesh profile can be interpolated in the real lag $x=k/(2n+1)^2$. Only the lowest and highest graphs meet. The lower degree index runs through a fixed multiple of the resolution, giving a uniform Lipschitz bound. A fractional-level interval then has length of order $n$ in the prime variable. Subdivide these disjoint intervals into boxes of length $2B^{1/3}$, $B=(2n+1)^2$. If a box has small Mangoldt mass, every start in its first half belongs to the short-interval deficit set. Its total measure is $o(B)$, whereas the level intervals have total length of order $B$. The remaining signed comparison concerns the integrated prime contact. [Almost-all short intervals](../../../../formal/GaloisForLFunctions/RHTower/PrimeAlmostAllShortIntervals.lean)
