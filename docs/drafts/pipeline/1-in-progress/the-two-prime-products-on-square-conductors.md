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
Its integral is zero. The proposed limit of $n^{-2}\log(U/V)$ is $-\int\{R_\tau(v)\}\,dv$. The proposed limit is open. Exponential decay of the ordinary generator and exponential growth of original sections hold at every prescribed positive multiplicity up to $c(n+1)^{1-w}$, where $w$ is the zeta zero width. [Prescribed multiplicities](../3-formalized/acs-prime-floor-loss-on-the-diagonal.md)

**Diagonal floor loss.** For every fixed $K\ge1$, the actual ordinary floors save at least $c_Kn^2$ at every $1\le m\le K(2n+1)$ for all sufficiently large $n$. At $m=n$ this gives $\log(U/V)/n^2\le P(D_n)-\delta$ with $\delta>0$. A uniform upper bound for the signed integrated prime contact $P(D_n)$ remains open. [Diagonal floor theorem](../3-formalized/acs-prime-floor-loss-on-the-diagonal.md)
