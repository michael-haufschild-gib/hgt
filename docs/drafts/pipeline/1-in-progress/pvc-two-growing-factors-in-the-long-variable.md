# Two growing factors in the long variable

**Route** PVC. **Stage** 1-in-progress.

Let $\alpha=10^{-5}$, $D=\lfloor X^{\alpha/8}\rfloor$, $R=\lfloor X^\alpha\rfloor$, $Y=\lfloor X^{1/2+\alpha}\rfloor$, $s_D(v)=\sum_{d\mid v,\,d\le D}\mu(d)$ and $M_D=\sum_{d\le D}\mu(d)/d$. Write the centered factorial weight as $w(j)=1+\sum_k c_k\lfloor j/k\rfloor$. Is the following uniform to $O(\sqrt X)$?
$$
\psi(X)-X =
M_D X\left(\frac12\sum_k\frac{c_k\log^2 k}{k}-\gamma\right)
-\sum_{\substack{Y<uv\le X/R\\u,v>D}}\Lambda(u)s_D(v)\,w(\lfloor X/(uv)\rfloor)
+O(\sqrt X).
$$
Only the short divisor coefficients enter the density term. Both variables of the signed convolution would exceed a fixed power cutoff at the divided horizon.

Apply [Vaughan's identity](../../../../formal/GaloisForLFunctions/RHTower/Sieve/VaughanIdentity.lean) with both inner cutoffs $D$. The short terms are $\mu_{\le D}*\log$ and $-\mu_{\le D}*\Lambda_{\le D}*1$. After subtracting their smooth log and constant densities, individual divisibility tests have interval discrepancy at most one; Abel summation up to $X$ costs a logarithm; truncate the discrepancy outside that horizon. The resulting $O(D^2(1+\log X)^2)$ discrepancy fits the [large-cell density bound](../3-formalized/pvc-sifting-the-large-complementary-prime-cells.md). The constant density is $O((1+\log D)^2)$, absorbable by the explicit unit-density error $O(X^{5\alpha}+X^{1/2-\alpha}(1+\log X))$. Also $|M_D|\le2$ follows from $\sum_{d\le D}\mu(d)\lfloor D/d\rfloor=1$. The long convolution has the displayed sign since $s_D(v)=0$ for $1<v\le D$. Passing from ordinary primes to the high Mangoldt row also requires the proper-power bound below $Y$.

It remains to evaluate the pair of $\log n$ with $w$. Reversing one floor produces the harmonic sums of $1/j$ and $(\log j)/j$. With $Z=Y+1$ the expected half-endpoint is $Z(\log Z-1)/2$. For $t=1/n$, $s=1/(n+1)$ and $r=\log(1+t)$, the unit trapezoid error for $(\log x)/x$ is $\log n\,[(t+s)/2-r]+r(s-r)/2$. From $t-t^2/2\le r\le(t+s)/2$ this is $O((1+\log n)/n^3)$. The fractional endpoint and its total stencil error remain to be checked.

The [corrected divisor coefficients](../3-formalized/pvc-balanced-products-in-the-large-quotient-cells.md) give a two-factor formula with zero smooth term at square-root precision. The displayed formula for the uncorrected Möbius coefficients still requires the logarithmic endpoint.
