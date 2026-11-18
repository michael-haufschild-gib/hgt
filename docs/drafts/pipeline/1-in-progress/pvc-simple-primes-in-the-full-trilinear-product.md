# Simple prime divisors of the full trilinear product

**Route** PVC. **Stage** 1-in-progress.

In the [coprime ordinary-prime row](../3-formalized/pvc-shared-prime-factors-in-the-balanced-product.md) $p,v,k$ with $(p,v)=1$, remove $p\mid k$ as well. This would make $p$ a prime of valuation exactly one in $pvk$. For each fixed Vaughan width the finitely many $p\le W$ also cost a bounded multiple of the square-root allowance, so $p$ could be simple in the complete product $dpvk$.

Let $J=128(128R^2+1)$, the endpoint of the [outer divisor stencil](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CenteringTheFactorialPrimeWeight.lean). For $p>J$, every stencil divisor is coprime to $p$. Its floor increment at $pt$ therefore equals its increment at $t$. Extending $w_R(0)$ by zero gives $h_R(pt)=h_R(t)-\mathbf1_{t=1}$ for $t\ge1$, where $h_R$ is the successive difference. The prefix of the removed outer coefficients at $j$ is $w_R(\lfloor j/p\rfloor)-1$ if $j\ge p$, and zero otherwise.

The prefix of $g_D(v)\mathbf1_{(v,p)=1}$ is bounded by $O(D+1)$, by subtracting the prefix on multiples of $p$. For fixed $p$ the removed row is consequently a quotient pairing at horizon $\lfloor X/p^2\rfloor$, with cost $O((D+1)R\sqrt X/p)$. Mertens bounds the prime sum by $O((D+1)R\sqrt X(1+\log X))$. Primes $p\le\max(J,2(D+1))$ can be removed as whole first factors using the fixed-factor estimate and Chebyshev. The remaining problem is cancellation among products carrying a simple prime.
