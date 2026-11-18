# Both ordinary-prime signs in the same fixed-width interval

Let $P$ be the ordinary-prime polar error of the threshold state. Can one find $c,H>0$ and arbitrarily large integers $j$ such that **both** sign masses on $[j-H,j+H]$ exceed $e^{cj}$?

Put $A_n=\int_n^{n+1}|P|$. A visible pole of the prime-head transform forces $A_n\ge e^{dn}$ arbitrarily late for some $d>0$: a bound $A_n\ll_\varepsilon e^{\varepsilon n}$ for every $\varepsilon>0$ would make the absolute Laplace integral holomorphic throughout $\Re p<0$. The [damped square bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/ExponentiallyIntegrableChangeOfPrimeVariance.lean) and the zero-free strip give $A_n=O(e^{b_0n})$ for some $b_0<1/2$.

Choose $\max(d,b_0)<b<1/2$. For each large cell $n$ with $A_n\ge e^{dn}$ maximize $A_k e^{-b|k-n|}$ over $k\ge0$. The maximum is attained since this sequence tends to zero. Its index $j$ satisfies $A_j\ge e^{dj}$ and $A_k\le A_j e^{b|k-j|}$ for every $k$. Such $j$ are unbounded.

For $K(v)=e^{-v/2}\{e^v\}$ the [signed response](../2-fully-proven/ecs-signed-ordinary-prime-fractional-response.md) stays bounded. On $(j,j+1]$ the weight $K(j-t)$ is at least $e^{-1/2}$. Each weighted sign mass on the full line is therefore at least $(e^{-1/2}A_j-O(1))/2$. The contribution from positive cells with $|k-j|\ge H$ is at most $2e^{1/2}A_j\sum_{m\ge H}e^{-(1/2-b)m}$, and $t<0$ costs $O(e^{-j/2})$ by confinement. Choose one $H$ so the geometric tail costs less than $e^{-1/2}A_j/8$. Since $K\le1$, both ordinary sign masses on the resulting fixed-width interval exceed $e^{cj}$ for any fixed $0<c<d$ and all large selected $j$.

The arithmetic upper bound for one sign on these intervals remains open. The analytic step to formalize is the passage from the visible prime-head pole to large unit-cell mass, followed by the positive-kernel estimate at the selected centers.
