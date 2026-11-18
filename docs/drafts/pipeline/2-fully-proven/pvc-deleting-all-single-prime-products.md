# Deleting all single-prime products

**Route** PVC. **Stage** 2-fully-proven.

In the [balanced product](../3-formalized/pvc-balanced-products-in-the-large-quotient-cells.md), every $uv$ supported on a single prime can be deleted at total cost $O(\sqrt X)$. This includes the whole diagonal $u=v$, since $\Lambda(u)$ vanishes unless $u$ is a prime power.

**Prime squares.** For $p>2(D+1)$ prime, the only active divisor dividing $p$ is one, with coefficient one. Therefore $g_D(p)=-1$. In the factorization of $p^2$ only $(p,p)$ survives and $B_D(p^2)=-\log p$. This cancels the original proper-power coefficient exactly. For every $n$, $|B_D(n)|\le 2(1+\mathrm{mass}(D+1))\log n$ by the uniform bounds on the partial sums of $g_D$ and $\sum_{u\mid n}\Lambda(u)=\log n$.

**Higher powers.** Outside the prime squares and the primes, the total Mangoldt mass through $X$ is $\psi(X)-\theta(X)-\theta(\sqrt X)=O(X^{1/3})$. Indeed the elementary upper bound for $\psi-\theta$ is $\psi(\sqrt X)+\psi(X^{1/3})+\psi(X^{1/5})$. Also $\psi(\sqrt X)-\theta(\sqrt X)=O(X^{1/4})$. On a prime power $n$, $\Lambda(n)\ge\log 2$, so the matched coefficient $\mathbf1_{n\text{ prime power}} B_D(n)+\Lambda(n)\mathbf1_{n\text{ nonprime}}$ is bounded by $O((D+1)(1+\log X))\Lambda(n)$ for $n\le X$. It vanishes on primes and on all prime squares above $[2(D+1)]^2$.

**Paired error.** The small squares cost at most the full positive Mangoldt mass through $[2(D+1)]^2$, hence $O((D+1)^2)$. The outer weight is $O(R)$. Bounding each $D$, $R$, and $1+\log X$ by a constant times $X^{1/45}$ gives a total matched error $O(X^{2/5})$. The original proper powers already cost $O(\sqrt X)$ on these high cells. Subtract them and sum over cofactor horizons. Only products with at least two distinct prime divisors remain.
