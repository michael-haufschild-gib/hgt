# The inner weight on large prime multiples

**Route** PVC. **Stage** 2-fully-proven.

Fix $D\ge1$ and a prime $p>2(D+1)$. For the [inner coefficient](../3-formalized/pvc-balanced-products-in-the-large-quotient-cells.md), every $t\ge1$ satisfies
$$
g_D(pt)=g_D(t)-\mathbf1_{t=1}.
$$
In particular, for every $T\ge1$, the prefix on multiples of $p$ differs from the ordinary prefix through $T$ by exactly $-1$. Its absolute value is bounded by $2+\mathrm{mass}(D+1)$, uniformly in $p,T$. On every interval $1\le L\le U$ the shared-prime coefficient has exactly the original interval sum over $L<t\le U$.

Write $F_{D+1}(n)$ as a signed sum of $\lfloor n/d\rfloor$ with $1\le d\le2(D+1)$. Differencing each floor gives $\mathbf1_{d\mid n}$. Since each such $d$ is coprime to $p$, the increment of $F_{D+1}$ at $pt$ equals its increment at $t$. For $t>1$ both increments enter $g_D$ with sign $-1$. At $t=1$, the definition $G_D(0)=0$ adds one to $g_D(1)$, while $pt>1$ has no such term. Summing gives the prefix and interval formulas.
