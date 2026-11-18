# Coincident products of ordinary prime weights

**Stage** 3-formalized. **Type** Theorem (Lean).

For $a\ge2$, $b\ge0$, $X\ge1$ and $p$ the least prime factor of $a$,
$$\sum_{2\le k\le X}\Lambda(ak)\Lambda(bk)=
\begin{cases}
(\log p)^2\lfloor\log_p X\rfloor,&a,b\in\{p^j:j\ge0\},\\
0,&\text{otherwise}.
\end{cases}$$
In particular this sum is at most $\log a\log X$. The bound also holds in absolute value on any subset of rows with any complex weights of modulus at most one.

**Proof.** If both factors are nonzero, $ak$ and $bk$ are prime powers. The factor $k>1$ forces the same prime base, and $a\ge2$ identifies this base as $p$. Conversely each admissible $k=p^j$, $j>0$, contributes $(\log p)^2$. These $k$ are exactly the nonunit divisors of $p^{\lfloor\log_p X\rfloor}$.

For distinct positive cofactors $d,e$, write $L=\operatorname{lcm}(d,e)$. The shared products through $N\ge L$ are $Lk$ with $k\le N/L$. Removing $k=1$ leaves the preceding correlation with dilations $L/d,L/e$, at least one of which exceeds one. This gives an independent logarithmic bound for coincident products of the two actual von Mangoldt weights. [Exact correlation and shared-product bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CoincidentProductsOfOrdinaryPrimeWeights.lean)
