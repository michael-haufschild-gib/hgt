# Deep endpoints and the information in a complete block

For a weight $f$ on the positive integers, put $S_{q,f}(X)=\sum_{m\le X} f(m)\,\mathbf1_{q\mid\lfloor X/m\rfloor+1}$. At $q>N+1$ the sampled endpoint $S_{q,f}(qN)$ vanishes for every $f$. Thus smallness there imposes no constraint on the primes.

At $q>M\ge1$ the interior cutoffs instead satisfy
$$S_{q,f}(qM-r)=\sum_{m\mid M,\,r\le m}f(m)\qquad(1\le r\le q).$$
Indeed a selected $m$ has $qM-r<qkm\le qM-r+m$. These inequalities give $km\ge M$. If $km\ge M+1$, then $(q-1)(M+1)\le(q-1)km\le qM-r$, contradicting $M\le q-1$. Hence $km=M$ and $r\le m$. The converse follows by substitution. The slot $r=M$ returns $f(M)$, and summing all slots gives $\sum_{m\mid M}mf(m)$. For $f=\Lambda$ the slot $r=1$ gives $\log M$. [Exact divisor and recovery laws](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/DeepQuotientBlocksRecoverWeightedPrimeDivisors.lean)

For arbitrary widths $w(N)>N$, let $T(N)$ sum all slots in blocks $1\le M\le N$ with that common width and $f=\Lambda-1$. At each $0<b<1$,
$$T(N)=O(N^{1+b})\quad\Longleftrightarrow\quad\psi(N)-N=O(N^b).$$
In fact $T$ sums the divisor convolution of $1$ with $g(m)=mf(m)$. At exponent $1+b$, convolving with either $1$ or its inverse $\mu$ costs at most $\sum_{d\ge1}d^{-1-b}$. Summation by parts carries a bound $O(N^b)$ for the prefix of $f$ to $O(N^{b+1})$ for the prefix of $g$. Inverting the weight uses $1/n-1/(n+1)\le1/n^2$ and $\sum_{n\le N}n^{b-1}\le N^b/b$. [Exponent equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CumulativeDeepQuotientBlocksHaveThePrimeErrorExponent.lean)

The Lean declarations are `quotientClassMassOf_deep_endpoint`, `quotientClassMassOf_recovers_weight`, `sum_quotientClassMassOf_deep_block` and `deepBlockPrimeExcess_power_iff`.
