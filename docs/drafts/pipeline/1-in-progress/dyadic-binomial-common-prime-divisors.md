# Common prime divisors of dyadic central binomial coefficients

For $q=2^j$, $j\ge1$, put
$$C_j(N)=\gcd_{1\le l\le j}\binom{2^lN}{2^{l-1}N},\qquad X=qN.$$
Can the size of this integer be controlled independently of the explicit formula for primes? An estimate of square-root size after subtracting the main term, for arbitrarily large fixed $j$, would detect every right zero.

[Fixed-depth obstruction and uniform excess](../3-formalized/dyadic-binomial-gcds-detect-every-right-zero.md) · [Shortest binomial cover and its linear excess](../5-failed/a-single-binomial-cover-of-the-last-quotient-class.md)

## An arithmetic comparison at the first intersection

For $q=4$, the alternating harmonic and Gregory series give $4c_4=3\log2-\pi/2$. The positive rational product
$$R_N=\prod_{k=1}^N\frac{(N+k)^2}{N^2+k^2}$$
has $\log R_N=N(3\log2-\pi/2)+O(1)$ by a Riemann sum for $2\log(1+u)-\log(1+u^2)$ on $[0,1]$. The denominator is a product of Gaussian norms. Can an arithmetic comparison bound $|\log C_2(N)-\log R_N|$ to square-root order? Equality of the leading constants alone gives no such estimate. At a zeta zero the $q=4$ symbol is $-L(s,\chi_4)/2$, since $D_4=(\tfrac12-2^{-s-1}-4^{-s})\zeta-L(s,\chi_4)/2$.

## Averaging the gcds

At every base $M\ge1$ and every $q\ge M+1$, the entire last block is explicit:
$$S_q(qM-r)=\sum_{m\mid M,\ m\ge r}\Lambda(m)\quad(1\le r\le q),\qquad
\sum_{r=1}^q S_q(qM-r)=\sum_{m\mid M}m\Lambda(m).$$
Indeed, a selected $m$ has $qM-r<qkm\le qM-r+m$. Thus $km\ge M$. If $km\ge M+1$, then $(q-1)(M+1)\le(q-1)km\le qM-r$, contradicting $q-1\ge M$. Hence $km=M$ and $r\le m$; the converse follows from the same interval. The block contains the weighted prime divisors of $M$ even where its sampled left endpoint vanishes. Summing complete blocks through $M$ gives $\sum_{m\le M}m\Lambda(m)\lfloor M/m\rfloor$. The divisor convolution multiplies its Dirichlet series by $\zeta(s)$ at the shifted argument $s=1+\rho$, where this factor is nonzero.

Write $A_q(u)=\mathbf1_{q\mid\lfloor u\rfloor+1}$ and $F_q(y)=y^{-1}\int_0^y A_q(u)\,du$. Then $0\le F_q\le1$ and $|yF_q'(y)|=|A_q(y)-F_q(y)|\le1$ between integers. The first mean of the selected prime count through $X$ is $\sum_m\Lambda(m)F_q(X/m)$. Its difference from the integer-density mean is at most $\sum_{m<X}|\psi(m)-m|/m$ by partial summation. The integer-density mean differs by $O(1+\log X)$ from $X\int_1^\infty F_q(u)\,du/u^2=c_qX/2$, by the logarithmic derivative bound. Sampling at integer base cutoffs costs only $O(1+\log M)$ in the mean through $M$, uniformly in $q$. For each $m$, the selected bases occupy the last $m/q$ units of every period of length $m$. Subtracting the count of selected integers in $[0,M)$ from the selected real length in $[0,M]$ gives exactly $\{m/q\}\lfloor M/m+1/q\rfloor$. Only $m\le2M$ occur. Its Mangoldt-weighted sum divided by $M$ is $O(1+\log M)$ by $\psi(2M)\ll M$ and partial summation.

Under a single quartet of multiplicity $h$, the conjugate-pair term in the first mean is
$$-2h\Re\!\left(\frac{D_q(\rho)X^\rho}{\rho(1+\rho)}\right).$$
Indeed $\int_0^X t^{\rho-1}F_q(X/t)\,dt=X^\rho D_q(\rho)/(\rho(1+\rho))$ by two integrations. The square-root remainder in the ordinary prime wave contributes $O(\sqrt X\log^2 X)$ by the same derivative bound. Thus the averaged log gcd should recover the quartet with that error at each fixed $q$, while RH gives $O_{q,b}(X^b)$ error for every $b>1/2$. Conversely, a power bound for these means extends their Mellin transforms across every point to its right. The multiplier $1/(s(s+1))$ preserves every detected right zero. The independent arithmetic estimate needed here is for the first mean of log gcds.
