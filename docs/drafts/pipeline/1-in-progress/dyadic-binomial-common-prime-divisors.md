# Common prime divisors of dyadic central binomial coefficients

For $q=2^j$, $j\ge1$, put
$$C_j(N)=\gcd_{1\le l\le j}\binom{2^lN}{2^{l-1}N},\qquad X=qN.$$
Can the size of this integer be controlled independently of the explicit formula for primes? An estimate of square-root size after subtracting the main term, for arbitrarily large fixed $j$, would detect every right zero.

[Fixed-depth obstruction and uniform excess](../3-formalized/dyadic-binomial-gcds-detect-every-right-zero.md) · [Sharp costs for signed binomial families](../5-failed/reflected-prime-residues-of-binomial-covers.md) · [Shortest binomial cover and its linear excess](../5-failed/a-single-binomial-cover-of-the-last-quotient-class.md)

## An arithmetic comparison at the first intersection

For $q=4$, the alternating harmonic and Gregory series give $4c_4=3\log2-\pi/2$. The positive rational product
$$R_N=\prod_{k=1}^N\frac{(N+k)^2}{N^2+k^2}$$
has $\log R_N=N(3\log2-\pi/2)+O(1)$ by a Riemann sum for $2\log(1+u)-\log(1+u^2)$ on $[0,1]$. The denominator is a product of Gaussian norms. Can an arithmetic comparison bound $|\log C_2(N)-\log R_N|$ to square-root order? Equality of the leading constants alone gives no such estimate. At a zeta zero the $q=4$ symbol is $-L(s,\chi_4)/2$, since $D_4=(\tfrac12-2^{-s-1}-4^{-s})\zeta-L(s,\chi_4)/2$.

The reduced numerator of the rational product $\prod_{k\le N}(4k-1)/(4k-3)$ gives a second arithmetic comparison. Its large prime factors are exactly the inert primes in the two middle quotient classes. [Quarter-shifted factorial ratio](height-of-the-quarter-shifted-factorial-ratio.md)

## Averaging the gcds

RH is equivalent to cumulative error $O(N^{1+b})$ about some linear slope at arbitrarily large fixed depths for every $1/2<b<1$. [First-mean theorem and proof](../3-formalized/the-first-means-of-dyadic-binomial-gcds.md)

Complete blocks with $q>N$ recover the ordinary prime-error exponent exactly. [Endpoint obstruction and full-block equivalence](../5-failed/deep-quotient-endpoints-and-the-prime-error.md)

Write $A_q(u)=\mathbf1_{q\mid\lfloor u\rfloor+1}$ and $F_q(y)=y^{-1}\int_0^y A_q(u)\,du$. Then $0\le F_q\le1$ and $|yF_q'(y)|=|A_q(y)-F_q(y)|\le1$ between integers. The first mean of the selected prime count through $X$ is $\sum_m\Lambda(m)F_q(X/m)$. Its difference from the integer-density mean is at most $\sum_{m<X}|\psi(m)-m|/m$ by partial summation. The integer-density mean differs by $O(1+\log X)$ from $X\int_1^\infty F_q(u)\,du/u^2=c_qX/2$, by the logarithmic derivative bound. Sampling at integer base cutoffs costs only $O(1+\log M)$ in the mean through $M$, uniformly in $q$. For each $m$, the selected bases occupy the last $m/q$ units of every period of length $m$. Subtracting the count of selected integers in $[0,M)$ from the selected real length in $[0,M]$ gives exactly $\{m/q\}\lfloor M/m+1/q\rfloor$. Only $m\le2M$ occur. Its Mangoldt-weighted sum divided by $M$ is $O(1+\log M)$ by $\psi(2M)\ll M$ and partial summation.

Under a single quartet of multiplicity $h$, the conjugate-pair term in the first mean is
$$-2h\Re\!\left(\frac{D_q(\rho)X^\rho}{\rho(1+\rho)}\right).$$
Indeed $\int_0^X t^{\rho-1}F_q(X/t)\,dt=X^\rho D_q(\rho)/(\rho(1+\rho))$ by two integrations. The square-root remainder in the ordinary prime wave contributes $O(\sqrt X\log^2 X)$ by the same derivative bound. Thus the averaged log gcd should recover the quartet with that error at each fixed $q$. The independent arithmetic estimate needed here is for the first mean of log gcds.
