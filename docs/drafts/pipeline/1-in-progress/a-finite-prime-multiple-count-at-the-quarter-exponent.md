# A finite prime-multiple count at the quarter exponent

For $X>0$ put $T(y)=\sum_{1\le m\le y}(1-m/y)$ and
$$A(X)=\sum_{pm\le X}(\log p)(1-pm/X)-\sum_{n\le X}(\log n)(1-n/X)
       +\sum_{r=2,3}\sum_{k^r m\le X}(1-k^r m/X).$$
Here $p$ is prime and $k,m,n$ are positive integers. The proposed arithmetic criterion is $|A(N)-2A(N/2)|=O_b(N^b)$ at every integer cutoff for every $1/4<b<1/2$. All three terms use finite sums. There is no fitted density.

Let $w(d)=\Lambda(d)\mathbf 1_{d\text{ nonprime}}$, $u(d)=w(d)-\#\{(k,r):r\in\{2,3\},\ k^r=d\}$. Then $A(X)=-\sum_d u(d)T(X/d)$. Write $H(y)=T(y)-2T(y/2)$. On $2j\le y\le2j+1$, $H(y)=j/y$; on $2j+1\le y\le2j+2$, $H(y)=1-(j+1)/y$. In particular $H$ is continuous, zero through one, and $|yH'(y)|\le1$ on every open cell. Under RH the square and cube prime weights have cumulative mass $x^{1/2}+x^{1/3}+O_b(x^b)$, and all higher powers together cost $O(x^{1/4}\log x)$. Thus $\sum_{d\le x}u(d)=O_b(x^b)$. Partial summation against $H(N/d)$ gives the claimed bound since $|H(N/d)-H(N/(d+1))|\le1/d$.

For the converse the Mellin symbol before the triangular mean is
$$-(1-2^{1-s})\zeta(s)\left(\sum_d w(d)d^{-s}-\zeta(2s)-\zeta(3s)\right).$$
If $a(n)$ are its coefficients, then $X[A(X)-2A(X/2)]=\sum_{n\le X}(X-n)a(n)$ is linear on each unit interval. Integer bounds therefore imply the same real bounds. Mellin integration gives a holomorphic continuation of the symbol divided by $s(s+1)$ to $\Re s>1/4$. The explicit lattice terms have only real poles in this region. The dyadic factor has no zeros in $1/4<\Re s<1/2$. At half a right zero the remaining residue is proportional to $\zeta(s)(\operatorname{ord}_{2s}\zeta/2+\operatorname{ord}_{3s}\zeta/3)$. Vanishing of all such residues would force $\zeta(\rho/2)=0$ for every right zero, which the reflection-and-halving theorem excludes. [Prime-power continuation and residues](prime-divisor-logarithmic-moments-at-a-finite-top.md)

Can the difference of the ordinary-prime and unrestricted lattice counts satisfy a bound strictly below $N^{\Re\rho/2}$ on the single-quartet stratum?
