# The critical Euler price of the log-square cutoff

- **Stage** 1-in-progress
- **Question** What replaces the unspecified epsilon loss in paying the smooth main term at exponent one half?

For \(E_s(y)=\prod_{p\le y}(1-p^{-s})^{-1}\), the critical price satisfies \(\log E_{1/2}(y)\asymp \sqrt y/\log y\). At \(y=\lfloor\log(X+1)\rfloor^2\) this has order \(\log X/\log\log X\).

**Leading coefficient.** Partial summation of the prime number theorem gives
\[
 \frac{\log y}{\sqrt y}\sum_{p\le y}\frac1{\sqrt p}\to2,\qquad
 \frac1{\sqrt y}\sum_{p\le y}\frac{\log p}{\sqrt p}\to2.
\]
For \(r=p^{-1/2}\), the difference \(-\log(1-r)-r\) lies in \([0,r^2/(1-r)]\). Its sum is \(O(1+\log y)\), by the harmonic upper bound and \(r\le1/\sqrt2\). Hence \(\log E_{1/2}(y)\sim2\sqrt y/\log y\).

**The actual population.** Rankin's bound at \(s=1/2\) prices \(y\Psi(X/y,y)\) by \(\sqrt X\exp(C\log X/\log\log X)\). The squarefree depth box at \(H=\lfloor X/y\rfloor\) has both signs and at least \(\sqrt H\exp(c\log H/\log\log H)\) members with all primes through \(y\). Hence the exponential factor has the correct order in the logarithm for the actual smooth population. The same upper estimate for rough part through \(X^\gamma\) multiplies \(X^{(1+\gamma)/2}\), and a smooth box times a single rough prime gives the matching lower scale for every fixed \(0<\gamma<1\).
