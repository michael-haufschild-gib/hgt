# The critical Euler price of the log-square cutoff

- **Stage** 1-in-progress
- **Question** What replaces the unspecified epsilon loss in paying the smooth main term at exponent one half?

For \(E_s(y)=\prod_{p\le y}(1-p^{-s})^{-1}\), the critical price satisfies \(\log E_{1/2}(y)\asymp \sqrt y/\log y\). At \(y=\lfloor\log(X+1)\rfloor^2\) this has order \(\log X/\log\log X\).

**Upper estimate.** Write \(A(n)=\sum_{p\le n}\log p/\sqrt p\) and \(T(n)=\vartheta(n)\le Cn\). Then \(A(n)\le C\sqrt n+T(n)/\sqrt n\). At a prime successor the new terms on both sides agree. The old terms cost \(T(n)(1/\sqrt n-1/\sqrt{n+1})\le C(\sqrt{n+1}-\sqrt n)\). Thus \(A(y)\le2C\sqrt y\). Up to \(y^{1/4}\) the unweighted reciprocal-root sum costs at most \(y^{1/4}\). On the rest divide the previous estimate by \((\log y)/4\). Since \(-\log(1-r)\le r/(1-r)\) and \(r\le1/\sqrt2\), summing proves the Euler bound. Primes in \((y/2,y]\) give the matching lower order.

**The actual population.** Rankin's bound at \(s=1/2\) prices \(y\Psi(X/y,y)\) by \(\sqrt X\exp(C\log X/\log\log X)\). The squarefree depth box at \(H=\lfloor X/y\rfloor\) has both signs and at least \(\sqrt H\exp(c\log H/\log\log H)\) members with all primes through \(y\). Hence the exponential factor has the correct order in the logarithm for the actual smooth population. The same upper estimate for rough part through \(X^\gamma\) multiplies \(X^{(1+\gamma)/2}\), and a smooth box times a single rough prime gives the matching lower scale for every fixed \(0<\gamma<1\).
