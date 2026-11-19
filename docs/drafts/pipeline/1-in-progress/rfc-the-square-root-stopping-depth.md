# The square-root stopping depth in least-prime expansion

- **Stage** 1-in-progress
- **Target** Identify the depth beyond which the actual squarefree terminal population in the sharp prefix already costs at most square root plus epsilon, without cancellation.

Fix \(0<\alpha<1\), put \(L=\log X\), and stop after \(k=\lceil\alpha L/\log L\rceil\) distinct prime factors. The number of squarefree integers of either sign through \(X\) reaching this depth is \(X^{1-\alpha+o(1)}\). For each sign its ratio to \(X^{1-\alpha}\) tends to infinity. Thus stopping at half this maximal order leaves an unsigned \(O_\varepsilon(X^{1/2+\varepsilon})\) terminal contribution at every endpoint. The remaining problem is the signed sum of the shallower exits. Stopping at any fixed smaller fraction leaves a terminal population of strictly larger exponent.

**Upper bound.** For \(z\ge1\), expand \(z^{\omega(n)}\) over squarefree divisors with weights \((z-1)^{\omega(d)}\). Each divisor appears at most \(X/d\) times. The sum through \(X\) is at most \(X\exp((z-1)\sum_{p\le X}1/p)\). Taking \(z=L^{1-\delta}\) makes the exponential factor \(X^{o(1)}\). Above the stopping depth, \(z^k\ge X^{\alpha(1-\delta)}\). Let \(\delta\downarrow0\).

**Both signs at the endpoint.** Take \(j=k\) or \(k+1\) of the required parity and \(Y=X^{1/j}\). All products of \(j\) distinct primes up to \(Y\) fit below \(X\). With \(P=\pi(Y)\) the prime number theorem gives \((P-j)L/(jY)\to1\), since \(\log Y=L/j\) and \(L/Y\to0\). The first half of the factors of \(j!\) are at most \(j/2\), so \(j!\le j^j2^{-\lfloor j/2\rfloor}\). For any fixed \(1<c<\sqrt2\), eventually \(\binom Pj\ge c^j(Y/L)^j\). Since \(j<\alpha L/\log L+2\), this exceeds \(c^j X^{1-\alpha}/L^2\). Half the positive gain in the exponent pays these logarithmic factors. The two exact layers each have at least \(X^{1-\alpha}\exp(cj)\) vertices at every large cutoff, all of their primes at most \(X^{1/j}\), for an absolute \(c>0\).

**Lean status.** The unsigned upper bound and the lower bounds for both adjacent exact layers have Lean sources awaiting verification.
