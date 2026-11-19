# Square-root truncation of the rough cofactor

- **Stage** 1-in-progress
- **Target** Remove a specified part of the actual Möbius prefix at square-root-plus-epsilon cost, uniformly in the sharp cutoff.

At \(X\) put \(y=\lfloor\log(X+1)\rfloor^2\). For a squarefree integer \(n\le X\), write \(d=\gcd(n,P(y))\), \(r=n/d\). The smooth part and rough part are unique. For \(1/2<s<1\), the unsigned count with \(r\le Y\) is at most
\[
  X^s E_s(y)\sum_{1\le r\le Y}r^{-s}
  \ll_s X^s E_s(y)Y^{1-s}.
\]
Count the admissible smooth cofactors through \(\lfloor X/r\rfloor\) by Rankin's inequality. Forgetting the coprimality of \(r\) only increases this upper bound. Since \(E_s(y)=X^{o(1)}\), for every \(0\le\gamma\le1\) the count with \(r\le X^\gamma\) has exponent at most \((1+\gamma)/2\). In particular every subpower rough cofactor can be dropped at square-root-plus-epsilon cost. This gives the estimate on the indicated portion of the actual signed prefix unconditionally. The opposite portion carries the open remainder.

**Sharpness at every endpoint.** For \(0<\gamma<1\) put \(T=X^\gamma\) and \(H=\lfloor X^{1-\gamma}/4\rfloor\). At depth \(j=\lceil(\log H)/(2\log\log H)\rceil\) or \(j+1\), the prime box contains \(\gg \sqrt H\exp(cj)\) squarefree numbers of either prescribed sign. Every prime is at most \(H^{1/j}\le(\log H)^2\le y(X)\). Multiply independently by one prime in \((T/2,T]\). These primes exceed \(y(X)\) for large \(X\), so the products are distinct, have the chosen opposite sign, and have rough part exactly that prime. Their count is \(\gg_\gamma X^{(1+\gamma)/2}\exp(c_\gamma\log X/\log\log X)\). Thus both signs exceed every constant multiple of the endpoint power at every sufficiently large cutoff. For \(\gamma=0\) the same smooth boxes at \(H=\lfloor X/4\rfloor\) suffice. At \(\gamma=1\) the sector contains every squarefree integer.

At the quotient wall \(H=\lfloor X/y(X)\rfloor\) the same boxes fit under \(y(X)\). In particular the smooth main term \(y(X)\Psi(H,y(X))\) in the centered prime-power identity exceeds \(\sqrt X\) times every fixed power of \(\log X\) at every sufficiently large cutoff. Its power exponent is one half. The exact centered identity then forces at least one of its two signed readings to be negative beyond each square-root-logarithmic budget at every sufficiently large cutoff.
