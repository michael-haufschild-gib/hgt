# The centered unit window detects the prime error

- **Stage** 1-in-progress
- **Question** Can the largest quotient indices of the floor-centered reading be priced separately at the target exponent?

Put \(y=\lfloor\log(X+1)\rfloor^2\) and \(K=\lfloor X/(y+1)\rfloor\). For \(K<q\le X\) the rough cofactor prefix equals one. Eventually \(K\ge y\). The ordinary prime reading on these indices, after subtracting the original floor increments, is exactly
\[
 U(X)=\vartheta(X)-\vartheta(K)-y(\lfloor X/y\rfloor-\lfloor K/y\rfloor)
     =E(X)-E(K)+(X\bmod y)-(K\bmod y),\qquad E(t)=\vartheta(t)-t .
\]
The remainder difference has size strictly less than \(y\). For each \(s>0\), \(U(X)=O(X^s)\) if and only if \(E(X)=O(X^s)\). Indeed \(y=o(X^s)\) and \(K\le X/2\) eventually. Strong induction recovers the prefix from its differences with geometric factor \((1-2^{-s})^{-1}\).

Changing any proper prime-power weights within \([-\Lambda(q),\Lambda(q)]\) changes the interval by at most \(\psi(X)-\vartheta(X)\) from the ordinary-prime reading. Thus every such choice detects the same exponents above one half, even if the choices depend on the observation. In particular, separately estimating this single band at every half-plus exponent already requires the ordinary-prime error bound at those exponents. A proof by recombination can instead retain the lower sector with its sign.
