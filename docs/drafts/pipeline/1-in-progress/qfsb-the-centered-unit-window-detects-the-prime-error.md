# The centered unit window detects the prime error

- **Stage** 1-in-progress
- **Question** Can the largest quotient indices of the floor-centered reading be priced separately at the target exponent?

Put \(y=\lfloor\log(X+1)\rfloor^2\) and \(K=\lfloor X/(y+1)\rfloor\). For \(K<q\le X\) the rough cofactor prefix equals one. Eventually \(K\ge y\). The ordinary prime reading on these indices, after subtracting the original floor increments, is exactly
\[
 U(X)=\vartheta(X)-\vartheta(K)-y(\lfloor X/y\rfloor-\lfloor K/y\rfloor)
     =E(X)-E(K)+(X\bmod y)-(K\bmod y),\qquad E(t)=\vartheta(t)-t .
\]
The remainder difference has size strictly less than \(y\). For each \(s>0\), \(U(X)=O(X^s)\) if and only if \(E(X)=O(X^s)\). Indeed \(y=o(X^s)\) and \(K\le X/2\) eventually. Strong induction recovers the prefix from its differences with geometric factor \((1-2^{-s})^{-1}\).

Changing any proper prime-power weights within \([-\Lambda(q),\Lambda(q)]\) changes the interval by at most \(\psi(X)-\vartheta(X)\) from the ordinary-prime reading. This costs \(O(\sqrt X)\) by the Chebyshev proper-power bound. Every such choice detects the same exponents at or above one half, even if the choices depend on the observation. In particular, separately estimating this single band at every half-plus exponent already requires the ordinary-prime error bound at those exponents. A proof by recombination can instead retain the lower sector with its sign.

**Critical endpoint.** Both signs of the centered unit band reach Littlewood size on sequences common to all proper-power choices. Write \(L(t)=\log\log\log t\). For either sign \(s\), take an arbitrarily large Littlewood witness \(x\) for \(sE(x)\), and maximize \(sE(m)/\sqrt m\) over the positive integers through \(\lfloor x\rfloor\). Flooring \(x\) costs less than one. These maximizing indices escape every finite set, and their normalized error is at least \(cL(x)\). At such an index,
\[
 s(E(m)-E(K(m)))\ge (1-2^{-1/2})\,sE(m).
\]
The floor residues cost \(o(\sqrt m)\) and all proper-power edits together cost \(O(\sqrt m)\). Since \(L(x)\ge L(m)\) at large arguments, the signed band exceeds \(c'\sqrt m L(m)\) simultaneously for every edit. In particular its exact square-root bound fails in both directions.
