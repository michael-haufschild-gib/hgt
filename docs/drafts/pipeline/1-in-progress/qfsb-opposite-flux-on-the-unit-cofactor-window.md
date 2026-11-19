# Opposite flux on the unit cofactor window

- **Stage** 1-in-progress
- **Question** What do the fixed and crossing terms of one actual exchange table contribute to the same growing prime reading?

Set \(K=\lfloor X/(y+1)\rfloor\), assume \(K\ge y\), and read ordinary primes in \((K,X]\) with weight \(\log q\). Their quotient floors \(t=\lfloor X/q\rfloor\) satisfy \(1\le t\le y\). Thus the rough Möbius prefix is exactly one, and the recombined signal is \(\vartheta(X)-\vartheta(K)\).

Take a density-one perfect completion of the squarefree nonunits. Its fixed signed prefix equals one at every positive argument. All integers through \(t\) are \(y\)-smooth, so the smooth lift of its fixed prefix is exactly \(t\); its crossing prefix lifts to \(1-t\). The interval therefore reads opposite contributions
\[
 D=\sum_{K<q\le X\atop q\text{ prime}}(\log q)\lfloor X/q\rfloor,\qquad
 C=\vartheta(X)-\vartheta(K)-D.
\]
Mertens' first theorem and the Chebyshev upper bound give \(D=X\log(y+1)+O(X)\) and \(C=-X\log(y+1)+O(X)\) uniformly for \(K\ge y\ge2\). The sharp prime signal has size asymptotic to \(X\) when \(y,K\to\infty\). Lean gives the two bounds with the exact logarithmic length \(\log X-\log K\). Since \(K(y+1)\le X<(K+1)(y+1)\) and \(K\ge1\), this length differs from \(\log(y+1)\) by at most \(\log 2\). [Perfect matching and exact prime interval](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/OppositeFluxOnTheUnitCofactorWindow.lean)

For a semiprime prescription with at most \(\sqrt t\) support errors through \(t\), the signed errors in its harmonic divisor sum are uniformly bounded, by partial summation. Through \(t\le y\), the fixed lift divided by \(t\) equals \(\tfrac12(\log\log t)^2+O(1+\log\log t)\). Indeed the semiprime reciprocal sum is squeezed between the distinct-prime pair sums with both primes through \(\sqrt t\) and through \(t\); the floors cost at most the semiprime population divided by \(t\). Hence the fixed and crossing prime-window fluxes should have respective leading terms \(\pm\tfrac12 X\log y(\log\log y)^2\). Their sum is the same prime interval at both prescriptions. This identifies the semiprime support directly in the quotient reading.
