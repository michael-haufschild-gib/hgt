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

For a density-one matching with at most \(\sqrt t\) semiprime prescription errors through \(t\), the fixed lift divided by \(t\) differs from the semiprime reciprocal sum by at most \(4\), uniformly for \(1\le t\le y\). Summing the prefix errors over the divisors costs at most \(2t\) before normalization. Distinct-prime pairs with both primes through \(\sqrt t\) and through \(t\) bound the reciprocal sum from below and above. Thus the normalized fixed lift is \(\tfrac12(\log\log t)^2+O(1+\log\log t)\). [Semiprime harmonic mass and normalized lift](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSemiprimeHarmonicMassInASmoothLift.lean)

**Open.** The conjectured fixed and crossing fluxes over the whole prime window have respective leading terms \(\pm\tfrac12 X\log y(\log\log y)^2\). Their sum is the same prime interval for both prescriptions.
