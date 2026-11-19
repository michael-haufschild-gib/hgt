# Smooth population and the bias of a polynomial rough cutoff

- **Stage** 1-in-progress
- **Question** How far can the explicit rough support be thinned before it acquires a systematic sign bias?

Write \(A_y(X)=\sum_{n\le X,\ P^-(n)>y}\mu(n)\) and let \(\Psi(T,y)\) count positive integers through \(T\) with all prime factors at most \(y\). For any integer cutoffs with \(y\to\infty\) and \(X/y\to\infty\), the boundary law to formalize is
\[
 (\log X) A_y(X)=-y\Psi(X/y,y)+o(X).
\]
At polynomial cutoffs the rough prefix therefore has negative charge of order \(X/\log X\). The smooth integers in this identity sit at the *quotient* endpoint.

**Mechanism.** The logarithmic Möbius divisor identity, restricted to the remaining primes, gives
\[
 \sum_{n\le X}\mu_y(n)\log n
 =-\sum_{m\le X/y}\mu_y(m)\psi_y(X/m).
\]
Here \(\psi_y(t)\) sums the Mangoldt weights of powers of primes greater than \(y\). For \(t\ge y\) it lies between \(\theta(t)-\theta(y)\) and \(\psi(t)-\psi(y)\). The prime number theorem therefore prices replacement by \(t-y\) at \(O(t/\log^2t+y/\log^2 y)\). The increments of \(1/\log(X/m)\) dominate \(1/(2m\log^2(X/m))\), giving total error \(O(X/\log(y/2))\).

Divisor inversion gives \(\Psi(t,y)=\sum_{d\le t}\mu_y(d)\lfloor t/d\rfloor\). Replacing the floors by their real arguments and paying the lower wall costs at most \(2yR_y(X/y)\), where \(R_y\) counts rough integers. For each \(\delta>0\), counting coprime residues modulo a fixed primorial gives \(R_y(t)\le\delta t+K_\delta\) uniformly for large \(y\). Summing \(R_y(m)\log(1+1/m)\) shows that replacing \(\log n\) by \(\log X\) costs at most \(\delta X+K_\delta\log X\).

**Positive lower bound.** For each fixed integer \(j\ge2\), the fraction of \(y\)-smooth integers through \(T\le y^{j/2}\) stays bounded below. Below \(y\) all integers qualify. Above it multiply smooth integers through \(T/p\) by primes \(\sqrt y<p\le y\). Their reciprocal mass tends to \(\log 2\), and at most \(j\) distinct such primes divide an output. Induction gives the positive bound.

**Logarithmic threshold.** Summing \(\log n\) over the smooth integers through \(T\) costs at most \(T\sum_{p\le y}(\log p)/(p-1)\ll T\log(2y)\). On \(n>\sqrt T\) each log weight exceeds \((\log T)/2\). Hence the smooth proportion tends to zero if \(\log y=o(\log T)\). The positive lower bound gives the converse along subsequences. The predicted sharp criterion is \(A_y(X)=o(X/\log X)\) exactly when \(\log y=o(\log X)\), under the two growth conditions above.

**At the square-root scale.** Center each prime-power reading at the exact floor \(y\lfloor X/(ym)\rfloor\). Its sum against the surviving Möbius cofactors, plus the logarithmically weighted rough prefix, equals \(-y\Psi(X/y,y)\) exactly. For every \(s>0\), Rankin gives \(\Psi(T,y)\le T^s\prod_{p\le y}(1-p^{-s})^{-1}\). The entire smooth term therefore costs \(O_\varepsilon(X^{1/2+\varepsilon})\) uniformly for \(y\le\lfloor\log(X+1)\rfloor^2\).

**A single moving polynomial cutoff.** Fix \(0<\theta<1\) and put \(S_\theta=\{n\ge1:P^-(n)>n^\theta\}\), including the unit. Every divisor of a member also belongs to \(S_\theta\). If \(n\le X\) passes its own cutoff but fails the frozen cutoff \(X^\theta\), write \(n=pm\) with its least prime factor. Then \(p\le X^\theta\) and \(m<n^{1-\theta}\le X^{1-\theta}\). The discrepancy injects into the product of the primes through \(X^\theta\) and the members of \(S_\theta\) through \(X^{1-\theta}\).

For real \(t\) large, split \(S_\theta(t)\) at \(\sqrt t\). All later members avoid the primes through \(z=\lfloor t^{\min(\theta/2,1/8)}\rfloor\). Selberg's upper sieve gives their number at most \(2t/\log z+O(z^2\log^4 z)\), hence \(S_\theta(t)\ll_\theta t/\log t\). It includes every prime. The discrepancy product therefore has size \(O_\theta(X/\log^2 X)\), even before taking signs. In particular the frozen negative smooth main term and its order \(X/\log X\) survive on one fixed arithmetic set at every sufficiently large cutoff.

The weighted error in the boundary law is also \(O_\theta(X/\log X)\) at these polynomial cutoffs. The prime-reading bound is \(O(X/\log y)\). The rounding term costs \(yS_\theta(X/y)\). In the variation sum use \(R_y(t)\le S_\theta(t)\), split at \(\sqrt X\), and sum the increments of \(\log t\). Thus the signed ordinary prefix on \(S_\theta\) equals \(-y\Psi(\lfloor X/y\rfloor,y)/\log X+O_\theta(X/\log^2 X)\) with \(y=\lfloor X^\theta\rfloor\).

**Lean status.** Exact floor centering and the square-root estimate for the smooth term at the log-square cutoff are formalized. The uniform boundary law is formalized in [signed_rough_prefix_tracks_smooth_population](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSmoothPopulationInASignedRoughPrefix.lean). Both smooth population bounds, the subpolynomial threshold criterion, and the second-logarithm error on the fixed polynomially rough set have Lean sources awaiting verification.
