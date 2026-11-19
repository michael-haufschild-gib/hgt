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

**Moving cutoff.** On a dyadic interval the additional eligible least primes between the two endpoint cutoffs lie in a fixed-ratio prime interval of reciprocal mass \(O(1/\log X)\). Their remaining cofactors have density tending to zero. Extending the signed main term to the single set defined by \(P^-(n)>n^\theta\) requires the corresponding lower bound for smooth integers in dyadic intervals and summation over the intervals.

**Lean status.** The uniform boundary law, both smooth population bounds and the subpolynomial threshold criterion have Lean sources awaiting verification. The moving-cutoff extension remains on paper.
