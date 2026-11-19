# Opposite prime triples at the cube root of the midpoint

At the sharp first strip milestone there are two prime-triple populations with exactly the same price per ordered tuple and opposite interval signs. The other surviving integers are smooth products of at least four prime factors, counting multiplicities. No smoothing of the endpoints is needed.

Let \(s(k)=\mathbf1_{(3n,4n]}(k)-\mathbf1_{(2n,3n]}(k)\), \(Y=\lfloor(3n)^{1/3}\rfloor\), \(D=\lfloor4n/(Y+1)\rfloor\). Take \(Y\ge3\). Let \(R(k)\) indicate that every prime divisor exceeds \(Y\), \(\Lambda_Y=R\Lambda\), and \(\mu_Y(d)=\mu(d)\mathbf1_{P^+(d)\le Y}\), with \(P^+(1)=1\). Then \(R=\mu_Y*1\), and \(\Lambda_Y*R=R\log\) by summing over divisors. Here \(*\) is Dirichlet convolution, \(1\) is the constant function, and \(e\) is the convolution unit. Applying the derivation \(\ell f(k)=f(k)\log k\) gives the exact identity
\[
 \Lambda_Y=2\ell R-\tfrac12\ell(R*R)+\Lambda_Y*(R-e)*(R-e).
\]
Indeed \(\ell(R*R)=2\Lambda_Y*R*R\) and the three convolution terms telescope.

The last convolution is supported above \(3n\) because \((Y+1)^3>3n\). Through \(4n\), its three factors must all be ordinary primes above \(Y\): four prime factors of that size already exceed \(4n\). Its weight at \(k\) is \(\log k/3\) times the number of ordered rough prime triples of product \(k\), by symmetry. Each priced prime lies below \(4n/(Y+1)^2\).

Expand the two complete terms using \(R=\mu_Y*1\) and \(R*R=(\mu_Y*\mu_Y)*\tau\). On \(d>D\), the complementary factor \(r=k/d\) is at most \(Y\), so the entire product is \(Y\)-smooth. Its signed coefficient before the logarithm is
\[
 a_n(k)=\sum_{d\mid k,\ d>D}\big[2\mu(d)-\tfrac12(\mu*\mu)(d)\tau(k/d)\big].
\]
In the two intervals a smooth product has at least three prime factors. Exactly three imply \(k\le Y^3\le3n\), and each factor is greater than \(2n/Y^2\). Since \(D\ge Y^2\), the sole contributing divisor is \(d=k\). For three distinct primes the coefficient is 2, for \(p^2q\) it is 1, and for \(p^3\) it is zero. Thus the smooth triples on the left also have price \(\log k/3\) per ordered tuple, omitting their pure cubes.

For \(d\le D\) use the ordinary summatory divisor theorem. The \(1\) and \(\tau\) rows have respective densities \(1\) and \(\log r+2\gamma\). Partial summation on the two sharp intervals, including the shared endpoint, costs \(O(\sqrt{n/d}\log(4n))\) per row. Finite Euler factors give \(|(\mu*\mu)(d)|\le\tau(d)\), so the total cost is \(O_\epsilon(n^{5/6+\epsilon})\) since \(D\ll n^{2/3}\). With \(c_i=\int_3^4\log^i u\,du-\int_2^3\log^i u\,du\), \(c_1=10\log 2-6\log3\), the resulting center is
\[
 A_n=n\!\sum_{\substack{d\le D\\P^+(d)\le Y}}
 \frac{2c_1\mu(d)-\tfrac12(\mu*\mu)(d)
 [c_2+c_1(2\log n+2\gamma-\log d)]}{d}.
\]
This follows by substituting \(k=dr\) into the two density integrals against \(s(k)\log k\). [Summatory divisor error](../../../../formal/GaloisForLFunctions/RHTower/DirichletDivisorAsymptotic.lean#L24)

Write \(T_-\) for the unsigned smooth-triple price on the left, excluding pure cubes, and \(T_+\) for the unsigned rough-triple price on the right. Removing proper prime powers from \(\Lambda_Y\) costs \(O(\sqrt n)\). The identity at every large integer is
\[
 D(n)=T_- - T_+ - A_n
 - \sum_{\substack{2n<k\le4n,\ P^+(k)\le Y\\\Omega(k)\ge4}}
      s(k)a_n(k)\log k
 +O_\epsilon(n^{5/6+\epsilon}).
\]
At sufficiently large prime centers all surviving products are coprime to \(n\), since even the rough triple factors are smaller than \(n\). These centers suffice at the first gate. There is a prime within \(O(n^{2/3})\) above every large \(n\); moving the three sharp endpoints changes \(D\) by \(O(n^{2/3}\log n)\). Thus the one-sided upper bound on this combined price at primes implies the full all-integer \(11/3\) prefix criterion. The comparably priced triple boxes and the smooth products of higher multiplicity must still be bounded together. Paper proof. [Prime-gap theorem](../../../../formal/GaloisForLFunctions/RHTower/PrimeShortIntervalsSevenTwelfths.lean#L63) · [First gate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L337) · [Smooth half-power reading](acs-pvc-a-smooth-midpoint-on-products-with-many-prime-factors.md)

## Positive surplus of the lower triples

The two triple boxes have a **positive excess on the left at every sufficiently large midpoint**. Write \(y=(3n)^{1/3}\). Then
\[
 T_- - T_+\sim \frac{K n}{\log^2(3n)},\qquad
 K=\frac{27}{2}\int_0^{1/3}\big[\log^2(1-v)-\log^2(1+v)\big]dv>0.
\]
Indeed the rescaled prime-count measure on \([2/3,4/3]\), multiplied by \(\log(y)/y\), tends to Lebesgue measure. This follows first on subintervals by the ordinary prime number theorem, then on the triple boxes by finite rectangular approximation because their product boundaries have volume zero. Each log price per ordered triple is \(\log y+O(1)\). Pure cubes cost \(O(y)\). The lower and upper box volumes are \(\frac12\int_{2/3}^1\log^2 u\,du\) and \(\frac12\int_1^{4/3}\log^2 u\,du\), respectively, by taking logarithms of the three coordinates and integrating over their sum. Strict positivity follows from \(-\log(1-v)>\log(1+v)\) for \(0<v<1/3\). [Ordinary prime number theorem](../../../../formal/GaloisForLFunctions/PNTPlus/Consequences.lean#L825)

There is also a pairing of actual primes. For \(0\le t\le y/3\) the excess of the prime count in \((y,y+t]\) over that in \([y-t,y]\) is uniformly \(o(y/\log y)\), by the same theorem on this fixed range of dilates. Discard the first \(E\) upper primes, where \(E\) is the maximum nonnegative excess. Match the \((j+E)\)-th prime above \(y\) to the \(j\)-th below it, including \(y\) if prime. Each matched lower prime is at least the additive reflection of its upper partner. Every retained upper triple maps into the left interval, because
\[
 \prod_{i=1}^3(1+u_i)+\prod_{i=1}^3(1-u_i)=2+2\sum_{i<j}u_iu_j>2
\]
for its normalized displacements \(u_i=(p_i-y)/y>0\). Discarding incident triples costs \(o(y^3/\log^2 y)\). The weight difference costs \(O(1)\) per matched tuple. Tuples with three equal coordinates can be omitted at \(O(y)\) cost. Every triple in \([7y/8,8y/9]^3\) lies on the left and is outside the image: its hypothetical upper primes would all be at least \(10y/9\), giving product greater than \(4n\). This exhibits a positive-volume supply of unpaired ordinary prime triples.

The excess \(T_--T_+\) exceeds every fixed sublinear power eventually. A first-strip estimate has to cancel its positive main term against the completed center and the smooth products of multiplicity at least four. The coefficient and the prime pairing are proved on paper.
