# Removing a growing terminal band from the centered reading

- **Stage** 1-in-progress
- **Question** Can both signs of every sufficiently low quotient be removed from a full sharp reading while pricing the induced change on every earlier cofactor?

Let \(a(q)\) be the surviving Mangoldt weights, or just their ordinary-prime part. Write \(A(t)=\sum_{q\le t}a(q)\), \(c=a*\mu\), \(B_T(t)=\sum_{d\le T}c(d)\lfloor t/d\rfloor\). Then \(A(t)=B_T(t)\) at every integer \(t\le T\), by Dirichlet inversion. The bound \(|c(d)|\le\sum_{q\mid d}\Lambda(q)=\log d\) is uniform in the prime cutoff and in any signed weights dominated by \(\Lambda\).

For \(T\ge y\ge1\), replace the original quotient center \(y\lfloor t/y\rfloor\) by \(B_T(t)\). The new reading vanishes at every cofactor \(m>X/(T+1)\). Over **all** cofactors the cost of the change, with its sign, is
\[
 \sum_{d\le T}c(d)\Psi(\lfloor X/d\rfloor,y)-y\Psi(\lfloor X/y\rfloor,y).
\]
This follows by exchanging the divisor and cofactor sums. Each floor sums against the deleted Möbius function to the population of smooth integers. In particular \(A-B_T\) must be retained at every smaller cofactor. The cost of the first term is bounded by \(2 E_{1/2}(y)\sqrt X\sqrt T\log T\), using Rankin's inequality and \(\sum_{d\le T}d^{-1/2}\le2\sqrt T\). Subtracting the two prefix identities keeps both endpoint costs and exact center signs.

At the log-square prime cutoff, every \(T=X^{o(1)}\) above the cutoff preserves the half-plus criterion. For \(T=X^\delta\) the first-term cost is \(X^{(1+\delta)/2+o(1)}\). This is a signed elimination of an entire growing band for several arithmetic weights. The outstanding cancellation is in the rebased reading at the smaller cofactors.

**The rough floor reaches the hyperbola.** Replace \(\lfloor t/d\rfloor\) by \(R_y(\lfloor t/d\rfloor)\), where \(R_y\) counts *all* positive integers coprime to the primorial. The inverse of its increment is exactly \(\mu_y\). With \(c_y=a*\mu_y\), the resulting center agrees with \(A(t)\) for all \(t\le T\). Its total charge against \(\mu_y\) is now just \(\sum_{d\le\min(X,T)}c_y(d)\). Each divisor coefficient costs at most \(\log d\) for every Mangoldt-dominated weight. Hence the entire charge is at most \(T\log T\), uniformly in \(y\). With \(T=\lfloor\sqrt X\rfloor\) the price is \(O(\sqrt X\log X)\) at every endpoint. This removes **all** cofactors above the hyperbola from the rebased reading for both ordinary primes and prime powers. Subtract the old \(y\Psi(X/y,y)\) when comparing centered readings. The actual smaller-cofactor residual still includes the new rough-count center at each quotient.
