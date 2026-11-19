# Removing a growing terminal band from the centered reading

- **Stage** 3-formalized
- **Question** Can both signs of every sufficiently low quotient be removed from a full sharp reading while pricing the induced change on every earlier cofactor?

Let \(a(q)\) be the surviving Mangoldt weights, or just their ordinary-prime part. Write \(A(t)=\sum_{q\le t}a(q)\), \(c=a*\mu\), \(B_T(t)=\sum_{d\le T}c(d)\lfloor t/d\rfloor\). Then \(A(t)=B_T(t)\) at every integer \(t\le T\), by Dirichlet inversion. The bound \(|c(d)|\le\sum_{q\mid d}\Lambda(q)=\log d\) is uniform in the prime cutoff and in any signed weights dominated by \(\Lambda\).

For \(T\ge y\ge1\), replace the original quotient center \(y\lfloor t/y\rfloor\) by \(B_T(t)\). The new reading vanishes at every cofactor \(m>X/(T+1)\). Over **all** cofactors the cost of the change, with its sign, is
\[
 \sum_{d\le T}c(d)\Psi(\lfloor X/d\rfloor,y)-y\Psi(\lfloor X/y\rfloor,y).
\]
This follows by exchanging the divisor and cofactor sums. Each floor sums against the deleted Möbius function to the population of smooth integers. In particular \(A-B_T\) must be retained at every smaller cofactor. The cost of the first term is bounded by \(2 E_{1/2}(y)\sqrt X\sqrt T\log T\), using Rankin's inequality and \(\sum_{d\le T}d^{-1/2}\le2\sqrt T\). Subtracting the two prefix identities keeps both endpoint costs and exact center signs.

At the log-square prime cutoff, every \(T=X^{o(1)}\) above the cutoff preserves the half-plus criterion. For \(T=X^\delta\) the first-term cost is \(X^{(1+\delta)/2+o(1)}\). This is a signed elimination of an entire growing band for several arithmetic weights. The outstanding cancellation is in the rebased reading at the smaller cofactors.

**The rough floor reaches the hyperbola.** Replace \(\lfloor t/d\rfloor\) by \(R_y(\lfloor t/d\rfloor)\), where \(R_y\) counts *all* positive integers coprime to the primorial. The inverse of its increment is exactly \(\mu_y\). With \(c_y=a*\mu_y\), the resulting center agrees with \(A(t)\) for all \(t\le T\). Its total charge against \(\mu_y\) is now just \(\sum_{d\le\min(X,T)}c_y(d)\). Each divisor coefficient costs at most \(\log d\) for every Mangoldt-dominated weight. Hence the entire charge is at most \(T\log T\), uniformly in \(y\). With \(T=\lfloor\sqrt X\rfloor\) the price is \(O(\sqrt X\log X)\) at every endpoint. This removes **all** cofactors above the hyperbola from the rebased reading for both ordinary primes and prime powers. Subtract the old \(y\Psi(X/y,y)\) when comparing centered readings. The actual smaller-cofactor residual still includes the new rough-count center at each quotient.

For the full rough Mangoldt reading, write \(L_y(t)=\sum_{d\le t}\mu_y(d)\log d\). The corrected smaller-cofactor sum equals \(L_y(\min(T,X))-L_y(X)\). Recovering the original centered reading subtracts both \(L_y(\min(T,X))\) and \(y\Psi(\lfloor X/y\rfloor,y)\). For every arithmetic reading the smaller-cofactor sum is also the sum of the same matching’s signed fixed and crossing flux between \(\min(T,X)\) and \(X\), with the original quotient weight at both endpoints.

At two observation cuts with the same weight and sieve, only coefficients between the two head endpoints survive. Taking the hyperbola head gives interval cost at most \((\lfloor\sqrt U\rfloor-\lfloor\sqrt L\rfloor)\log\lfloor\sqrt U\rfloor\). The head charge is exactly constant between squares. Changing the weight or prime wall at the join adds the signed coefficient difference on the common head.


**Lean.** `cost_of_eliminating_a_growing_quotient_band`, `rough_head_and_interior`, `two_cutoff_change_of_the_rough_reading` and `square_crossings_pay_the_interval_error` give the exact finite estimates. `signed_flux_of_the_corrected_interior` retains both boundary charges. `mertens_criterion_below_the_hyperbola` proves equivalence between the half-plus bound for the smaller-cofactor reading at the log-square wall and the full Mertens bound. The estimate of that reading is open.
