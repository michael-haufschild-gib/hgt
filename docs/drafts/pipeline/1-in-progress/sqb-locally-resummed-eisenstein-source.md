# SQB locally resummed complete Eisenstein source

Status: the complete exponential resummation is admitted and nonzero, but
its full-Xi occurrence residual is nonzero. All source, constant-mode, and
actual entire-domain assertions are audited in Lean. The centered source
equation remains open. [Full proof and audit](../3-formalized/sqb-resummed-source-mean-obstruction.md).
RH remains open. Frontier map is read-only. No numerical computations.

Full chain: original Xi/modular source → independent full-Xi occurrence in
the native entire operator → real-spectrum classification → critical line
→ RH. Independent occurrence is the hardest obstacle.

## Concrete source and test

For an actual Xi copy rho, set s=rho/2+2, so Re(s)>2. Consider the original
modular row periodization of h_s(y)=y^s exp(−y). Its Taylor expansion uses
complete Eisenstein fields at s+n, with coefficient

    (−1)^n / (n! Lambda(2s+2n)).

These exponents are the quarter-lattice subsequence j=8+4n and share the
full Xi entire-transform value. Their completion denominators lie in the
absolute-convergence half-plane and are nonzero. The summation must be
proved locally before testing the native norm: the completed finite packet
results exclude native-norm convergence of its nonzero partial sums.

The actual coprime-row realization, absolute row convergence, nonparabolic
height bound, and exact modular strip unfolding are already present in the
Lean corpus. Use them with the full source, including every row and mode.

- [x] Absolute resummation of the complete shifted fields to the row profile.
- [x] Native L² admission of the actual resummed automorphic source.
- [x] Full native mean equals Gamma(s−1), which is nonzero.
- [x] Original constant vector has A1=1, C1=1/3, T1=1 in the actual native graphs.
- [x] Every bounded residual v−(2+mu)Cv has mean (1−mu)/3 times the mean of v.
- [x] Nonzero full-Xi residual and positive normalized residual of the actual domain source CP_s.

A nonzero admitted source alone is insufficient. The explicit residual mean
is (1−mu) Gamma(s−1)/3. An actual Xi target cannot equal one: the audited
real-preimage classifier would force the real Casimir zero to equal
1/4+Im(rho)^2/4. Thus this particular uncentered source cannot supply
occurrence, including on the critical line.

Positive survivor: a literal nonzero admitted full-field resummation, exact
original mean, quantitative residual bound, and exact separation of its
constant component. Centering commutes with the actual covariance. It
removes only the detected component; the centered source's nonvanishing,
entire graph behavior, and full-Xi occurrence remain to be established.
No termwise infinite operator interchange is assumed.
