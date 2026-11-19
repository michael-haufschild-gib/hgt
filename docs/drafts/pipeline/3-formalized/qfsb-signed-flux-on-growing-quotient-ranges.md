# Signed flux on growing quotient ranges

- **Stage** 3-formalized
- **Question** How much of a centered rough quotient sum on a growing set of cells can one matching move at square-root precision?

Let \(M_y\) be the Möbius prefix coprime to the primorial at \(y\). Dirichlet convolution gives \(\mu_y=1_{y\text{-smooth}}*\mu\), including multiplicities at integers divisible by excluded primes. For any exchange involution \(F\), write \(D_F,C_F\) for its signed fixed and crossing prefixes. For each quotient atom \(q\), replace \(M_y(\lfloor X/q\rfloor)\) by
\[
 \sum_{d\le X/q,\ d\text{ smooth}}(D_F+C_F)(\lfloor X/(qd)\rfloor).
\]
Subtract the evaluations at both endpoints. This charges one copy per smooth divisor. The convolution recombines those copies to the rough cofactor coefficient. In successive transports the differences of readings telescope at each visit, including returns.

Choose one density-one matching whose crossing prefix has absolute value at most \(\log(1+t)\) at every \(t\). At the upper endpoint \(X\), the total crossing cost on atoms \(q\in S\) is at most
\[
 \log(1+X) E_{1/2}(y)\sqrt X\sum_{q\in S}|a(q)|/\sqrt q .
\]
The lower endpoint has its own copy of the bound. Thus any polylogarithmic range of atoms with polylogarithmic weights costs \(X^{1/2+o(1)}\) on the moving part at the log-square wall. This applies to ordinary primes, surviving prime powers, and the floor increments \(y1_{y\mid q}\) with the same matching. The fixed contribution and the higher quotient atoms remain signed. These are the unresolved terms in an estimate for the complete centered reading.

**Lean.** `smooth_lift_of_the_full_prefix`, `two_cutoff_rough_quotient_flux`, `signed_flux_along_a_quotient_history` and `one_matching_for_all_rough_quotient_boundaries` establish the exact account and uniform price in [SignedFluxOnGrowingQuotientRanges.lean](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/SignedFluxOnGrowingQuotientRanges.lean).

**Further question.** Can the prime-minus-floor weights gain on the fixed contribution over the same ranges, retaining all smooth divisor multiplicities?
