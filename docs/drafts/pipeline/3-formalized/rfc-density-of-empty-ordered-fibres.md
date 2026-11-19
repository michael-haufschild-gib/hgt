# Positive proportion of negative vertices in empty ordered fibres

- **Stage** 3-formalized
- **Question** Does the obstruction occupy positive density on every large dyadic block?

For each negative squarefree \(c\le X^{1/24}\), put \(T=X/c=t^{12}\). Take primes \(2t^4<q\le t^5\) and \(T/q<r\le2T/q\). Then \(c<q<r\), and \(cq^3>2X\) makes the ordered fibre of \(cqr\) empty. The two largest primes recover \(c\), so all these sources are distinct across all cofactors. The prime number theorem gives \(\gg T/(q\log T)\) choices of \(r\), uniformly. Differencing Mertens' first theorem at the endpoints gives \(\sum_q1/q\gg1\). Hence each cofactor supplies \(\gg X/(c\log X)\) empty-fibre vertices.

The signs separate exactly:
\[
 2\sum_{\substack{c\le N\\\mu(c)=-1}}1/c
 =\sum_{\substack{c\le N\\ c\ {\rm squarefree}}}1/c-\sum_{c\le N}\mu(c)/c.
\]
The first sum on the right is at least half the full harmonic sum, and the second has absolute value at most one. Taking \(N=\lfloor X^{1/24}\rfloor\) gives at least \((\log X)/192\) in negative-cofactor reciprocal mass for large \(X\). The row lower bound \(X/(260c\log X)\) gives at least \(X/49920\) distinct empty-fibre negatives. All can be transported simultaneously.

**Lean** [Prime mass in deficient rows](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PrimeMassInDeficientRows.lean), `eventually_deficientProducts_lower`. [Positive density of the transported debt](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PositiveDensityOfTheTransportedDebt.lean), `eventually_linear_deficient_family`, `eventually_linear_empty_fibre_debt` and `eventually_linear_cross_fibre_transport`.
