# Fixed vertices and crossing vertices can both retain the full signed exponent

- **Stage** 1-in-progress
- **Question** Can one short involution at prescribed sparsity retain the full Mertens power exponents in each of the two disjoint signed remainders separately?

Start with a finite collection of high disjoint prime ranges with small uncovered fraction. Let \(Q_0\) be their product modulus. Every integer coprime to \(Q_0\) is fixed. Choose one further short exchange \(p\leftrightarrow w=qr\) in a disjoint range of modulus \(P\), with all primes in all ranges exceeding five. Put \(Q=30P Q_0\).

For \(a\in\{2,3,5\}\), add the exchange only on squarefree integers satisfying \((n,Q)\in\{ap,aw\}\). These were all fixed. The common external factor is coprime to \(Q\), so the two gcd rows interchange and all other pairs persist. At each cutoff the new fixed and crossing population is a subset of the old unpaid population. Write \(D_j G(X)=G(\lfloor X/j\rfloor)\) and \(U=M_Q\). The parameter \(a\) subtracts the signed row sum \(D_a(D_p-D_w)U\) from the original fixed prefix. The signed crossings receive the same change with opposite sign.

The difference between any two fixed prefixes is, up to sign, \((D_a-D_b)(D_p-D_w)U\). Both sharp differences are invertible on every positive power class, and \(U\) has exactly the powers of \(M\). At an exponent where \(M\) fails, no two candidates can have bounded fixed prefixes, and no two can have bounded crossing prefixes. Three candidates therefore suffice for both prefixes to fail in one candidate. The same candidate works simultaneously for all exponents. Otherwise each of the three has a bad exponent. At the largest of the three exponents, \(M\) still fails and each candidate has at least one bounded component, a contradiction. All fixed and crossing prefixes are finite divisor sums on \(M_Q\), which gives the other implication.

The construction adds one genuine exchange on one gcd class. It requires three candidate refinements of one table, independent of the number of ranges. It would show that even two disjoint contributions to the exact signed prefix can each have its full power spectrum.
