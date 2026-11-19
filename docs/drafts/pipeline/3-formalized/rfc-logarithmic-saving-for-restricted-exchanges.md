# Counting missed exchanges beyond a complete period

- **Stage** 3-formalized
- **Target** Some absolute \(c>0\) permits a restricted matching on each sufficiently large \((X,2X]\) with both unmatched population and maximum displacement \(O(X/(\log X)^c)\).

For a prime band \(B\) and its paired single primes \(A\), call an integer missed if its set of prime divisors in \(B\) is not a singleton from \(A\). The missed indicator has an exact squarefree divisor expansion. The coefficient of 1 is 1. For each nonempty subset \(S\subseteq B\), the coefficient of \(d=\prod_{p\in S}p\) is \((-1)^{|S|}|S\cap A|\). Indeed each good singleton \(p\) contributes its divisibility indicator times the product of all complementary nondivisibility indicators. Across disjoint bands the coefficients multiply, with absolute value bounded by \(2^{\omega(d)}\).

Let \(z\) bound all the primes, let \(a_d\) be the combined coefficients, and let \(H=\sum_d a_d/d\), the exact missed fraction in a complete period. For \(0<\eta<1\), comparing \(\lfloor X/d\rfloor/X\) with \(1/d\) costs at most \(X^{-\eta}d^{\eta-1}\) for every \(d\), on either side of \(X\). Hence
\[
 \left|X^{-1}\#\{n\le X:n\text{ missed}\}-H\right|
 \le X^{-\eta}\prod_{p\le z}(1+2p^{\eta-1}).
\]
With \(z=\exp(\sqrt{\log X})\) and \(\eta=1/\log z\), the product is at most a fixed power of \(\log z\) by Mertens' theorem. The sampling error is smaller than every fixed negative power of \(\log X\), regardless of the enormous combined period.

The estimate holds for *every* bounded function \(|f|\le1\) of the local gcd, not only missed-event indicators. Its divisor coefficient is \(a_d=\sum_{b\mid d}\mu(d/b)f(b)\), bounded by \(2^{\omega(d)}\) for squarefree \(d\). Thus the same Euler product controls all local tests simultaneously.

Take the cell parameter \(J=\lceil(\log X)^{1/8}\rceil\). The sharp cell capacity holds once \(k\log 2\ge J\) and \(2^k\) exceeds an absolute threshold. Choose successive exponents \(k,25k,25^2k,\ldots\) until \(2^{24k_i}\le z\). There are at least \(c_0\log\log X\) bands for an absolute \(c_0>0\). Each removes a fixed fraction \(\kappa\) of the remaining full-period residues. Thus \(H\le(1-\kappa)^{c_0\log\log X}\), a negative power of \(\log X\). The first eligible switch gives the required disjoint exchange and costs at most \(2X/J\) displacement. The two cutoff strips cost \(O(X/J)\) vertices.

Equivalently take \(J=2^m\), seed exponent \(C2^m\) above the absolute threshold, and \(m\) bands. Their largest prime is at most \(Z=2^{C50^m}\). At \(X\ge 2^{C100^{m+1}}\), choose \(\eta=1/(C50^m)\). Then \(p^\eta\le2\) and \(X^{-\eta}\le2^{-100\cdot2^m}\). The Euler factor is at most \(\prod_{2<p\le Z}(1+1/p)^4\ll (C50^m)^4\). This makes the relative sampling error \(O(2^{-m})\) throughout the sharp interval between consecutive thresholds. Since \(1-\kappa\ge1/2\), taking \(c=-\log(1-\kappa)/\log 100\) suffices.

**Formalized.** `prime_pattern_sampling` gives the uniform sharp-cutoff error for every bounded gcd test. `logarithmic_saving_for_restricted_matchings` proves both bounds on every sufficiently large octave. `logarithmic_saving_for_one_involution` gives the same rate for the actual unpaid prefix and displacement of one fixed involution. [Divisor sampling](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/SamplingPrimeDivisorsAtSharpCutoffs.lean) · [Restricted exchanges](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/LogarithmicSavingsForRestrictedExchanges.lean)

**Boundary.** Every ordinary prime in \((X,2X]\) is fixed when all bands end below \(X\). These vertices contribute \(\asymp X/\log X\) unsigned remainder. More generally, `unsigned_dyadic_power_boundary` rules out a uniform power saving for the unpaid prefix of any single global restricted involution.
