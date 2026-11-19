# Shrinking the cofactor range for genuine prime readings

- **Stage** 3-formalized

At the log-square wall \(y=b(X)\), retain every ordinary prime greater than \(y\) and allow independent signed weights of magnitude at most \(\Lambda\) on all proper prime powers. The cost of the complete removed head, including its final sharp prefix, is \(O_u(X^u)\) for every \(u>\alpha\Theta\), uniformly in \(T\le X^\alpha\). Here \(\Theta\) is the zeta zero abscissa. At \(T=\lfloor X^{4/7}\rfloor\), the cost is \(O(X^{1/2-1/84000})\) and the corrected reading uses only cofactors through \(X^{3/7}\).

The genuine Mangoldt head equals the negative logarithmically weighted rough Möbius prefix at \(T\). For \(\Theta<s\le1\), partial summation bounds it by \(O_s(E_s(y)T^s(1+\log T))\). The perturbation is a sum of proper-power weights against rough prefixes at \(\lfloor T/q\rfloor\). The series \(\sum_{q\text{ not prime}}\Lambda(q)q^{-s}\) converges. At the moving log-square wall the finite Euler factor costs \(X^{o(1)}\). The explicit transfer uses the project's bound \(\Theta\le20999/24000\). More generally, atomwise total variation of proper-power edits controls their cumulative signed cost on arbitrary observation walls and heights.

For \(\alpha\Theta\le1/2\), the half-plus estimate for the corrected smaller-cofactor Mangoldt sum is equivalent to the half-plus Mertens estimate. The remaining estimate on this interior is open.

**Lean.** `structured_prime_head_above_the_strip`, `signed_price_of_all_proper_power_edits`, `shrinking_the_cofactor_range_for_prime_readings`, `ordinary_and_prime_power_transfer_to_three_sevenths`, and `mertens_criterion_on_the_shrunken_cofactor_range` in [ThePrimeReadingsBeyondTheHyperbola.lean](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/ThePrimeReadingsBeyondTheHyperbola.lean).
