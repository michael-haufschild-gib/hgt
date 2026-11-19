# A single factorization involution at all cutoffs

- **Stage** 3-formalized
- **Theorem** One involution of the squarefree integers by prime-to-semiprime exchanges, with displacement \(o(n)\) and \(o(X)\) unpaid vertices in every sharp prefix. The same involution must work for every tolerance.

On \((2^j,2^{j+1}]\) minimize the larger of the number of unmatched squarefree integers and the longest edge length. The empty matching makes the minimum well-defined. The [short-exchange construction](rfc-density-one-restricted-matching.md) bounds the minimum by \(\varepsilon 2^j\) for every sufficiently large \(j\), for each \(\varepsilon>0\). Choose a minimizing matching on each block. Acting by its two-cycles on its block and fixing the unit defines an involution on the whole half-line. Every nontrivial move is an actual one-to-two exchange, of displacement \(o(n)\).

Choose \(K\) beyond the threshold for \(\varepsilon\). Through \(2^{j+1}\), the fixed squarefree population is at most \(2^K+\varepsilon\sum_{i=K}^j 2^i\). At a cutoff \(2^j<X\le 2^{j+1}\), only edges in block \(j\) can cross. Their lower endpoints lie in the last \(\varepsilon 2^j\) integers below the cutoff. Thus the unpaid population is at most \(2^K+3\varepsilon X+1\). Its signed sum equals the exact Möbius prefix, including the unit. The conclusion supplies no power saving for this signed population.

**Lean.** `dyadic_switch_prefix_bound` bounds both crossing and fixed populations from the block costs. `one_involution_with_sublinear_unpaid_prefix` proves the all-cutoff identity and both sublinear estimates for `dyadicPrimeSwitch`. Its axiom audit lists `propext`, `Classical.choice` and `Quot.sound`. [One involution for every sharp prefix](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/OneInvolutionForEverySharpPrefix.lean)
