# Signed mass in a cube-root rough row

- **Stage** 3-formalized
- **Question** Which sharp terminal rows in the least-prime recursion have an unconditional sign and a positive supply of exposed primes?

Let \(L<U\le2L\). For \(y^3\ge U\), a squarefree nonunit tail whose primes exceed \(y\) is a prime or a product of exactly two distinct primes. Thus its signed balance is the available primes minus the eligible semiprimes. Write \(s=L^{1/6}\). At fixed logarithmic relative width, the cube-root product estimate gives demand at most \((U-L)/(7\log s)\), while the prime count is at least \(0.99(U-L)/\log(2s^6)\). For large \(s\) their ratio is below \(9/10\). If \(y>L\), all eligible tails are already primes.

The signed balance is at least one tenth of the actual prime row. Smaller least-prime cutoffs lead to longer tails of both signs.

The obstruction occurs at every sufficiently large \(X\). Choose a prime \(2X^{1/4}<p\le4X^{1/4}\). The least-prime branch at \(p\) contributes at least \(X/(20p\log X)\), hence at least \(X^{3/4}/(80\log X)\). An absolute square-root estimate on each stopped prefix fails already at depth one.

On every sufficiently large octave take all least primes in \((2X^{1/4},X^{5/16}]\). Their reciprocal mass is at least \(1/10\). Each branch contributes at least \(X/(20p\log X)\), so their total signed mass is at least \(X/(200\log X)\). The dyadic quotient endpoints are exactly \(\lfloor X/p\rfloor,\lfloor2X/p\rfloor\), also the endpoints in the sharp real-window estimate.

Across this region any disjoint matching must leave vertices unmatched there or export positive endpoints to negative partners outside. The sum of these two counts is at least the signed mass. This forces at least \(X/(200\log X)\) such vertices or crossings on every large octave, for every edge relation.

**Lean.** `eventually_cube_root_signed_surplus`, `eventually_large_single_prime_branch`, `eventually_prime_order_signed_branches` and `eventually_forced_least_prime_flux` use only `propext`, `Classical.choice` and `Quot.sound`. [Signed cube-root rows](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSignOfCubeRootRows.lean)
