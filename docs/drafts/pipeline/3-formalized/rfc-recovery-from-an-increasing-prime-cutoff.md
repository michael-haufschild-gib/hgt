# Recovery from an increasing prime cutoff

- **Stage** 3-formalized

For a nondecreasing integer cutoff \(b\), let \(A_b(X)\) be the signed prefix on integers avoiding all primes through their own \(b(n)\). For each \(s>0\), put \(E(y)=\prod_{p\le y}(1-p^{-s})^{-1}\). The bound \(|A_b(n)|\le Cn^s\) gives \(|M(X)|\le2C(b(X)+1)E(b(X))^2 X^s\) for every \(X\). Conversely \(|M(n)|\le Cn^s\) gives \(|A_b(X)|\le4C(b(X)+1)E(b(X))X^s\).

For \(y\ge b(n)\), induct on \((n,y)\). Adding a prime creates a term at \(\lfloor n/p\rfloor\) with coefficient cost \(p^{-s}\). At \(y=b(n)\), the current constant-cutoff interval has charge equal to a difference of two \(A_b\) values; its preceding boundary has a strictly smaller cutoff. Removing the primes through \(b(X)\) costs a further product of at most \(E(b(X))\).

**Lean.** `recovering_above_an_increasing_prime_cutoff`, `full_prefix_from_sifted_prefix`, and `sifted_prefix_from_full_prefix` in [RecoveringTheMobiusPrefixFromAnIncreasingPrimeCutoff](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/RecoveringTheMobiusPrefixFromAnIncreasingPrimeCutoff.lean).
