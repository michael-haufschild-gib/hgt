# Saturation when three prime factors can survive

- **Stage** 1-in-progress
- **Question** On the whole sharp octave of squarefree integers with every prime factor above \((2X)^{1/4}\), can a restricted matching leave only single primes unmatched, even though there are more semiprimes than primes?

**Matching before the sign estimate.** At every sufficiently large \(X\), uniformly for \(y^4\ge2X\), the rough squarefree block has only primes, semiprimes and triples. In the row of the least prime \(p>y\), composite tails are pairs and use no more than the number of single-prime tails. This is the cube-root estimate at quotient scale \(X/p\), since \(p^4>2X\). If a triple exists then \(X/p>p^2/2\), so the required scale is uniformly large. Match all triples into semiprimes by increasing rank in each least-prime row. The remaining semiprimes form a complete bipartite graph with the root primes. A second rank pairing leaves exactly the absolute signed imbalance of the **entire** rough block, regardless of which sign prevails. The strictly positive surplus below would identify the remaining vertices as single primes and extend the recursion to the next layer.

In units of \(X/\log X\), the limiting number of semiprimes is \(\int_{1/4}^{1/2} k(t)\,dt\), where \(k(t)=1/[t(1-t)]\). This exceeds one because \(k>4\) below the square root. The trapezoidal bound on the two intervals split at \(3/8\) gives at most \(67/60\) by convexity.

For triples, write \(t=\log p/\log X\) for the smallest prime and \(a=t/(1-t)\). Relative to the size of its quotient prime row, the pairs available above \(p\) have limiting mass \(\int_a^{1/2} k(v)\,dv\ge 2-4a\). The prime-row weights integrate against \(da/a\). Since \(1/a\ge4-4a\), the total triple mass is at least
\[
 \int_{1/3}^{1/2}(2-4a)(4-4a)\,da=11/81 .
\]
Thus primes plus triples exceed semiprimes by at least \(31/1620\) in the limit. The sharp integer estimate needs uniform prime-window integration, including the thin collars at both extremal exponents.

Each triple can first merge its two largest primes inside its least-prime row, by the cube-root theorem. The remaining semiprimes can then merge into distinct root primes. This uses both layers and would attain the signed surplus with exactly the uncovered single primes as remainder. More generally, nonnegative signed balances throughout a prime-prefix subtree suffice for the same construction by induction from the leaves.

Uniformity in the roughness cutoff reduces to one endpoint. For \((2X)^{1/4}\le y\le z\le X\), the root prime count is constant. Raising the cutoff removes children whose prime-minus-semiprime balances are nonnegative by the cube-root capacity. Hence \(F(X,2X;z)\ge F(X,2X;y)\) on the actual integer rows. Above \(X\) only single primes can remain.
