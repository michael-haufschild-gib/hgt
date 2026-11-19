# Density one forces unbounded reuse of a smaller prime

- **Stage** 1-in-progress
- **Question** Can short restricted exchanges cover density one if each smaller split prime occurs in only boundedly many distinct primitive exchange patterns?

Compress each edge \(cp\leftrightarrow cqr\), \(q<r\), to its triple \((p,q,r)\), forgetting the cofactor. Suppose each \(q\) occurs in at most \(D\) distinct triples and \(qr/2\le p\le2qr\). A vertex used by the matching is divisible by \(p\) or \(qr\). Add the squares \(n^2\), \(n\ge2\), to these forbidden divisors. Any integer avoiding all of them is a genuinely unmatched squarefree vertex.

**Uniform tail.** For products \(qr>Y\) with \(q\le\sqrt Y\), there are at most \(D\sqrt Y\) terms, each contributing at most \(1/Y\). For \(q>\sqrt Y\) the contribution is bounded by \(D\sum_{q>\sqrt Y}q^{-2}\). Singles \(p>Y\) contribute at most twice the corresponding product mass above \(Y/2\). Square divisors have the same inverse-square tail. Thus the reciprocal mass of all forbidden divisors above \(Y\) is \(O((D+1)/\sqrt Y)\), uniformly in the octave, the table and the cofactors.

**Positive survivor.** Any finite family of forbidden divisors greater than one with a common vanishing reciprocal tail leaves a positive proportion of every sufficiently large octave free, uniformly over the family. Choose \(Y\) so the tail is at most \(1/8\), put \(Q=Y!\), and restrict to \(n\equiv1\pmod Q\). No divisor through \(Y\) occurs. For \(Y<b\le T\), two hits with \(b\mid n\) differ by a multiple of \(Qb\), since a hit forces \((b,Q)=1\). These divisors cost at most \(X/(8Q)+T\) vertices. Choose the fixed \(T\) so the remaining reciprocal tail is at most \(1/(16Q)\); those multiples cost at most \(X/(8Q)\) up to \(2X\). The progression contributes at least \(X/Q-1\) vertices to \((X,2X]\). In particular at least \(X/(4Q)\) unmatched squarefree vertices survive on all sufficiently large octaves.

The obstruction allows the prime ranges, the numbers of cofactors and the triples themselves to vary with \(X\). Hence a density-one sequence of short matchings must use unboundedly many primitive exchange types at some smaller split prime, even though no integer is ever matched twice. The uniform tail criterion also applies to tables whose degrees grow but whose reciprocal tails stay uniformly small.
