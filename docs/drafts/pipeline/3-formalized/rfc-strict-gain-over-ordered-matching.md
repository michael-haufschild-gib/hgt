# Linear gain over the best ordered-fibre matching

- **Stage** 3-formalized
- **Question** Can a cross-fibre transport increase total matching size by a positive proportion of the octave while retaining every old endpoint?

Put \(S=X^{1/24}\). For every negative cofactor \(c\le S\), merge the deficient pairs counted in [the density argument](rfc-density-of-empty-ordered-fibres.md) into distinct primes above \(X/c\). The new positives \(cp\) would use the old row \(b=c/P^+(c)\le S\). Reassign the negative targets of **every** old row \(b\le S\) inside that same row. For \(T=X/b\), use pairs \(qr\) with \(T^{1/16}<q\le T^{1/2}\) and \(T/q<r\le2T/q\). Then \(r>q>S\ge b\), whereas the second largest prime of every reserved \(cp\) is at most \(S\). All reassigned endpoints decode to their original \(b\).

Split the smaller-prime range at \(T^{1/8}\) and \(T^{1/4}\). In each interval \((v,v^2]\), Mertens' first theorem gives \(\sum1/q\ge3/8\) eventually, uniformly as \(v\to\infty\). Thus the full reciprocal mass is at least \(9/8\). Sharp dyadic prime-window bounds count at least \(0.99T/(q\log T)\) larger partners for each \(q\), while the prime demand of the old row is at most \(1.01T/\log T\). The reserved positives are therefore free even after paying every displaced edge.

Keep all other old edges. The resulting matching covers all old negative endpoints and a disjoint additional family of size \(\gg X\). Alternating with the original matching preserves every old positive endpoint as well. The strict cardinal gain follows by counting negative endpoints.

**Sharp block conclusion.** The new matching retains every old endpoint, gains at least \(X/49920\) edges, and has an unmatched set contained in the old one with at least \(X/24960\) fewer vertices. A second conclusion achieves the same gain while covering all empty-fibre negatives and retaining all old positives.

**Lean** [Room for displaced prime targets](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/RoomForDisplacedPrimeTargets.lean), `eventually_replacement_capacity`. [Strict gain over ordered matchings](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/StrictGainOverOrderedMatchings.lean), `eventually_strict_gain_over_ordered`, `eventually_linear_reduction_of_ordered_debt` and `eventually_linear_gain_covering_all_empty`.
