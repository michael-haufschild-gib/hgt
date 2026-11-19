# Transport of the two largest primes

- **Stage** 3-formalized
- **Source** [Signed cancellation](../../../reports/review-1811/obstacles-summary.md#211-mathematics-for-a-proof-by-signed-cancellation-alone)

The replacement \(cqr\leftrightarrow cp\) keeps the exact quotient interval \((L/c,U/c]\). For a negative cofactor \(c\), pair equal ranks in the increasing lists of eligible primes and ordered semiprimes. Both lists lose precisely the entries beyond their common minimum cardinality. Removing the largest prime from \(cp\), or the two largest from \(cqr\), recovers \(c\). Thus different rows never reuse an integer, regardless of factor count.

At scale \(s^2=L/c\), fixed aspect ratio and width at least \(s^2/(\log s)^B\), the prime supply eventually exceeds the semiprime demand by every prescribed factor. Sum the sharp partner-window prime bound over \(q\asymp s\); the second prime introduces an extra inverse logarithm. This exhausts every eligible source even though its original ordered fibre has no positive vertex in the full octave.

**Lean** [Prime supply](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/PrimeSupplyForBalancedProducts.lean), `eventually_balancedProducts_capacity`. [Transport](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TransportAcrossOrderedFibres.lean), `exists_ranked_transport` and `exists_transport_covering_empty_fibres`.
