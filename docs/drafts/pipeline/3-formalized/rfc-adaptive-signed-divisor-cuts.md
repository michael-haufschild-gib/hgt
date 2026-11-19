# Exact signed divisor sums at adaptive cuts

- **Stage** 3-formalized
- **Source** [Signed cancellation](../../../reports/review-1811/obstacles-summary.md#211-mathematics-for-a-proof-by-signed-cancellation-alone)

Delete the least prime of each nonunit squarefree tail in \((L,U]\) whose prime factors exceed \(y\). Prime tails give a single boundary count. Every longer tail with least prime \(p\) continues in \((\lfloor L/p\rfloor,\lfloor U/p\rfloor]\), with threshold \(p\) and reversed sign. These fibres are disjoint. On any stopped row, summing \(\mu(d)\) over the divisors of the gcd with the primorial up to \(y\) selects exactly the admissible tails.

At every adaptive cut, the signed boundary and terminal charges equal the unmatched Möbius count of every disjoint matching, with a separate unit correction. Full expansion has exactly one root plus one row per nonunit squarefree prefix up to \(U\) with all prime factors above \(y\). Every adaptive rule makes at most that many visits, including terminal rows with empty sharp intervals.

**Lean** [The signed boundary of a prefix](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSignedBoundaryOfAPrefix.lean), `tailBalance_recursion`, `tailBalance_divisor_inversion`, `adaptive_cut_conservation`, `signed_unmatched_at_cut`, `full_cut_visits`, `adaptive_cut_visits_le`.
