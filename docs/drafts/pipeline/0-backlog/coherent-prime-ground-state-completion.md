# Coherent completion by the prime ground states

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** finite-prime horizon finite part; proposed valuation/KMS diagonalization
- **Count:** uncounted; separate novelty, paper, and Lean obligations

For a finite prime set Q, let H_Q be ell-two on its supported positive integers
and let A_Q be the actual operator `diag(log n)-P_Q+gamma_Q I`. The active
valuation-spectrum card addresses its complete finite-prime diagonalization.

For Q contained in R, conjecture compatible embeddings obtained by tensoring
with the normalized geometric ground vector at each new prime. In the unique
factorization n=d*e with d Q-supported and e supported on R minus Q,

`V_(Q,R) f(d*e)=sqrt(delta_(R minus Q))*f(d)/sqrt(e)`.

Finite Euler products should prove isometry and composition. The local ground
equation should prove `A_R V_(Q,R)=V_(Q,R) A_Q`, including domain preservation.
The resulting Hilbert completion would have an excitation basis indexed by all
positive integers, with energies

`gamma+log(n)+tameDifferent(n)=gamma+2log(n)-selfIntersection(n)`.

The actual finite-prime operator and the embedding identities must be proved;
defining an abstract diagonal operator with these eigenvalues does not suffice.
Compact resolvent and spectral simplicity likewise require their own proofs.

This completion changes the embeddings of the finite-prime sequence spaces.
Comparison with the original full Weil-test carrier and uniform passage from
arithmetic horizons remain separate problems. No all-primes Weil sign or RH
claim follows from a formal infinite tensor product.

Inspected leads are recorded on
`docs/drafts/pipeline/2-fully-proven/local-valuation-haar-diagonalization.md`.
No computations, no Lean proof, and no contribution count for this conjecture.

A further corpus query for an infinite-prime ground-state/tame-different spectrum
found `HTGeometry/PrimeLogKMSRealization.lean`. Its construction through line 150
was inspected: the carrier is a vacuum and one prescribed log-prime level per
prime, with normalized transition intensities. It does not identify the present
number-minus-Weil-kernel operator or its coherent ground-state embeddings.
It is baseline for thermal terminology, not evidence for the present conjecture.

Possible construction route: use the physical product with the normalized new-
prime ground vector, prove its coefficient formula and its action on the existing
finite-prime eigenbasis, then prove domain intertwining from the actual spectral
domains. Only after those identities may the all-integer excitation carrier serve
as a concrete realization of the Hilbert completion. Density and the completion's
universal property remain obligations, as do novelty and all-prime energy audits.
