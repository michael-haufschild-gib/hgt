# Arithmetic ladder quotients and twisted Green fibres

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B133, one-prime arithmetic carrier.

## Question

The diagonal p-unit of SL₂ identifies degrees p^k and p^{k+2} on the product
of the degree geodesic and the p-adic apartment. Can a scalar Green function on
that quotient retain the prime-ladder kernel and its self-intersection diagonal?

## Proposed result

The scalar quotient loses the ladder level: a kernel invariant under the diagonal
p-unit cannot reproduce the prime-ladder Green kernel. A Robin mass invariant under
that action cannot equal the torsion self-intersection either. The latter is a
separate obstruction for the torsion diagonal, not an identification of Weil’s
renormalized diagonal with that self-intersection.

The positive replacement is the family of unitary twists. For 0<r<1 and |z|=1,
periodize r^{|k|} by 2ℤ with character z. The resulting 2×2 Green matrix has
entries with denominator (1−r²z)(1−r²/z), is positive definite, and its Fourier
coefficients recover every original ladder entry. At r=p^{−1/2} this is the
critical tree Green kernel. The quotient needs the full twist parameter to retain
the arithmetic ladder.

## Status

Corpus normalization gives the exact obstruction:
`frobeniusIntersection(1,p^k)=log p+1/(1−p^{−2k})` for k≥1, strictly decreasing
in k; the two identified odd levels k=1,3 therefore disagree. The diagonal
increment is `selfIntersection(p³)−selfIntersection(p)=2 log p`.
No previous corpus result supplied this arithmetic-unit descent obstruction
or the corresponding two-level Bloch fibre reconstruction. No general adelic
carrier exclusion is asserted: the obstruction concerns quotients containing the
diagonal p-unit. Bloch reconstruction and the Robin obstruction remain to formalize.
