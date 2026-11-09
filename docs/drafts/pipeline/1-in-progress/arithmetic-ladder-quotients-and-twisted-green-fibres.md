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
p-unit cannot reproduce the Frobenius intersection kernel. A Robin mass invariant under
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
diagonal p-unit. The off-diagonal and torsion-Robin obstructions are formalized in
`HyperbolicArakelovTheory/TheArithmeticPrimeUnitCollapsesTheLadder.lean`; plain source
audit passes, with only `propext`, `Classical.choice`, and `Quot.sound`. Twisted
reconstruction and positivity remain under Lean verification.

The same obstruction extends to every unitary automorphy law: the intersections
at (1,p) and (1,p³) are positive and unequal, while unitary translation preserves
their absolute values. Thus one unitary twist cannot carry the full Frobenius
kernel either. This strengthening has an exact paper proof; Lean verification is
pending. The positive survivor below reconstructs the tree channel, not the full
Frobenius kernel, from a family of twists.

## Positive survivor: exact proof

Put E_e(z)=∑_{j∈ℤ}r^{|e+2j|}z^j, |z|=1, 0≤r<1. Absolute convergence follows
from the bilateral geometric series and the injection j↦e+2j. Reindexing gives
E_{e+2}(z)=z^{−1}E_e(z). Splitting the sum at zero gives

    E_0(z) = (1−r⁴)/D,
    E_1(z) = r(1−r²)(1+z^{−1})/D,
    D = (1−r²z)(1−r²/z) = |1−r²z|² > 0.

For complex u,v the fibre energy is exactly

    Re(E_0)(|u|²+|v|²)+2 Re(E_1 u conjugate(v))
      = (1−r²)/D · (|u+rv|²+|ru+zv|²).

The two squares vanish together only when u=v=0, since |z|=1>r². Thus each
unitary fibre is positive definite. Absolute convergence permits termwise Fourier
integration. The j-th coefficient of E_e(exp(2πiθ)) is r^{|e+2j|}. Choosing
e=k mod 2 and j=⌊k/2⌋ recovers every k≥0 from only the two fibres e=0,1.
Multiplying by q^s/(q^{2s}−1), with r=q^{−s}, recovers `treeGreen q s k`.
At q=p,s=½ the existing local normalization gives the actual Weil prime kernel.

The survivor is a family of positive line-bundle fibres retaining the ladder
through its Fourier label. It does not construct the global adelic carrier or
supply positivity of Weil’s full form.
