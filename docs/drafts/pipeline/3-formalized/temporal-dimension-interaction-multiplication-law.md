# Temporal-dimension interaction multiplication law

Status: **formalized**

Formal source:
`formal/GaloisForLFunctions/HTGeometry/TemporalDimensionInteractionMultiplicationLaw.lean`

## Theorem

For every pair of nonempty finite spectra with dimensions
\[
  d_A=m+1,\qquad d_B=n+1,
\]
define projective temporal dimension as the rational rank of the energy
gaps relative to one level.

The uncoupled tensor-sum spectrum obeys
\[
  \tau(H_A\otimes I+I\otimes H_B)\le m+n.
\]

For every \(\delta>0\), there exists a joint diagonal Hermitian
perturbation of operator norm at most \(\delta\) whose coupled spectrum has
maximal projective temporal dimension
\[
  \tau(H_{\rm coupled})
  =mn+m+n
  =d_A d_B-1.
\]
Consequently,
\[
  \tau(H_{\rm coupled})-\tau(H_{\rm uncoupled})
  \ge mn=(d_A-1)(d_B-1).
\]

The same witness satisfies, for every observable \(O\) and real time \(t\),
\[
  \|\tau_t^{H_{\rm coupled}}(O)
      -\tau_t^{H_{\rm uncoupled}}(O)\|
  \le 2|t|\delta\|O\|,
\]
and every positive full-support fidelity replica collision mass equals its
permutation floor at every order.

No genericity hypothesis is imposed on either input spectrum.

## Interpretation boundary

This is an exact theorem for every finite pair. The perturbation is a
legitimate joint interaction diagonal in the uncoupled product eigenbasis.
It is not yet proved to be geometrically local inside the two factors.

For a finite Type-I model containing \(D\) horizon microstates and a
two-state probe, the theorem gives a possible gain of at least \(D-1\)
recurrence directions. Any replacement \(D\sim e^S\) is a separate model
input; the theorem does not establish finite-dimensional black-hole or de
Sitter microscopic dynamics.

## Verification

Target source compilation:

```text
lake env lean GaloisForLFunctions/HTGeometry/TemporalDimensionInteractionMultiplicationLaw.lean
```

passes.

Axiom audit of the six load-bearing declarations reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque` or `unsafe` declaration is
used.
