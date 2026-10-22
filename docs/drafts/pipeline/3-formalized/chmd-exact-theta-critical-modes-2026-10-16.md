# Exact theta critical modes in the full CHMD graph

Status: FORMALIZED. Six leaf builds and final direct Lean audits passed.
Unconditional RH remains open.

## Structural objective

Small real translates of the theta ground source enter the complete, literal
prime--archimedean Doob graph. Their mixed polarization against compact tests
depends on two hyperbolic moments. Pole-annihilated translates yield a countably
infinite independent family of primitive vectors in the exact full-domain radical.
The whole radical admits a canonical removal preserving signed pairings.
This is an actual domain and critical-mode theorem, not an RH receiver or a bound.

## Paper proof

Write Phi for the positive even Riemann kernel, mu = Phi cosh(x/2) dx, and
B(p,q) = <edge p,edge q> - <source p,source q>.

1. The full theta envelopes show Phi(x-a)^2 cosh(x/2)/Phi(x) is integrable
   whenever 2 exp(-2|a|)>1. The uncancelled cusp exponent is strictly negative.
2. Translate the existing compact theta cutoffs. Their signed energy, and the
   signed energy of every difference of two approximants, equal the corresponding
   unshifted energies exactly. Weighted source convergence plus the identity
   ||p||graph^2 = E(p)+2||source p||^2 makes these approximants graph-Cauchy.
3. Translation invariance of compact mixed polarization and convergence of the
   unshifted cutoff to the ground give
   B(T_a,q) = -cosh(a/2) C(q) + sinh(a/2) S(q),
   where C(q)=integral Phi q cosh(x/2), S(q)=integral Phi q sinh(x/2).
   Both functionals are continuous in the actual source norm. Core density
   extends the identity to every graph vector.
4. Therefore T_a+T_-a-2cosh(a/2)T_0 belongs to the signed radical and is
   primitive. Its source is a literal nonzero finite theta-translation filter.
5. Choose a_n = radius/(n+1), with radius = log(4/3)/2. As x tends to infinity,
   the polar source at a_n divided by Phi(x-a_n) tends to one. For j>n the
   corresponding quotient for a_j tends to zero, by full-theta cusp separation.
   In any finite relation the least occupied index therefore has zero
   coefficient, a contradiction. Transfer this literal-function independence
   through source L2 representatives to the actual graph vectors.
6. The entire signed radical is closed. Its graph-orthogonal projection also
   splits the source and edge inner products separately, since graph inner
   product against a radical vector equals twice its source inner product.
   Subtracting this projection preserves every signed mixed pairing and the
   hyperbolic primitive condition, while removing the full critical band. The
   resulting form on its complement is nondegenerate: any further radical vector
   would belong to both the full radical and its orthogonal complement.

## Scope and safeguards

No RH, zero-location, positivity, spectral-gap, or omitted-prime premise.
No claim that zero signed energy alone implies membership in the radical.
No inference from a formal Fourier multiplier to graph membership.

## Validation

- Six leaves built with `lake --old build <leaf>`:
  CHMDThetaTranslateMass, CHMDSignedGraphPolarization, CHMDThetaTranslateGraph,
  CHMDThetaCriticalModes, CHMDInfiniteCriticalModes, CHMDCriticalBandReduction.
- Final `lake env lean <leaf>` audit of every leaf: exit 0, empty diagnostic logs.
- All 92 declarations audited with `#print axioms` in `/tmp`: only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 76 explicit `have := @Name` API probes passed with explicit universe levels.
- Each leaf imported exactly once by `formal/GaloisForLFunctions/RHTower.lean`;
  audited source hashes unchanged; whitespace checks passed.
- `scripts/formal_tools.py index`: exit 0, 14 changed files, 0 removed.
- Global `scripts/formal_tools.py lint`: exit 1 solely for six other untracked,
  unwired leaves: RHTower/Deninger/DeningerHasseHilbertShift,
  RHTower/Deninger/DeningerHasseResolventTriangular, RHTower/Deninger/DeningerMeyerClosedHasseGenerator,
  RHTower/Deninger/DeningerMeyerFredholmXi, RHTower/Deninger/DeningerMeyerHasseResolvent,
  HTGeometry/GradedTriangularRegularizedDeterminant. No lint error names this
  contribution. Concurrent leaves were left untouched.
- All 31 owned scratch artifacts removed; absence verified. All owned processes
  terminal. RH goal remains active.

## Exact formal outputs

- `CHMDThetaTranslate.exists_infinite_exact_primitive_critical`: an independent
  sequence in the actual compact core, primitive in the original theta--cosh
  mass, with full edge pairing equal to source pairing against every graph test.
- `CHMDDoobGraph.criticalBandSequence_linearIndependent`: an independent sequence
  in the closed full signed radical itself.
- `CHMDDoobGraph.exact_critical_band_decomposition`: source and edge orthogonality,
  preservation of signed energy, and preservation of the primitive moment.
- `CHMDDoobGraph.sourcePair_reduced` preserves every mixed signed pairing;
  `CHMDDoobGraph.reduced_nondegenerate` removes all remaining signed radical from
  the complement.

## Remaining frontier

Primitive sign on the complement of the exact critical band remains open.
Infinite critical multiplicity must be removed before a compact spectral
argument could apply. No compactness or sign assertion for that complement is
made here.
