# SP-E relative-carrier facts

## Dependency-closed source identity

For every integer aperture `M >= 2` and every shift `h > 0`, the partial sums of the literal
completed unit-Riesz shift codiagonal converge to the normalized labelled SP-E transport:

```text
sum_{j < m} completedShiftCodiagonal(M,h,jh)
  -> speCompletedQuantileRieszTransport(M) / (2 M).
```

Formal source: `RHTower/SPEQuantileRieszRelativeCarrier.lean`, theorem
`tendsto_unitRieszCoherentCompletedShiftCodiagonal_eq_speQuantileRieszTransport`.

This combines the existing exact SP-E quantile-cell identity
`speCompletedQuantileRieszTransport(M) / M = criticalMellinChebyshevResolventSource(log M)`
with the existing exact codiagonal boundary reconstruction.  No new estimate, replacement
profile, or unproved arithmetic premise is introduced.

## Consequence for the route

The remaining SP-E bound is equivalently a uniform bound for a **specific infinite signed
accumulation of decaying physical shift codiagonals**, not a bound on a terminal seam or on an
individual cell.  This gives a literal interface to Route P's relative-carrier source while
respecting the established obstruction to a dense closable scalar reader.  It does not supply the
missing oriented phase law needed by Q, and it does not imply RH by itself.

## Negative applicability checks

- Recent fixed-modulus bilinear Kloosterman estimates do not apply to Route E's literal
  inverse-unit Fourier energy: that object is a one-variable Fourier transform summed after taking
  nonnegative squared norms, not a bilinear Kloosterman form.
- The corpus contains no source identity linking `criticalMellinChebyshevResolventSource` to
  `completedPrimeGammaFlux` under the searched transform/bridge mechanisms.  Any SP-E-to-Q
  transfer must construct, rather than assume, an oriented complex source law.

## Cross-route charge identity

For every `M >= 2`, the literal normalization of labelled SP-E transport is exactly the completed
outgoing charge:

```text
speCompletedQuantileRieszTransport(M) / (2 M)
  = unitRieszCoherentCompletedOutgoingCharge(M).
```

At `N + 1`, the literal Suzuki Eulerian discrepancy is therefore exactly negative normalized SP-E
transport plus `suzukiEulerianCompletedOutgoingResidual(N)`.  That residual already has the
unconditional explicit bound `5 + |suzukiEulerianCoherentBoundaryAnchor|`.  Consequently the two
actual signed observables control one another up to that same bounded residual.

Formal source: `RHTower/SPEQuantileRieszSuzukiEulerianBridge.lean`.

**Falsified route-level conjecture:** SP-E and the Suzuki Eulerian discrepancy might have supplied
independent cancellation mechanisms whose estimates could be combined.  The exact charge identity
rules this out: both carry the same unique unbounded arithmetic coordinate.  Their difference is
only the already-controlled polar--lattice residual.  The hard core remains a direct proof that
this common oriented charge is uniformly bounded; combining their separate triangle estimates
cannot advance that core.

## Unconditional causal Laplace bridge

The common source has the unconditional elementary envelope

```text
|criticalMellinChebyshevResolventSource(t)|
  <= (2/3) (log 4 + 5) exp(t/2).
```

It follows directly from `Chebyshev.psi(x) <= (log 4 + 4)x` and exact integration of the literal
causal kernel.  The factor `2/3` is the kernel mass, and is the same pre-prime boundary mass that
appears in the ray/current relation.

Consequently, for every real `r > 1/2`, the exact source identity is unconditional:

```text
((r + 1) * Laplace(source)(r) + 2/3)
  = -(logDeriv zetaResidueUnit(r + 1/2) + 1) / (r + 1/2).
```

Formal source: `RHTower/CCMUnitRieszCausalLaplaceBridge.lean`, theorem
`criticalMellinChebyshevResolventLaplace_eq_logDeriv_on_real`.

## Whole-route meaning

This identifies the shared SP-E/Suzuki object as a **causal current**, not two independent signed
estimators.  Its exponential growth rate is exactly the analytic-continuation width carried by the
route: the elementary rate `1/2` supplies only the already-honest half-plane, while RH requires
rate `0`.  Thus the remaining obstacle is neither normalization nor a missing transform: it is a
source-faithful proof that the common oriented charge loses its elementary `exp(t/2)` growth.
