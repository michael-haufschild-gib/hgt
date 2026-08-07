# Mass-Xi critical Volterra-adjoint transference

- **ID:** `mass-xi-critical-volterra-adjoint-transference`
- **Stage:** 1 — in progress
- **Route:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3
- **Primary claim:** `[CONJECTURE] [NOVELTY UNVERIFIED]`
- **RH used:** no
- **Computation used:** no

## Exact frontier

`RHTower.XiMassCriticalErrorFlux` proves unconditionally, for `a>1/2` and `sigma>0`,

```text
Prime_a,sigma,u(H) -> 2 pi g_a,sigma,u(-i/2)
  + integral_(0,infinity) Ecrit(h) F'_a,sigma,u(h) dh.
```

Polar term has norm independent of `u`; terminal completed-error flux vanishes. Remaining
RH-equivalent source problem is uniform boundedness in `u` of canonical infinite current.

New-corpus audit:

- `HedenmalmThetaTraceKernel.thetaTraceSq_eq_source_variance` is exact positive trace calibration,
  but no theorem maps `Ecrit` or mass orbit into its source inverse.
- `HermiteL2ClosedSpan` now gives exact positive/negative even Fourier-sector decomposition, but
  no theorem makes normalized Chebyshev error an `L2` vector or bounded functional there.
- Suzuki Gamma-wall block Hardy transfer and weighted-tail coercivity convert a *realized literal
  trace-zero carrier* into weighted `H1`; their cards retain literal source realization as open.
- prime-normal flow resolves bounded self-adjoint prime breadth, but its Gamma/Feshbach source
  coupling remains open.
- translated-window sieve and Halasz estimates control finite Dirichlet polynomials in mean square;
  they do not give a pointwise cofinal completed-error current bound.

External primary audit found Hedenmalm's 2026 theta differential-pair spectral realization and
Suzuki's 2022--2026 screw/Weil operator constructions. Their stated results provide spectral
realizations or RH criteria, not a source-side uniform bound for this mass current.

## Hostile conjecture loop

### C41-A — Hedenmalm variance directly controls the mass current

`[CIRCULAR]`. The trace variance is a fixed scalar. A bound for the mass current requires an
additional source map whose boundedness on completed zeta modes is exactly the missing provider.
No current theorem supplies it.

**Failure constraint:** next conjecture must construct an exact source map before using positivity.

### C41-B — Hermite-sector completeness turns the current into a uniform `L2` pairing

`[INSIGNIFICANT / INAPPLICABLE]`. Plancherel makes the mass orbit's unweighted `L2` norm independent
of `u`, but the corpus does not place the critical normalized Chebyshev error in the dual `L2`
space. Exponential weighting recovers integrability only by moving to a shifted line whose mass
orbit has the already-classified `exp(lambda |u|)` corona growth.

**Failure constraint:** next conjecture must retain causal completion and cannot replace source
cancellation by absolute `L2` magnitude.

### C41-C — Apply Suzuki weighted-tail coercivity directly to `Ecrit`

`[CIRCULAR]`. Suzuki theorem assumes literal cutoff equation for a realized physical carrier.
Identifying `Ecrit` with such a carrier is absent and is source-bearing, not formal bookkeeping.

**Failure constraint:** determine exact differential expression selected by causal completion
before seeking an intertwiner.

## Positive survivor: critical Volterra-adjoint law

Put

```text
e(h) = criticalMellinNormalizedChebyshevError(h),
E(h) = criticalMellinCompletedError(h),
D_1/2 F(h) = (1/2)F(h) - F'(h).
```

Corpus identity on `h>=0` is

```text
E(h)=1-2 exp(-h/2)-e(h)-(1/2) integral_0^h e(s) ds.       (1)
```

For `H>=0`, every differentiable `F` with the displayed finite integrals satisfies

```text
integral_0^H E(h)F'(h) dh
 = F(0) - integral_0^H exp(-h/2)F(h) dh
   + integral_0^H e(h) D_1/2 F(h) dh
   + (E(H)+e(H))F(H).                                    (2)
```

`[PAPER-PROVED]`. Proof: expand `(1)`. Fundamental theorem gives
`integral F'=F(H)-F(0)`. Integration by parts gives

```text
-2 integral exp(-h/2)F'
=-2 exp(-H/2)F(H)+2F(0)-integral exp(-h/2)F.
```

Fubini on `0<=s<=h<=H` gives

```text
integral_0^H F'(h)(integral_0^h e(s)ds)dh
=F(H)integral_0^H e(s)ds-integral_0^H e(s)F(s)ds.
```

Collect terms and use `(1)` at `H`; this is `(2)`.

For actual mass profile, existing deep-shift bounds and the elementary local Chebyshev bound imply
`e(H)F(H)->0`; existing theorem already gives `E(H)F(H)->0`. Therefore

```text
xiMassCompletedErrorFlux(a,sigma,u)
 = F(0) - integral_0^infinity exp(-h/2)F(h)dh
   + integral_0^infinity e(h) D_1/2 F(h)dh.              (3)
```

This is not the RH proof. It removes the causal primitive from the open current. The exact
source-bearing object is normalized Chebyshev error acting on the critical outgoing derivative.

## Frozen primary conjecture

`[CONJECTURE] CRITICAL_OUTGOING_SOURCE_TRANSFERENCE`

There is a source-defined intertwiner from the completed Suzuki/Hedenmalm physical carrier to the
half-line Chebyshev distribution such that its boundary functional is

```text
Phi -> integral_0^infinity e(h) ((1/2)Phi(h)-Phi'(h)) dh,
```

and the intertwiner is bounded on the complete mass half-wave orbit for every fixed `a>1/2` and
`sigma>0`.

Risky consequence: together with `(3)`, boundedness forces the §9.3 fixed-line prime source bound
and hence RH. Falsifier: any exact source realization whose outgoing boundary norm necessarily has
the mass-independent `exp(|u|/2)` radiation corona cannot provide this intertwiner.

## Open core

`[OPEN CORE]` Construct or rule out the literal source-defined intertwiner. A theorem merely
assuming boundedness of the displayed Chebyshev functional is rejected as the original open core.

## Gates

- [x] audit newest HTGeometry/RHTower theorem surfaces
- [x] repeat internal and external audit for exact connector
- [x] kill direct variance, bare `L2`, and assumption-only Gamma routes
- [x] dependency-close finite Volterra-adjoint identity on paper
- [ ] formalize `(2)` and actual-mass infinite law `(3)` unconditionally
- [ ] hostile-audit and construct the literal source intertwiner
- [ ] prove uniform current bound and RH
