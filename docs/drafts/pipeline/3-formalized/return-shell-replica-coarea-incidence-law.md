# Return-shell replica coarea incidence law

- **ID:** `return-shell-replica-coarea-incidence-law`
- **Stage:** 3 — formalized
- **Type:** theorem / failure-driven frontier advance
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [AXIOM-AUDIT PENDING] [APPLICATION NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/oriented-no-shortcut-without-return-law.md`
- **Date:** 2026-08-07

## Public sentence

Removing an approximate return does not merely identify a longitudinal branch: every fraction of
target norm erased by that removal is amplified to replica power before the complete shortcut
union is integrated.

## Open core attacked

The replica--Hilbert incidence law bounds complete target capture by one projection moment and
retains source fibre multiplicity, occupied endpoint image, duplicate invariance, and exact-return
zero invariance.  Its unit-ball step nevertheless discarded quantitative information exposed by
return removal.  A target residual with squared norm `rho < 1` was treated identically to a fully
transverse unit target.

The missing bound had to satisfy four constraints simultaneously:

1. integrate on quenched source space, so every endpoint fibre sheet remains counted;
2. depend on occupied target image rather than number of circuit descriptions;
3. erase exact returns and discount approximate returns;
4. retain growing-replica strength before any complete-union estimate.

## Conjecturing protocol

### C0 — raw coarea density

**Verdict:** `[REDISCOVERED / CIRCULAR]`.

The coarea formula writes endpoint probability as the integral of Gaussian density divided by
Jacobian over every fibre sheet.  It preserves multiplicity but supplies no upper bound.

### C1 — unweighted replica target span

**Verdict:** `[PROVED EARLIER / INCOMPLETE AFTER APPROXIMATE RETURN REMOVAL]`.

For `S_r = span{z^(tensor r)}`, capture implies

```text
a^r <= ||Proj_(S_r) psi^(tensor r)||^2.
```

This is duplicate invariant and exact-return zeros add no direction, but its proof replaced
`||z^(tensor r)||^2` by one.  Approximate longitudinal erasure was lost.

### C2 — one residual radius for the complete target family

**Verdict:** `[SURVIVES BUT TOO LOSSY]`.

Using `sup_z ||z||^2` retains a replica power, but one fully transverse target forces the supremum
back to one and erases all information from every nearly longitudinal target.

### C3 — return-shell occupied-image reporter

**Verdict:** `[PAPER-PROVED] [LEAN-PROVED]`.

Partition the return-removed occupied target image into finitely many squared-radius shells.  Take
the Veronese span only after this partition, then weight each shell projector by its radius to
replica power.  This retains approximate-return attenuation without reverting to target labels.

## Exact universal law

Let `B` be finite.  For every shell `b`, let `Z_b` be an arbitrary target family in a finite
complex Hilbert space, and suppose

```text
||z||^2 <= rho_b,       rho_b >= 0,       z in Z_b.
```

At replica order `r >= 1`, put

```text
S_(b,r) = span_C { z^(tensor r) : z in Z_b },
q_(b,r)(x) = ||Proj_(S_(b,r)) psi(x)^(tensor r)||^2,
Q_r(x) = sum_b rho_b^r q_(b,r)(x).
```

For threshold `a > 0`, define complete capture

```text
E_a = {x : exists b, exists z in Z_b, |<psi(x),z>|^2 >= a}.
```

Then, pointwise and for every finite source measure `mu`,

```text
1_(E_a)(x) a^r <= Q_r(x),

mu(E_a) <= a^(-r) integral Q_r(x) dmu(x).              (RSCI)
```

No measurability or selector assumption is used in the pointwise inclusion.  The integrated form
uses only integrability of `Q_r`.  It is quenched: integration remains over original source points,
not distinct endpoints, so all fibre-sheet multiplicity survives.

Within each shell, `S_(b,r)` depends only on occupied target vectors.  Duplicate labels change
nothing.  At positive replica order, adjoining zero to every shell changes neither `S_(b,r)` nor
`Q_r`; exact returns therefore cost zero.

## Static-Choi return identity

For normalized static-Choi target `phi` and normalized orbit anchor `Phi_H(u)`, write

```text
alpha = <Phi_H(u), phi>,
phi_perp = phi - alpha Phi_H(u).
```

The lag-resolved split is orthogonal, hence

```text
||phi_perp||^2 = 1 - |alpha|^2.                        (ANCHOR)
```

Therefore shell radii may be chosen directly from the amount of anchor fidelity removed.  Feeding
`(ANCHOR)` into `(RSCI)` yields the static-Choi capstone: each residual shell contributes

```text
(1 - anchor-fidelity upper/lower information)^r
    * occupied-shell replica projection mass,
```

with the exact inequality direction encoded as an upper bound on residual squared radius.

## Dependency-closed proof

Fix one captured target `z in Z_b`.  Set `u = psi(x)^(tensor r)`,
`v = z^(tensor r)`, and let `P_(b,r)` project onto `S_(b,r)`.  Since `v` lies in the target span,

```text
<u,v> = <P_(b,r)u,v>.
```

Cauchy--Schwarz and tensor multiplicativity give

```text
|<psi(x),z>|^(2r)
  <= ||P_(b,r)u||^2 ||v||^2
  = q_(b,r)(x) ||z||^(2r)
  <= q_(b,r)(x) rho_b^r
  <= Q_r(x).
```

Capture and monotonicity of nonnegative powers prove the pointwise law.  One application of
Markov's integral inequality proves `(RSCI)`.  No targetwise probability union appears.

For `(ANCHOR)`, the anchor component and residual are orthogonal.  Pythagoras, target norm one,
and anchor norm one give the identity exactly.

## Why this advances the frontier

Earlier formal laws handled exact return removal as a zero-vector invariance.  The new law handles
the entire approximate longitudinal hierarchy.  It also identifies the correct order of
operations:

```text
return removal -> residual-radius shells -> occupied Veronese spans
               -> replica weighting -> source integration.
```

Taking one global radius before occupied-image compression loses the gain; taking targetwise
moments after integration reintroduces circuit-label entropy.

The remaining ordinary-local-Hamiltonian task is now sharper: bound the finite sum of
radius-weighted occupied-shell projection moments.  Shells close to permitted history already
carry their growing-replica penalty; only genuinely transverse occupied image remains for the
local-ensemble anti-concentration theorem.

## External priority audit

- Negro's coarea distribution theorem (`arXiv:2110.01441`) proves the pushforward density as the
  fibre integral of source density divided by the appropriate Jacobian.  This validates the
  fibre-sheet interpretation but does not provide the return-shell Veronese projection bound.
- Oszmaniec--Kotowski--Horodecki--Hunter-Jones (`arXiv:2205.09734`) prove saturation and recurrence
  for random circuits and stochastic local-Hamiltonian evolution using approximate designs.  They
  explicitly leave autonomous local-Hamiltonian dynamics outside that closure.
- Brown--Freedman--Lin--Susskind (`arXiv:2111.12700`) study long-distance complexity geometry, not
  incidence-normalized fibre mass or return-shell replica projections.
- Al-Ghattas--Gamarnik (`arXiv:2607.14384`) obtain shallow-circuit lower bounds for random quantum
  spin-glass low-energy states via Gaussian processes indexed by circuits.  Their theorem is about
  ground-state energy and does not state the dynamical return-shell incidence law.
- Search of current mathlib and public Lean repositories found no coarea theorem or reusable
  geometric-measure-theory infrastructure.  The present Lean theorem therefore formalizes the
  Hilbert/probability reduction directly; it does not claim formalization of continuous coarea.

**Novelty verdict:** generic ingredients are classical.  The assembled return-shell,
duplicate-invariant, occupied-Veronese, quenched-incidence law was not found in the audited
literature, but priority remains `[APPLICATION NOVELTY UNVERIFIED]` until theorem-level expert
comparison.

## Hostile review

1. This is not yet a Brown--Susskind growth theorem.  It is a strict reduction of its fixed-time
   complete-union core.
2. A shell of radius one receives no return-removal gain.  Its occupied projection moment still
   requires genuine ordinary-local-Hamiltonian anti-concentration.
3. Shell count must remain subexponential at the chosen replica order.  Artificially assigning one
   shell per circuit word would reproduce the forbidden target union.
4. The radius is squared target norm, while lag-resolved capture thresholds in the static-Choi law
   are amplitudes.  Applications must square the residual amplitude threshold before invoking
   `(RSCI)`.
5. Coarea terminology refers to disintegration of the source integral.  Lean currently proves the
   measure bound on source space, not a continuous Hausdorff-fibre formula.
6. Novelty is not established by Lean and is not claimed from Pythagoras, tensor-norm
   multiplicativity, projection, or Markov individually.

## Formal trace

Abstract module:

`formal/GaloisForLFunctions/HTGeometry/ReplicaReturnShellCoareaIncidenceLaw.lean`

- `norm_sq_finitePureTensorPowerEuclidean_eq_pow`
- `finitePureStateFidelity_pow_le_replicaTargetProjectionMass_mul_norm_sq`
- `replicaReturnShellProjectionMass_duplicated`
- `replicaReturnShellProjectionMass_withZero`
- `completePureStateReturnShellCapture_subset_projectionMass`
- `measure_completePureStateReturnShellCapture_le_projectionMoment`

Static-Choi module:

`formal/GaloisForLFunctions/RHTower/StaticChoiReturnShellCoareaIncidenceLaw.lean`

- `norm_sq_staticChoiAnchorResidual_eq_one_sub_norm_sq_component`
- `norm_sq_staticChoiReturnShellResidualTarget_le`
- `measure_completeStaticChoiReturnShellCapture_le_projectionMoment`

Both owning files pass foreground `lake env lean`.  Final module builds, axiom audit, formal lint,
and umbrella audit remain to be recorded below.

## Gates

- [x] Conjecturing loop and falsifiers recorded.
- [x] Dependency-closed paper proof.
- [x] Abstract Lean theorem.
- [x] Static-Choi anchor-residual bridge.
- [x] Duplicate and exact-return-zero invariance.
- [ ] Final module builds.
- [ ] Axiom audit.
- [ ] Formal lint and umbrella reachability.
- [ ] External expert priority audit.

