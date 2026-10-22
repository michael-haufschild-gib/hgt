# Coefficient-faithful exterior source contour

## Conjecture loop

### C1 — raw Deninger translation clocks

Right translation gives the exact multiplier `exp(a rho)`.  **Failed:** after centering, an
off-pair mode has modulus `exp(a (beta_i + beta_j - 1))`; Cesaro averaging can diverge before the
reflection selector acts.

### C2 — insert bounded source clocks directly in the Guinand--Weil contour

The two Burnol ordinate clocks and the Ward/Cayley horizontal clock are unit-valued and
source-native.  **Failed as a literal analytic weight:** the Ward normalization depends on the
transverse real coordinate and cannot be a nonconstant holomorphic unit-modulus function on the
strip.

### C3 — finite coefficient-faithful analytic lift

On every finite Xi rectangle, lift the complete nonholomorphic clocked moment data by the existing
finite-divisor Lagrange gauge theorem, then apply exact Guinand--Weil rectangle extraction.  This
preserves every coefficient at every distinct zero and lets analytic multiplicity reproduce all
zero copies.  Four lifted moment contours therefore equal the full oriented exterior determinant
before Cesaro scalarization.

## Deliverable

Formalize C3 unconditionally in
`HedenmalmCoefficientFaithfulExteriorSourceContour.lean`, including:

- arbitrary finite coefficient interpolation and normalized continued-source contour identity;
- centered versions of both Burnol clocks, the fixed-prime Ward clock, Abel--Green row, and both
  adjacent critical features;
- exact equality between the four-contour source determinant and the multiplicity-copy exterior
  determinant for every admissible rectangle and every clock depth triple.

## Remaining hard core

Interpolation alone gives no uniform contour norm.  More sharply, the resulting countable
fixed-prime, rational-rectangle subquantum condition is now proved equivalent to RH.  It is an
exact endpoint, not an independent producer.  Any surviving conjecture must therefore use
arithmetic cancellation before the positive packet landing; a generic contour-norm estimate is
merely RH in source notation.

## Closure update — 2026-08-14

The module now continues through the complete source Cesaro landing:

- four contours equal the multiplicity-copy determinant;
- the copy determinant equals the existing support-indexed source-native determinant;
- one orientation converges to half its fixed-center positive packet energy;
- two full-rectangle orientations converge to their complete positive landing, without reporter
  block restriction.

Direct Lean check passes. Key declarations audit to `[propext, Classical.choice, Quot.sound]`.
Umbrella import is present. `HedenmalmExteriorSourceThetaBoundaryGap.lean` proves that any
nonneutral theta Green boundary fibre forces this literal source-contour landing above
`4*(96/145)^2`. Thus remaining issue is not source expression or interpolation existence; it is
same-fibre rank-two boundary neutralization / an equivalent strict subquantum source estimate.

The endpoint is exact in both directions:

```text
XiPrimeWardExteriorCoefficientFaithfulSourceSubquantum ↔ RiemannHypothesis.
```

The forward implication places any hypothetical off-line divisor in an admissible rational
symmetric rectangle, retains its analytic multiplicity and both exterior orientations, and
contradicts the one-copy quantum.  The reverse implication proves every fixed-center packet energy
zero under RH and hence supplies the strict bound with limit zero.  This classification prevents a
false pivot: proving the displayed source estimate by compactness, interpolation, or a generic
contour norm would already contain the whole RH argument.

## Heavy-conjecture failure ledger after C3

### C4 — holomorphic cross-ratio dephasing

Express the Ward coordinate through ratios of the two holomorphic reflection-orientation values.
**Failed:** unit dephasing needs a divisor-pair-dependent denominator.  Homogeneous normalization
either becomes nonholomorphic or collapses the spectral label; the shared-reservoir no-go applies.

### C5 — all-order reciprocal-trace ladder

Use enough reciprocal powers to cover every residual annulus left by the finite curvature bands.
**Failed atomwise:** reciprocal powers of an off-line complex atom rotate, so no universal
all-order positivity survives.  Existing orders through 19 are positive on their bands; orders
20/21 and 32 still leave RH-equivalent residual annuli.

### C6 — normalized Cassini reflection divided difference

Remove the transverse zero from the reflection difference before taking its source trace.
**Already classified:** `HedenmalmWardGreenRemovableExtensionKernelProjection.lean` proves the
totalized Green quantity equals its removable source extension minus one positive critical-line
spectral projector.  The missing term is exactly the obstruction, not a removable singularity.

### C7 — pay that projector from the unconditional critical-line density reservoir

Combine the previous identity with the external rank--trace theorem placing more than two thirds
of zeros on the line.  **Failed:** density cannot exclude a fixed reflected off-line pair.  A
synthetic amplification does not create Xi divisor multiplicity, while a genuine recurrence that
does so is already RH-equivalent; `MeasuredIndexBlindness.lean` formalizes this blindness.

### C8 — pinched critical-line contour

Recover the missing projector by shrinking a source contour onto the critical line.  **Failed:**
the pinched contour computes the same projector after choosing a zero-avoiding strip but supplies no
new sign or ceiling.  It is a restatement of the C6 fracture.

### C9 — Poincare--Lelong/Jensen source domination

Dominate the Ward--Green charge by an ordinary logarithmic source measure.  **Failed sharply:**
the Jensen weight vanishes at the critical line whereas the normalized Green charge retains a
quantum; singular totalization adds exactly the C6 projector.  The corpus Hardy--Green metric
no-go already rules out the required domination.

### C10 — external on-line divided-vector reservoir

Use the many critical-line completed-source divided vectors to cancel their common source and leave
an approximate nonreal eigenvector.  **Failed:** the theta source orbit is cyclic, so quotienting
out the common source kills the whole carrier; zero density gives no graph-norm interpolation.
The completed-source resolvent corpus identifies the residual positive radial source work and
proves that its vanishing is RH-equivalent.

### C11 — Schwarz-odd contact cancellation pays the Ward projector

Splice the exact damped-sine contact law `C_y'(0)=0` into the removable Ward--Green extension.
**Failed by carrier mismatch:** contact flatness removes one local boundary evaluation, whereas the
Ward fracture subtracts the full critical-line spectral projector.  The corpus supplies no
identity between those objects; asserting one would discard the labelled critical spectrum.

### C12 — exterior determinant removes the divergent Gamma/polar channel

Use the determinant before the real-part absorption whose scalar source majorant diverges.
**Failed under the exact rank test:** a determinant cancels an additive local channel only when its
four weighted values form a rank-one matrix.  The four independent Lagrange-weighted Gamma/polar
contours have no such factorization and can have full rank.  Exteriorization therefore does not
automatically pay the local channel identified by
`XiWardInteriorSourceBudgetDivergence.lean`.

### C13 — phase-replicated moment-neutral index amplification

Twist coefficient-faithful replicas by roots of unity so prime traces cancel while exterior index
adds.  **Already killed by the exact corpus handoff:** complex twists break the Hermitian input of
the rank--trace inequality; Hermitian shared-reservoir replicas retain coefficients and arbitrarily
small Frobenius cost, but simultaneous reflection restores linear positive-index cost.  This is
the formal/paper wall in `SourceHorizontalMomentNeutralAmplification.lean` and
`source-horizontal-shared-reservoir-polarization.md`.

## Validation

```text
lake env lean GaloisForLFunctions/RHTower/HedenmalmCoefficientFaithfulExteriorSourceContour.lean
lake build GaloisForLFunctions.RHTower.HedenmalmCoefficientFaithfulExteriorSourceContour
```

Both passed.  A scratch `#print axioms` audit of the zero-sum identity, determinant identity,
Cesaro landing, RH implication, and final equivalence reports only
`[propext, Classical.choice, Quot.sound]`.  Targeted forbidden-declaration scan is clean.
