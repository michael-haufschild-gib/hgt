# Xi squared-Euler aperture Hilbert correlation

- **ID:** `xi-squared-euler-aperture-hilbert-correlation`
- **Stage:** `1-in-progress`
- **Type:** `[THEOREM ON PAPER] [LEAN-PROVED RIGHT-EDGE CRITERION]`
- **Scientific status:** `[CORPUS-NEW EXACT DECOMPOSITION]`
  `[CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/XiSquaredEulerApertureHilbertCorrelation.lean`,
  `formal/GaloisForLFunctions/RHTower/XiSquaredEulerAllDegreeChargeCriterion.lean`

## Problem

The physical-cutoff Jordan-mass route failed because the low/high split is a splice gauge.  After
the forced join, the actual open problem is whether completed response correlation cancels the
transverse signed charge.  The squared-Euler response proves that one- and two-node detectors are
positive and that a single transverse orbit first becomes negative at three nodes, but it did not
identify the positive cross-orbit object competing with that charge.

This card creates that object.  It is not a generic Hilbert space attached after the fact.  It is
forced by the actual reciprocal-square Xi response coefficients.

## All-degree oriented square law

Let

```text
lambda_q = xiZeroCopyReciprocalSquare(q) = a_q + i b_q,
w_q      = p(lambda_q) = u_q + i v_q,
```

for a real polynomial `p`.  The source-derived Xi chamber gives `a_q>0` unconditionally.  Direct
completion of the square gives

```text
Re(lambda_q w_q^2)
 = a_q (u_q-(b_q/a_q)v_q)^2
   - ((a_q^2+b_q^2)/a_q) v_q^2.                         (AH1)
```

Both terms on the right are nonnegative before subtraction.  Thus the complete trace-Hankel form
has one canonical positive channel and one canonical transverse channel:

```text
H_p = ||U_p||^2 - ||V_p||^2,                             (AH2)

U_p(q)=sqrt(a_q) (Re p(lambda_q)-(b_q/a_q) Im p(lambda_q)),
V_p(q)=sqrt(|lambda_q|^2/a_q) Im p(lambda_q).
```

The missing RH estimate is exactly contractivity of `p -> V_p` against `p -> U_p` on the
source-selected real-polynomial evaluation space.  This is the reciprocal-square spectral version
of the circle-state cosine/sine orientation inequality already isolated on paper, but `(AH1)` is
pointwise, exposes the transverse density explicitly, and connects directly to the squared-Euler
response chamber and HTGeometry reciprocal-square defect law.

## First-minor response-correlation law

Define, orbitwise,

```text
a_q   = Re lambda_q,
tau_q = Re(lambda_q^2)/a_q,
chi_q = b_q^2 |lambda_q|^2/a_q.
```

The first three real central coefficients obey

```text
Re(lambda_q^2) = a_q tau_q,
Re(lambda_q^3) = a_q tau_q^2-chi_q.                     (AH3)
```

For a finite multiplicity-exact packet `S`, put

```text
A = sum_S a_q,
B = sum_S Re(lambda_q^2),
C = sum_S Re(lambda_q^3),

G_S = A sum_S a_q tau_q^2-(sum_S a_q tau_q)^2,
J_S = A sum_S chi_q.
```

Then

```text
A C-B^2 = G_S-J_S.                                      (AH4)
```

The positive term is an actual Hilbert Gram determinant.  The existing weighted bilinear
variance identity gives the exact metric realization

```text
2 G_S = sum_(q,r in S) a_q a_r (tau_q-tau_r)^2 >= 0.    (AH5)
```

Consequently

```text
A C-B^2 >= 0  iff  J_S <= G_S.                          (AH6)
```

This is the requested response-correlation cancellation statement: the correlation is not an
unoriented slogan but the weighted Hilbert dispersion of the central orbit slopes; the Jordan
mass is not either physical-cutoff half but the invariant transverse density `chi_q`.

## Atomic sharpness and critical radical

For one orbit,

```text
a_q Re(lambda_q^3)-Re(lambda_q^2)^2
  = -b_q^2 |lambda_q|^2.                                (AH7)
```

Thus every off-critical orbit has negative first minor.  Cross-orbit slope dispersion is the only
possible cancellation mechanism.  Moreover

```text
chi_q=0  iff  b_q=0  iff  Re(rho_q)=1/2.                 (AH8)
```

For every nonempty finite packet, `J_S=0` exactly when all its orbits lie on the critical line.
This makes the charge radical exact, not merely bounded.

In the earlier `(t,c)` orbit coordinates,

```text
a=t/(t^2+c),
tau=(t^2-c)/(t(t^2+c)),
chi=c/(t(t^2+c)^2),
```

and `(AH7)` becomes `-c/(t^2+c)^3`, the confluent form of the already-formalized negative
three-node transverse determinant.

## Hostile novelty audit

1. Completing one complex square and the weighted variance identity are standard parent algebra.
2. The existing circle-state paper route already writes the full Hankel value as a cosine norm
   minus a sine norm.  This card does not claim discovery of indefinite Hilbert polarization.
3. The corpus-new content is the exact source-specific identification of the positive response
   metric `G_S`, the invariant transverse density `chi_q`, their cancellation identity `(AH4)`,
   and the all-degree pointwise shear `(AH1)` joining the Xi reciprocal-square chamber to that
   response metric.
4. `(AH6)` does not prove its right-hand inequality for the complete Xi divisor.  Calling the
   decomposition an RH proof would be false.

## Exact right-edge closure

The complete two-channel sums in `(AH9)` are well-defined without RH.  The already-proved Xi
reciprocal-square sector estimate gives

```text
b_q^2 <= a_q^2/84,
(a_q^2+b_q^2)/a_q <= (85/84) a_q.                       (AH7)
```

The reciprocal-square spectrum is bounded, so for each fixed real polynomial `p` there is a
finite `C_p` with `|p(lambda_q)|<=C_p`.  Therefore the transverse term is bounded by
`(85/84) C_p^2 a_q`.  Since `sum_q lambda_q` is absolutely convergent, `sum_q a_q` converges and
the complete transverse channel is summable.  The raw Hankel term is bounded in absolute value by
`C_p^2 |lambda_q|`, hence is summable as well.  Equation `(AH1)` then makes the Hilbert channel
summable.

Grouping the multiplicity copies over each distinct Xi divisor point gives exactly

```text
sum_q Re(lambda_q p(lambda_q)^2)
  = Re(xiCentralTraceHankel(p))
  = HilbertEnergy(p) - TransverseEnergy(p).              (AH8)
```

Consequently

```text
(AH9) for every p in R[X]
  <-> XiCentralTraceHankelNonnegative
  <-> RH.                                                 (AH9-RH)
```

Coefficient density sharpens the producer interface: it is enough to prove `(AH9)` for the
countable family `p in Z[X]`.  Lean names this exact remaining condition
`XiSquaredEulerApertureIntChargeDominated` and proves
`xiSquaredEulerApertureIntChargeDominated_iff_riemannHypothesis`.  The explicit downstream
connector is
`xiWeilPolarization_nonneg_of_xiSquaredEulerApertureIntChargeDominated`; hence the formal chain is

```text
integer-polynomial charge domination
  -> complete square-summable Xi Weil positivity
  -> RH.
```

The zero-data-elimination identity now closes the source connector directly, without using RH as
an intermediate implication:

```text
PrimeArchSourceTraceHankelIntNonnegative
  <-> XiSquaredEulerApertureIntChargeDominated
  -> complete square-summable Xi Weil positivity
  -> RH.                                                   (AH10)
```

Lean theorem
`xiSquaredEulerApertureIntChargeDominated_iff_primeArchSourceTraceHankelIntNonnegative`
proves `(AH10)` from `(AH8)` and
`xiCentralTraceHankel_eq_primeArchSourceTraceHankel`.  Therefore existing coherent producers—one
positive moment representation, finite-KMS local closure, a positive Sonin aperture barycenter,
or coupled-Sonin finite-Gram closure—now discharge `(AH9)` through their already-formalized source
Hankel theorems.  Their construction hypotheses remain open; the connector itself is closed.

Hostile audit: `(AH9-RH)` is a consumer theorem, not a proof of its left side.  It closes the
previously unstated infinite-summability and multiplicity-grouping obligations and shows that no
additional “three nodes to all degrees” connector remains after `(AH9)` itself.  Any source route
must now construct one of the coherent source producers above or prove the named integer-polynomial
charge inequality directly; merely renaming prime--Gamma Hankel positivity does not do so.

## Surviving open target

The source-side theorem must prove, for every real polynomial in the remaining tail cone,

```text
sum_q ((a_q^2+b_q^2)/a_q) (Im p(lambda_q))^2
 <=
sum_q a_q (Re p(lambda_q)-(b_q/a_q) Im p(lambda_q))^2.  (AH9)
```

At degree one, it is exactly the infinite-divisor limit of `J_S<=G_S`, hence exactly the open
theta-cusp sixth-moment Hankel inequality.  Any proposed producer must therefore create genuine
cross-orbit slope dispersion.  A diagonal bound on `b_q/a_q`, terminal projection, or separate
Jordan estimate cannot close `(AH9)`; real-polynomial interpolation can concentrate on one
transverse atom at high degree.

The next research attack is to transport `(AH9)` to the explicit prime--Gamma circle/Born--Witten
source and determine whether the theta translation structure supplies a contractive intertwiner,
not merely another equivalent positivity statement.

## Gates

- [x] physical-cutoff Jordan gauge rejected
- [x] all-degree oriented Hilbert/charge identity proved on paper
- [x] first-minor Hilbert dispersion minus transverse charge proved on paper
- [x] exact atomic negative charge and critical radical proved on paper
- [x] zero-free prime--Gamma source positivity connected directly to integer charge domination
- [x] direct Lean check of both permanent target modules
- [x] narrow final module build, lint, and axiom audit
- [ ] source proof of `(AH9)` / RH

## Log

- 2026-07-19 — Replaced the vague “response correlation cancels Jordan mass” target by the exact
  Hilbert dispersion/charge law `(AH4)`--`(AH6)` and derived its all-degree oriented-square parent
  `(AH1)`--`(AH2)`.  Permanent Lean source written; verification deferred until the shared foreign
  build load permits one owned foreground check.
- 2026-07-21 — Closed the right-edge consumer.  Proved unconditional summability of both complete
  channels from the `1/84` reciprocal-square sector, grouped multiplicity copies back to the Xi
  trace-Hankel form, and formalized real- and integer-polynomial `(AH9) <-> RH` criteria in
  `XiSquaredEulerAllDegreeChargeCriterion.lean`.  Direct `lake env lean` check passed.  Remaining
  open theorem is exactly `XiSquaredEulerApertureIntChargeDominated`, not an unspecified
  all-degree lift.
- 2026-07-21 — Final audit: exact module build completed at `9077/9077`; formal lint passed; five
  right-edge capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-21 — Closed the direct source-discharge edge.  Integer squared-Euler charge domination
  is exactly the zero-free normalized prime--Gamma source Hankel condition by two existing value
  identities, with no RH detour.  This wires every coherent source producer already in the corpus
  into complete Weil positivity; constructing such a producer remains RH-hard.
- 2026-07-21 — Proved the sharp orbit-diagonal obstruction in Lean.  At every off-critical atom,
  one degree-at-most-one real polynomial has zero sheared Hilbert response and strictly positive
  transverse charge.  Therefore no finite termwise comparison constant exists at that atom;
  allowing a separate arbitrary constant for every atom is already equivalent to RH.  Any viable
  all-degree source/response intertwiner must mix distinct atoms globally.  Formal module:
  `XiSquaredEulerApertureDiagonalControlObstruction.lean`.
