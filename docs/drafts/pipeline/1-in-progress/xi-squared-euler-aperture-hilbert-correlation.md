# Xi squared-Euler aperture Hilbert correlation

- **ID:** `xi-squared-euler-aperture-hilbert-correlation`
- **Stage:** `1-in-progress`
- **Type:** `[THEOREM ON PAPER] [LEAN TARGET WRITTEN, VERIFICATION OPEN]`
- **Scientific status:** `[CORPUS-NEW EXACT DECOMPOSITION]`
  `[CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/XiSquaredEulerApertureHilbertCorrelation.lean`

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
- [ ] direct Lean check of the permanent target module
- [ ] narrow final module build and axiom audit
- [ ] source proof of `(AH9)` / RH

## Log

- 2026-07-19 — Replaced the vague “response correlation cancels Jordan mass” target by the exact
  Hilbert dispersion/charge law `(AH4)`--`(AH6)` and derived its all-degree oriented-square parent
  `(AH1)`--`(AH2)`.  Permanent Lean source written; verification deferred until the shared foreign
  build load permits one owned foreground check.
