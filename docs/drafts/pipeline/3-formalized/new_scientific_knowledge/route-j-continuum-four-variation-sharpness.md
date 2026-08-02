# Route J: the four-row continuum variation bound is exact

**Status:** `[PAPER+LEAN-PROVED] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

## Frontier advance

The four-row obstruction proves that every nonzero atomless physical source needs at least four
changes in its phase-weighted density `sin(u t)h(t)`. That lower bound is exact. For every
reflected damping `c>0` and carrier frequency `u>0`, there is an explicit nonzero Lebesgue density:

- supported strictly inside one open sine chamber;
- integrable in all four physical value/derivative rows;
- annihilating all four rows exactly;
- having a global four-change sign certificate;
- admitting no three-change sign certificate.

Thus the surviving four-change regular class is nonempty. No theorem using only the four local
rows, integrability, atomlessness, or sign variation can close Route J. Any further exclusion must
use canonical theta/prime--Gamma source provenance or cross-mesh coherence.

This is not a source-faithful RH construction: its spacing and coefficients use the local
parameters `c,u`. It is a sharp falsifier of stronger row-only no-go conjectures.

## Five translated bumps

Fix `c,u>0` and put

```text
L = pi/(6u),             r = exp(cL).                   (1)
```

For `j=0,1,2,3,4`, let

```text
I_j = (L/4+jL, 3L/4+jL],
b_j(t) = 1_(I_j)(t).                                   (2)
```

The five intervals are pairwise disjoint. Their union lies in `(0,5L)`, while

```text
u(5L)=5pi/6<pi.                                         (3)
```

Hence `sin(ut)>0` throughout their support.

Use the reciprocal double-root polynomial

```text
A(X)=(X-r)^2(X-r^(-1))^2
    =a_0+a_1X+a_2X^2+a_3X^3+a_4X^4,                   (4)
```

whose coefficients are

```text
a_0=1,
a_1=-2(r+r^(-1)),
a_2=r^2+r^(-2)+4,
a_3=-2(r+r^(-1)),
a_4=1.                                                  (5)
```

Since `r>0`, their signs alternate

```text
+,-,+,-,+.                                              (6)
```

Define the phase-weighted density

```text
p(t)=sum_(j=0)^4 a_j b_j(t),                            (7)
```

and the actual source

```text
h(t)=p(t)/sin(ut)  when sin(ut)!=0,
h(t)=0              when sin(ut)=0.                    (8)
```

Because of `(3)`, `sin(ut)h(t)=p(t)` everywhere. In particular, `h>0` on `I_0`; it is not zero
almost everywhere and has no carrier-node mass.

## Exact four-row cancellation

Let

```text
V(q)=integral exp(qt)b_0(t) dt,
T(q)=integral t exp(qt)b_0(t) dt.                       (9)
```

Translation invariance gives, for every `j`,

```text
integral exp(qt)b_j(t) dt
  =exp(qjL)V(q),                                        (10)

integral t exp(qt)b_j(t) dt
  =exp(qjL)(T(q)+jL V(q)).                              (11)
```

Therefore

```text
integral exp(qt)p(t) dt
  =V(q)A(exp(qL)),                                      (12)

integral t exp(qt)p(t) dt
  =T(q)A(exp(qL))
   +L V(q) exp(qL)A'(exp(qL)).                          (13)
```

At `q=c`, `exp(qL)=r`; at `q=-c`, it equals `r^(-1)`. Both are double roots of `A`, so `(12)` and
`(13)` vanish at both reflected parameters:

```text
integral exp( ct)p(t) dt = 0,
integral t exp( ct)p(t) dt = 0,
integral exp(-ct)p(t) dt = 0,
integral t exp(-ct)p(t) dt = 0.                        (14)
```

Using `p=sin(ut)h(t)`, these are exactly

```text
integral S_c = integral S_(-c) = 0,
integral R_c = integral R_(-c) = 0.                    (15)
```

All rows are integrable because `h` has compact support away from sine nodes.

## Exactly four changes

The intervals in `(2)` lie successively between the four points

```text
L, 2L, 3L, 4L.                                         (16)
```

The quartic

```text
P_4(t)=(t-L)(t-2L)(t-3L)(t-4L)                         (17)
```

has signs `+,-,+,-,+` on `I_0,...,I_4`, exactly matching `(6)`. Outside their union `p=0`.
Consequently

```text
P_4(t) sin(ut)h(t) >= 0   for every real t.             (18)
```

So the phase-weighted density has at most four alternating changes. It cannot have at most three.
If a cubic sign certificate at `0<a<b<d` existed, the already formalized four-row obstruction
would imply `h=0` almost everywhere. But `h>0` on the positive-length interval `I_0`.
Therefore `(18)` is optimal:

```text
minimum possible phase-weighted variation = four.       (19)
```

## Scientific consequence

The regular and phase-node branches are now separated sharply:

```text
regular row-level source:
  four changes are necessary and sufficient;

full-turn finite source:
  evades the sine rows through carrier-node support.     (20)
```

The generic physical-row problem is therefore finished. The remaining J-SF6 problem is source
provenance, not local solvability:

- Can one fixed divisor-independent theta/prime--Gamma law produce the required translated-bump
  mask or another four-change family across the full Xi mesh?
- If not, can a class-complete source theorem exclude every such coherent regular family?
- Can phase-node/singular or relation-valued carriers satisfy the same provenance and global
  budget gates?

Those are Route J survivors and keep the route open.

## Novelty and theatre audit

- `[LITERATURE]` Compactly supported wavelets with exponential vanishing moments, and filter-symbol
  factorization by exponential cancellation operators, are established technology; see
  M. Cotronei and N. Sissouno, *A note on Hermite multiwavelets with polynomial and exponential
  vanishing moments*, arXiv:1702.01007, and the exponential-spline wavelet literature.
- `[LITERATURE]` General Chebyshev-system sign-change lower bounds are classical.
- `[BRIDGE]` Translation identities `(10)`--`(13)`, reciprocal double-root algebra, and interval
  sign bookkeeping receive no standalone novelty claim.
- `[CORPUS AUDIT]` Internal search found finite full-turn interpolation and the four-row lower
  bound, but no compact atomless source attaining it.
- `[EXTERNAL AUDIT]` Targeted searches found general exponential vanishing-moment wavelets, not
  the reflected Route-J pair `q=±c`, Fourier carrier chamber, exact four-row cancellation, and
  four-change optimality in one theorem.
- `[CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]` Candidate content is the exact weld
  `(1)`--`(19)`: one explicit physical-time Lebesgue source simultaneously attaining the Route-J
  lower variation boundary at both reflected fibres.
- `[THEATRE CHECK]` The source depends on local `c,u`; it is not canonical across the Xi mesh, does
  not encode a source-only divisor selector, and does not close Route J.

## Lean certificate

Formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedContinuumFourVariationEscape.lean
```

Principal declarations:

```text
integral_exp_mul_routeJRectangleBump_shift
integral_t_mul_exp_mul_routeJRectangleBump_shift
routeJReciprocalDoubleRootCoeff_value_at_r
routeJReciprocalDoubleRootCoeff_deriv_at_r
routeJFiveBumpPhaseDensity_four_change_pattern
routeJFiveBumpSourceDensity_four_rows_zero
routeJFiveBumpSourceDensity_no_three_change_pattern
exists_routeJ_nonAtomicContinuum_exactFourChange_survivor
```

The Lean theorem constructs the Lebesgue density, proves interval disjointness and carrier
positivity, derives both translated value and first-moment identities, proves reciprocal
double-root cancellation algebraically, verifies integrability and all four zero rows, proves the
quartic sign certificate pointwise, proves nonvanishing on a positive-measure interval, and invokes
the formal four-row no-go to exclude every cubic certificate. The module is wired into
`GaloisForLFunctions/RHTower.lean`. Direct
`lake env lean GaloisForLFunctions/RHTower/XiCTaylorSignedContinuumFourVariationEscape.lean`
and exact-module
`lake build GaloisForLFunctions.RHTower.XiCTaylorSignedContinuumFourVariationEscape`
both pass. A scratch `#print axioms` audit of all eight principal declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`.
