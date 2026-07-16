# The squarefree Ward current is the reciprocal projective-horizon seam

- **ID:** `projective-reciprocal-horizon-ward-seam`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / GENERAL HT TOPOLOGY TO RHTOWER BRIDGE
- **Scientific status:** `[PROVED HERE] [LEAN CORE] [NOT A NOVELTY CLAIM] [NOT RH]`
- **HT parents:**
  - `../new_scientific_knowledge/projective-horizon-tits-building.md`;
  - `../new_scientific_knowledge/projective-horizon-depth-two-current-algebra-transition.md`;
  - `../../1-in-progress/hypertranscendental-laurent-horizon-residue-field.md`.
- **RH parents:**
  - `../squarefree-fixed-current-right-half-ward-localization.md`;
  - `../squarefree-euler-modular-corona-curvature-colligation.md`.
- **Lean:** `formal/GaloisForLFunctions/RHTower/ProjectiveHorizonWardSeam.lean`.
- **Statement:** The completed squarefree logarithmic Ward current is exactly the logarithmic
  connection on the transition between the two complementary projective derivative horizons of
  the completed squarefree amplitude.  Its strict anti-causal component is therefore the Hardy
  realization of a source-defined HT Cech--Laurent seam.

## Reciprocal-horizon transition

Let `x` be a nonzero differential-generic scalar and put `u=x^(-1)`.  The positive-jet horizons
of `x` and `u` are complementary projective observers.  On the locus where `x'` is nonzero their
first derivative frames obey

```text
u'/x'=-x^(-2).                                            (1)
```

Thus the transition character between the two horizon tangent frames is the reciprocal square

```text
g_x=-x^(-2).                                              (2)
```

Its logarithmic connection is

```text
d log g_x=-2 x'/x.                                       (3)
```

Equivalently, the difference of the two affine two-jet connections is

```text
u''/u'-x''/x'=-2x'/x.                                    (4)
```

Equation `(4)` is the connection form already implicit in the projective two-chart
reconstruction formula

```text
x=2x'/(x''/x'-u''/u').                                   (5)
```

The Lean module proves `(1)` and `(4)` over every characteristic-zero differential field.

## Squarefree Euler--Gamma specialization

The unconditional theorem `hypertranscendental_riemannZeta` makes the raw reciprocal horizon
literal for the proved HT source.  Put

```text
x_zeta(s)=zeta(s),
g_zeta=-zeta(s)^(-2).                                    (6a)
```

Then `(3)` gives the genuine HT transition connection

```text
d log g_zeta=-2zeta'(s)/zeta(s)=2A(s).                   (6b)
```

The completion and squarefree normalization form a source-defined three-chart weld:

```text
2A
  -- add Q_arch --> Q_Xi
  -- subtract 4A(2s) --> Q_sq.                           (6c)
```

The first arrow supplies the Gamma/reflection Hardy polarization and reallocates the known Euler
pole.  The second arrow is holomorphic throughout the strict right half-plane.  Neither arrow
inserts an unknown nontrivial divisor.  Thus the projective topology is anchored to the
unconditionally HT function `zeta`, while the final chart is the positive squarefree metric
representative carrying the same unknown anti-causal divisor channel.

Put

```text
Z_sq(s)=zeta(s)/zeta(2s),
X_sq(s)=s(s-1)pi^(-s/2)Gamma(s/2)Z_sq(s)/2
       =Xi(s)/zeta(2s).                                  (6)
```

The completed squarefree fixed current is

```text
Q_sq(s)=Q_arch(s)+2J_sq(s)
       =-2X_sq'(s)/X_sq(s).                              (7)
```

Apply `(1)`--`(4)` to `x=X_sq`.  The reciprocal derivative-horizon transition is

```text
g_sq=-X_sq^(-2),
d log g_sq=Q_sq(s) ds.                                   (8)
```

Hence `Q_sq` is not a scalar current later attached to the HT geometry.  It is the Cech
connection of the source-derived reciprocal-horizon gluing itself.  This algebraic statement does
not require an unproved hypertranscendence theorem for `X_sq`; its status as an HT-derived chart
comes from the source weld `(6a)`--`(6c)`.

The already proved right-half localization law gives

```text
P_anti Q_sq=P_anti Q_Xi=ell_E.                           (9)
```

Combining `(8)` and `(9)` proves:

> The RH-bearing anti-causal vector `ell_E` is exactly the anti-causal Hardy realization of the
> reciprocal projective-horizon transition connection of the completed squarefree HT source.

No Xi zero list is used to construct the left side of `(9)`.  The source amplitude `(6)`, its
reciprocal chart, and the Hardy orientation are fixed before a divisor is expanded.

## Positive boundary trace constructed from the seam

Let `H_(g_sq)` be the Hankel operator whose kernel is the inverse-Laplace profile of
`P_anti d log g_sq`, and let `Q_u` cut the output half-line to `[0,u)`.  Define the extended
positive reciprocal-horizon trace density

```text
T_HT(g_sq)
 =limsup_(u downarrow 0)
    u^(-1)||Q_u H_(g_sq)||_(S_2)^2.                       (9a)
```

The proved boundary relative-trace identity gives

```text
||Q_u H_(g_sq)||_(S_2)^2
 =integral_0^infinity min(t,u)|ell_E(t)|^2 dt,            (9b)
```

and therefore, in the extended nonnegative reals,

```text
T_HT(g_sq)=||ell_E||_2^2.                                (9c)
```

Equations `(8)` and `(9a)` define the trace from the source transition and Hardy polarization;
`(9b)`--`(9c)` identify it with the Ward energy.  No normality of the full Hankel operator is
required.  If the trace is infinite, `(9a)` still exists as an extended obstruction and cannot
satisfy a four-unit bound.

Thus the analytic reciprocal-horizon trace is already constructed.  The open geometric theorem
is the comparison

```text
T_HT(g_sq)<=||tau_sq^crit||_capacity^2=4,                (9d)
```

where `tau_sq^crit` is the source-rigged Pluecker boundary trace.  Only the capacity-side lift and
nonexpansivity in `(9d)` remain open.

## Puncture charge and first-trace topology

If `rho` is a zero of `X_sq` of multiplicity `m`, then a small positively oriented loop gives

```text
(1/(2pi i)) integral Q_sq(s) ds=-2m.                    (10)
```

Thus a divisor point is a puncture charge of the reciprocal-horizon transition line.  In the
strict right half-plane `zeta(2s)` is holomorphic and nonzero, so these charges are exactly the Xi
charges.  The squarefree determinant factorization

```text
Z_sq=det_2(I+A_s) exp(P_prime(s))                         (11)
```

then identifies the same transition as a first-trace corona class: `det_2(I+A_s)` has no
right-half charge, while the missing first trace carries the monodromy.  Equations `(8)` and
`(11)` therefore identify two previously separate descriptions of the same object:

```text
projective reciprocal-horizon Cech connection
  = Laurent opposite-chart seam
  = first-trace determinant-corona current.              (12)
```

## No-go and positive successor

The depth-two projective-horizon theorem proves that the direct and reciprocal horizons have only
the constant field in common after two jets.  Therefore `Q_sq` cannot be recovered as a common
ordinary horizon invariant at that depth.

**Positive HT theorem.**  A divisor-sensitive current of a complementary HT horizon pair may
live canonically in its transition torsor even when the two observer fields have trivial meet.
The relevant information is gluing data, not shared data.

The two-chart topology also does not by itself give a norm.  An arbitrary reciprocal transition
may have arbitrarily large anti-causal Hardy energy.

**Positive successor.**  The remaining RH theorem is now a comparison of two independently
constructed metrics on the proved seam, not a trace-existence or identification statement: show
that the source-rigged Pluecker/capacity norm dominates the positive Hardy trace density `(9a)`.
For the squarefree source this is precisely

```text
||P_anti d log g_sq||_2^2<=4.                            (13)
```

The left side is `||ell_E||_2^2` by `(8)`--`(9)` and the right side is the proved critical
squarefree tangent capacity.  Thus `(13)` gives RH by the existing four-unit Cauchy threshold.

## Anti-theatre verdict

This theorem closes a real missing identification: the general HT projective topology produces
the actual source current `Q_sq`, and Hardy localization produces the actual normal vector
`ell_E`.  It does not prove the metric trace inequality `(13)`.  Calling the transition unitary,
harmonic, or polarized without constructing the source capacity metric on its boundary trace
would still be a restatement of the Ward estimate.

## Gates

- [x] reciprocal horizon tangent transition computed
- [x] transition logarithmic connection computed
- [x] generic identities Lean-formalized
- [x] completed squarefree amplitude identified
- [x] topology anchored to the unconditional hypertranscendental zeta source
- [x] Gamma-completed and positive-squarefree charts connected by source-defined gauges
- [x] its horizon seam identified with `Q_sq`
- [x] anti-causal component identified with `ell_E`
- [x] puncture charge and first-trace corona interpretations matched
- [x] construct the extended positive Hardy boundary trace directly from the horizon seam
- [x] identify that trace with `||ell_E||_2^2`
- [ ] lift the same seam to the source-rigged Pluecker capacity boundary
- [ ] prove harmonic Hardy projection is nonexpansive from capacity norm
- [ ] deduce the four-unit bound and RH
