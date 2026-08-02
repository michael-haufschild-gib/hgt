# Route J: actual continuum phase rows force three phase-weighted sign changes

**Status:** `[PAPER+LEAN-PROVED] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`
`[STRICTLY STRENGTHENED BY THE FOUR-ROW THEOREM]`

## Frontier correction

The finite full-turn theory uses source times at which the Fourier phase is exactly one. A
non-atomic physical-time density cannot inherit that reduction: its phase varies continuously.
Any continuum theorem that keeps only the reciprocal radial factors and suppresses
`sin(u t)` is an auxiliary radial model, not a theorem about the actual Fourier--Laplace source.

Restoring the physical phase exposes the correct invariant. Imaginary-value cancellation and
real-derivative cancellation at the two reflected fibres force three orthogonality rows for

```text
cosh(c t) sin(u t) h(t).
```

Strict concavity then proves that every nonzero atomless source needs at least three sign changes
after multiplication by the carrier phase `sin(u t)`. On one open phase chamber, where the sine
has constant sign, these are sign changes of `h` itself. Support may be unbounded.

This three-row theorem does not close Route J. The companion four-row theorem now eliminates the
three-change class as well. Four-or-more phase-weighted changes, mass on phase nodes, singular
measures, reflection breaking, and relation-valued channels remain live.

## Actual reflected Fourier--Laplace rows

Let `mu` be an atomless positive measure on the real line, let `h` be real, and fix `c>0` and a
real carrier frequency `u`. Assume almost every nonzero source point satisfies

```text
t>0,  sin(u t) != 0.                                    (1)
```

For `q=+c,-c`, define the sine rows

```text
S_q(t)=h(t) exp(q t) sin(u t),
R_q(t)=t h(t) exp(q t) sin(u t).                        (2)
```

These are not invented radial constraints. If

```text
G_q = integral h(t)(1-exp(q t)exp(i u t)) dmu(t),
H_q = integral (-i t)h(t)exp(q t)exp(i u t) dmu(t),
```

then, up to the fixed sign convention,

```text
Im G_q = -integral S_q dmu,
Re H_q =  integral R_q dmu.                             (3)
```

Thus a literal scalar leading jet with zero value and purely imaginary derivative at both
reflected fibres necessarily satisfies

```text
integral S_c dmu = integral S_(-c) dmu = 0,
integral R_c dmu = integral R_(-c) dmu = 0.             (4)
```

Assume all four rows in `(2)` are integrable.

Say the phase-weighted source has at most two sign changes if for some `0<a<b` either

```text
(t-a)(t-b) sin(u t) h(t) >= 0 almost everywhere,        (5a)
```

or the reversed inequality `(5b)` holds.

## Theorem: actual continuum three-alternation necessity

**Theorem.** Conditions `(1)`--`(5)` imply

```text
h=0  mu-almost everywhere.                              (6)
```

Therefore every nonzero atomless literal reflected scalar source has at least three alternating
sign changes in `sin(u t)h(t)`.

## Proof

Put

```text
v(t)=cosh(c t) sin(u t)h(t).                            (7)
```

The sums of the two value and derivative rows in `(4)` give

```text
integral v dmu = 0,
integral t v(t) dmu = 0.                                (8)
```

Their value-row difference gives

```text
integral sinh(c t) sin(u t)h(t) dmu = 0.                (9)
```

Define

```text
g(t)=(exp(2c t)-1)/(exp(2c t)+1)=tanh(c t).             (10)
```

The exact hyperbolic identity

```text
g(t) cosh(c t)=sinh(c t)                                (11)
```

turns `(8)`--`(9)` into

```text
integral v dmu = integral t v dmu = integral g(t)v(t) dmu = 0.  (12)
```

Because `c>0`,

```text
g''(t)=
  8c^2 exp(2c t)(1-exp(2c t))/(exp(2c t)+1)^3 < 0
  for t>0.                                              (13)
```

Hence `g` is strictly concave on the positive half-line. Let `L` be its residual from the affine
chord through `(a,g(a))` and `(b,g(b))`. Strict concavity and strict secant-slope monotonicity give

```text
L(t)<0 on (0,a),
L(t)>0 on (a,b),
L(t)<0 on (b,infinity),
L(a)=L(b)=0.                                            (14)
```

Since `cosh(c t)>0`, `v` has the same sign pattern as `sin(u t)h(t)`. Under `(5a)`, `L(t)v(t)`
is nonpositive almost everywhere; under `(5b)`, replace `v` by `-v`. Equation `(12)` gives

```text
integral L(t)v(t) dmu = 0                               (15)
```

because `L` lies in `span{1,t,g}`. A one-signed integrable function with zero integral vanishes
almost everywhere. Strictness in `(14)` and atomlessness remove the chord endpoints, so `v=0`
almost everywhere. Finally `cosh(c t)>0` and `(1)` force `h=0` almost everywhere. QED.

## Exact boundary exposed

The physical continuum boundary is

```text
zero imaginary value at both reflected fibres
  + pure-imaginary derivative at both reflected fibres
  + atomless positive-time source away from phase nodes
  => at least three changes of sign in sin(u t)h(t).     (16)
```

Consequences:

- On any one open half-turn chamber, `sin(u t)` has constant sign. A nonzero regular density
  supported there needs at least three changes of its own sign.
- The finite full-turn survivor is concentrated exactly on `sin(u t)=0`. It is therefore a
  phase-node singular escape, not an atomless extremizer of `(16)`.
- Smearing a full-turn atom into ordinary physical time immediately activates the sine rows. It
  cannot retain the reflected scalar jet with only two effective alternations.
- Unbounded support is allowed; what matters is carrier-weighted sign variation, not support size.

At this stage this moved the source frontier from the false dichotomy “four atoms versus arbitrary
continuum” to the alternatives

```text
regular source under this three-row reduction: at least three phase-weighted sign changes;
phase-locked source: singular mass on the half/full-turn lattice;
other escapes: reflection breaking or relation-valued scalarization.             (17)
```

The later four-row exponential-Hermite certificate strengthens the first line to at least four.

## Novelty and theatre audit

- `[LITERATURE]` Orthogonality/sign-change theorems for finite Chebyshev systems are classical;
  see S. Karlin and W. J. Studden, *Tchebycheff Systems: With Applications in Analysis and
  Statistics* (1966).
- `[LITERATURE]` O. R. Musin, *Chebyshev systems and zeros of a function on a convex curve*,
  arXiv:0903.1908, proves general sign-change principles and converses.
- `[BRIDGE]` Strict concavity of `tanh` and the chord argument are standard and receive no novelty
  claim.
- `[CORPUS AUDIT]` Targeted searches found finite Route-J phase locking, arity rigidity, and
  unrelated hyperbolic moment arguments, but no reduction of the actual reflected continuum
  sine rows to `span{1,t,tanh(c t)}`.
- `[EXTERNAL AUDIT]` Targeted primary-source searches found general Chebyshev/exponential-system
  theory, not the Route-J Fourier--Laplace row conjunction or phase-node singularity boundary.
- `[CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]` Candidate content is the exact physical reduction
  `(2)`--`(12)` and the resulting carrier-weighted boundary `(16)`, not the parent Chebyshev
  theorem.
- `[THEATRE CORRECTION]` An earlier radial draft omitted `sin(u t)` and therefore did not justify a
  claim about non-atomic physical time. That claim is withdrawn. Lean retains the radial statement
  only as an analytic lemma used by the corrected theorem.
- `[THEATRE CHECK]` This result does not construct an RH selector. By itself it does not close
  three-change or phase-node singular survivors; the companion four-row theorem closes the former
  but not the latter.

## Lean certificate

Formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedContinuumSignComplexityNoGo.lean
```

Principal declarations:

```text
strictConcaveOn_routeJReflectionRatio
routeJ_twoSignChange_reflectionMoments_ae_zero
routeJReflectionRatio_two_mul_cosh
routeJ_nonAtomicContinuum_sineRows_atMostTwoChanges_ae_zero
```

The formal theorem uses an arbitrary atomless reference measure, allows unbounded support, proves
all integrability transfers from the four actual sine rows, treats both alternating orientations,
and concludes almost-everywhere equality to zero. Direct
`lake env lean GaloisForLFunctions/RHTower/XiCTaylorSignedContinuumSignComplexityNoGo.lean`
and exact-module
`lake build GaloisForLFunctions.RHTower.XiCTaylorSignedContinuumSignComplexityNoGo`
both pass. The module is wired into `GaloisForLFunctions/RHTower.lean`. A refreshed scratch
`#print axioms` audit of the analytic core and corrected source theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`.
