# Route J: all four continuum rows force four phase-weighted sign changes

**Status:** `[PAPER+LEAN-PROVED] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

## Frontier advance

The preceding continuum theorem used three linear combinations of the four physical
imaginary-value and real-derivative rows and proved that a nonzero atomless source needs at least
three sign changes in `sin(u t)h(t)`. That was not sharp. The unused antisymmetric derivative row
adds a fourth independent moment.

Using all four physical rows gives the exponential-Hermite system

```text
exp(c t),  t exp(c t),  exp(-c t),  t exp(-c t).        (1)
```

After multiplication by the positive factor `exp(c t)`, its test functions have the form

```text
J(t)=(A+B t)exp(2c t)+C+D t.                            (2)
```

A dependency-closed twice-Rolle argument proves that a nonzero `J` has at most three distinct
roots. Rank-nullity constructs a nonzero `J` through any prescribed three positive roots, and the
same rigidity forces those roots to be simple and exhaustive. Its sign therefore alternates
exactly at those roots. Pairing this test against the physical rows kills every atomless source
with at most three phase-weighted sign changes.

This strictly strengthens the previous boundary from three to four. It does not close Route J:
four-or-more phase-weighted changes, phase-node mass, other singular measures, reflection
breaking, and relation-valued channels remain live.

## Physical hypotheses

Let `mu` be a positive measure on the real line with zero mass at every singleton. Let `h` be
real-valued, fix `c>0`, and let `u` be real. Assume almost every nonzero source point satisfies

```text
t>0,  sin(u t) != 0.                                    (3)
```

Write

```text
p(t)=sin(u t)h(t).                                      (4)
```

For `q=+c,-c`, define the actual reflected sine rows

```text
S_q(t)=exp(q t)p(t),
R_q(t)=t exp(q t)p(t).                                  (5)
```

These are forced by the source jet. If

```text
G_q = integral h(t)(1-exp(q t)exp(i u t)) dmu(t),
H_q = integral (-i t)h(t)exp(q t)exp(i u t) dmu(t),
```

then, up to the fixed convention for the derivative sign,

```text
Im G_q = -integral S_q dmu,
Re H_q =  integral R_q dmu.                             (6)
```

Hence zero imaginary value and purely imaginary derivative at both reflected fibres imply

```text
integral S_c dmu = integral R_c dmu = 0,
integral S_(-c) dmu = integral R_(-c) dmu = 0.          (7)
```

Assume all four rows are integrable.

Say `p` has at most three alternating sign changes if there are `0<a<b<d` such that either

```text
(t-a)(t-b)(t-d)p(t) >= 0  mu-almost everywhere,         (8a)
```

or the reversed inequality `(8b)` holds.

## Theorem: four-alternation necessity

**Theorem.** Conditions `(3)`--`(8)` imply

```text
h=0  mu-almost everywhere.                              (9)
```

Therefore every nonzero atomless literal reflected scalar source satisfying all four physical
rows has at least four alternating sign changes in `sin(u t)h(t)`.

## Exponential-Hermite rigidity

For a nonzero real number `lambda`, define

```text
J(t)  = (A+B t)exp(lambda t)+C+D t,
J'(t) = (B+lambda(A+B t))exp(lambda t)+D,
J''(t)= exp(lambda t)
        (2 lambda B+lambda^2(A+B t)).                   (10)
```

### Lemma 1: four distinct roots force the zero function

Suppose `J(a)=J(b)=J(d)=J(e)=0` for `a<b<d<e`. Rolle's theorem gives three ordered roots of `J'`.
A second application gives two distinct roots `y_1<y_2` of `J''`. Since the exponential factor is
strictly positive,

```text
2 lambda B+lambda^2(A+B y_1)=0,
2 lambda B+lambda^2(A+B y_2)=0.                         (11)
```

Subtracting and using `lambda!=0`, `y_1!=y_2` gives `B=0`; either equation then gives `A=0`.
The original function is now affine, and two distinct roots give `C=D=0`. Thus a nonzero `J`
has at most three distinct roots.

### Lemma 2: a nonzero test exists through any three prescribed roots

Evaluation at `a,b,d` is a linear map

```text
E : R^4 -> R^3,
(A,B,C,D) |-> (J(a),J(b),J(d)).                         (12)
```

Its kernel is nontrivial by `dim R^4 > dim R^3`. Choose a nonzero coefficient vector in the
kernel. Lemma 1 shows that its zero set is exactly `{a,b,d}`.

### Lemma 3: the three roots are simple

If, for example, `J'(a)=0`, Rolle gives roots of `J'` in `(a,b)` and `(b,d)`. Applying Rolle to
two disjoint ordered pairs of roots of `J'` produces two distinct roots of `J''`. Equations `(11)`
again force `A=B=0`, and the two original roots then force `C=D=0`, contradicting the chosen
coefficient vector. The arguments at `b` and `d` are identical. Thus

```text
J'(a) != 0,  J'(b) != 0,  J'(d) != 0.                  (13)
```

Continuity, absence of any other roots, and `(13)` imply exact sign alternation. Consequently one
of the following two global certificates holds on `t>0`:

```text
(t-a)(t-b)(t-d)J(t) >= 0,                               (14a)
(t-a)(t-b)(t-d)J(t) <= 0.                               (14b)
```

## Proof of theorem

Take `lambda=2c` in `(2)` and choose the test `J` supplied by Lemmas 2--3 for the three putative
change points. Put

```text
W(t)=J(t)exp(-c t)p(t).                                 (15)
```

Expanding gives the exact physical-row identity

```text
W(t)
 = A S_c(t)+B R_c(t)+C S_(-c)(t)+D R_(-c)(t).          (16)
```

Thus `W` is integrable, and `(7)` yields

```text
integral W dmu = 0.                                    (17)
```

Let `P(t)=(t-a)(t-b)(t-d)`. Combining one orientation in `(8)` with one in `(14)` shows that `W`
is nonnegative almost everywhere or nonpositive almost everywhere. Indeed, away from the three
roots,

```text
(P J)(P p)=P^2 J p,                                    (18)
```

and `P^2>0`; the factor `exp(-c t)` in `(15)` is positive. At a root of `P`, `J` vanishes.

A one-signed integrable real function with zero integral vanishes almost everywhere, so `W=0`
almost everywhere. The measure gives zero mass to `a,b,d`. Away from these points, Lemma 1 gives
`J(t)!=0`; the exponential never vanishes. Hypothesis `(3)` then converts `W(t)=0` to `h(t)=0`.
This proves `(9)`.

## Exact boundary exposed

```text
four reflected physical value/derivative rows
  + atomless positive-time source away from carrier nodes
  + at most three changes in sin(u t)h(t)
  => zero source.                                      (19)
```

Consequences:

- On one open half-turn chamber, `sin(u t)` has constant sign, so a nonzero regular density needs
  at least four changes of its own sign.
- Unbounded support does not help a source below the four-change threshold.
- The four-row result is strictly stronger than the earlier three-row concavity theorem: it uses
  the derivative-row difference that the concavity reduction discarded.
- Full-turn finite survivors lie on `sin(u t)=0`; they evade `(19)` through singular carrier-node
  support, not through low-variation regular approximation.
- The companion
  `route-j-continuum-four-variation-sharpness.md` constructs a compact atomless source with exactly
  four phase-weighted changes. Thus `(19)` is the exact row-only boundary, not merely a lower
  estimate.

## Novelty and theatre audit

- `[LITERATURE]` Zero bounds for exponential-polynomial Chebyshev systems are classical.
- `[LITERATURE]` General orthogonality-to-Chebyshev-system sign-change principles are classical;
  O. R. Musin, *Chebyshev systems and zeros of a function on a convex curve*, arXiv:0903.1908,
  states such a theorem and converse.
- `[BRIDGE]` Rank-nullity, Rolle's theorem, and one-signed integral rigidity receive no novelty
  claim.
- `[CORPUS AUDIT]` Repository searches found the preceding three-row
  `span{1,t,tanh(c t)}` obstruction, finite full-turn interpolation, atomic arity thresholds, and
  singular phase-node escapes, but no use of all four physical continuum rows to obtain the
  four-change boundary `(19)`.
- `[EXTERNAL AUDIT]` Targeted searches found general ECT-system and sign-change theory, not the
  reflected Fourier--Laplace row conjunction `(5)`--`(7)` or its carrier-weighted Route-J
  consequence.
- `[CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]` Candidate content is the exact use of all four
  source-forced rows, the reduction `(16)`, and the strict source-class upgrade from at least three
  to at least four phase-weighted changes. It is not the parent Chebyshev theorem.
- `[THEATRE CHECK]` This result neither constructs an RH selector nor eliminates coherent
  pre-divisor sources at the sharp four-change boundary. The companion extremizer shows why no
  stronger local-row claim is available. This result does not touch phase-node/singular or
  relation-valued carriers. Route J remains open.

## Lean certificate

Formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedContinuumFourVariationNoGo.lean
```

Principal declarations:

```text
routeJExpHermiteCombination_four_roots_rigid
exists_nonzero_routeJExpHermiteCombination_three_roots
routeJExpHermiteCombination_three_roots_zero_iff
exists_routeJExpHermiteCombination_three_root_sign_certificate
routeJExpHermiteCombination_mul_sine_eq_rows
routeJ_nonAtomicContinuum_sineRows_atMostThreeChanges_ae_zero
```

The module proves the four-root rigidity rather than importing an abstract Chebyshev-system
theorem; constructs the three-root test by finite-dimensional rank-nullity; proves its roots
simple, exhaustive, and alternating; treats both source and test orientations; allows unbounded
support; and concludes almost-everywhere equality under an arbitrary singleton-null reference
measure. Direct
`lake env lean GaloisForLFunctions/RHTower/XiCTaylorSignedContinuumFourVariationNoGo.lean`
and exact-module
`lake build GaloisForLFunctions.RHTower.XiCTaylorSignedContinuumFourVariationNoGo`
both pass. It is wired into `GaloisForLFunctions/RHTower.lean`. A scratch `#print axioms` audit of
all six principal declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.
