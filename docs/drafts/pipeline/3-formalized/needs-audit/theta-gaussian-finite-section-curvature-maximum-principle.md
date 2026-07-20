# Theta-Gaussian finite-section curvature maximum principle

- **ID:** `theta-gaussian-finite-section-curvature-maximum-principle`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Statement:** Every finite gamma-normalized curvature section of the completed Riemann-theta
  Gaussian moment flow preserves the nonnegative cone when its initial section and its single
  outgoing curvature channel are nonnegative.

## Exact theorem

Let `a <= b`, let `J` be a nonnegative integer, and let

```text
S_j, R_j, A_j, B_j : [a,b] -> R,       0 <= j <= J,
S_(J+1) : [a,b] -> R
```

be continuous, with every `S_j`, `j <= J`, differentiable on `(a,b)`.  Suppose

```text
S_j' = A_j + B_j S_(j+1) + R_j S_j,   0 <= j <= J,             (1)
A_j >= 0,  B_j >= 0.                                            (2)
```

If

```text
S_j(a) >= 0,                 0 <= j <= J,                        (3)
S_(J+1)(lambda) >= 0,        a <= lambda <= b,                   (4)
```

then

```text
S_j(lambda) >= 0,            0 <= j <= J, a <= lambda <= b.      (5)
```

For the completed theta Gaussian aperture, put

```text
M_j(lambda)=integral_0^infinity x^(2j) exp(lambda x^2) Phi(x) dx,
q_j(lambda)=M_(j+1)(lambda)/((j+1/2)M_j(lambda)),
S_j(lambda)=q_j(lambda)-2q_(j+1)(lambda)+q_(j+2)(lambda).
```

The exact source flow already proved in
`PrimeArchThetaGaussianApertureCurvatureFlow.lean` has

```text
A_j=4(q_j-q_(j+1))^2,
B_j=(j+7/2)q_(j+2)>0,

R_j=-(j+9/2)q_j+(1/2-j)q_(j+1)+(j+9/2)q_(j+2).                 (6)
```

Thus `(1)`--`(5)` apply literally to every finite curvature section of the completed theta source.

## Complete proof

### Scalar integrating-factor lemma

Let `f,r` be continuous on `[a,b]`, let `f` be differentiable on `(a,b)`, and assume

```text
f'(lambda)-r(lambda)f(lambda)>=0,        a<lambda<b,             (7)
f(a)>=0.                                                         (8)
```

Define

```text
I(lambda)=integral_a^lambda r(t)dt,
g(lambda)=exp(-I(lambda))f(lambda).
```

The fundamental theorem of calculus and the product and chain rules give, on `(a,b)`,

```text
g'(lambda)
 =exp(-I(lambda))(f'(lambda)-r(lambda)f(lambda))
 >=0.                                                            (9)
```

Hence `g` is nondecreasing on `[a,b]`.  Since `I(a)=0`,

```text
g(lambda)>=g(a)=f(a)>=0.
```

The exponential factor is strictly positive, so `f(lambda)>=0` throughout `[a,b]`.

### Finite triangular cone

We prove `(5)` by downward induction.

At level `J`, hypotheses `(1)`, `(2)`, and `(4)` give

```text
S_J'-R_J S_J=A_J+B_J S_(J+1)>=0.
```

Together with `S_J(a)>=0`, the scalar lemma gives `S_J>=0` on `[a,b]`.

Now suppose `S_(j+1)>=0` on `[a,b]`.  Again,

```text
S_j'-R_j S_j=A_j+B_j S_(j+1)>=0,
```

and `S_j(a)>=0`; the scalar lemma yields `S_j>=0`.  Repeating from `j=J` down to `j=0` proves
`(5)`.

### Theta specialization

For the literal completed theta source, positivity of every moment gives `q_j>0`.  Equation `(6)`
is the exact differentiated moment-ratio identity, so `A_j>=0` and `B_j>0`.  The abstract finite
triangular theorem therefore gives the claimed finite-section maximum principle without any RH,
zero-location, spectral, or unproved source hypothesis.

## Hostile audit

- The boundary implication `S_j=0` and `S_(j+1)>=0` implies `S_j'>=0` is **not by itself** enough:
  a flat cubic may cross with zero derivative.  The proof uses the full linear differential
  inequality and its integrating factor.
- Positive-orthant invariance for cooperative systems is classical Nagumo/Kamke parent theory.
  The abstract triangular lemma is therefore a `[BRIDGE]`, not a novelty claim.
- The candidate new content is the exact completed-theta curvature flow `(6)` and its resulting
  identification of the sole outgoing boundary coordinate `S_(J+1)` for every finite section.
- The theorem does not prove `S_j>=0` on the whole infinite hierarchy.  It proves positively that a
  successful proof must supply a cofinal nonnegative boundary condition; finite-degree curvature
  cannot fail independently of the tail.

## Positive RH obligation

The remaining source theorem is now a boundary-at-infinity statement:

```text
For every compact Lambda subset (-infinity,0],
there exists J such that S_j(lambda)>=0
for every lambda in Lambda and every j>=J.                       (10)
```

Combined with the cold-aperture fixed-degree seed and the finite-section maximum principle, `(10)`
propagates nonnegative curvature to every finite degree, including the GABTC coordinate `S_0`.
The height-localized completed-tail contraction already removes the undifferentiated higher-atom
mass from `(10)`; the surviving research core is the large-degree second-difference transfer for
the positive `p=4` channel and its first-atom amplitude multiplier.

## Literature boundary

- Csordas--Varga prove the Gaussian-deformed ordinary Turan inequalities for the Riemann theta
  moments, not the second-difference curvature flow or this source-specialized outgoing-coordinate
  reduction.
- Positive invariance of the nonnegative orthant for quasipositive/cooperative ODEs is classical.
  No novelty is claimed for that parent theorem.
- Targeted searches found no statement of the completed-theta flow `(6)` together with its
  finite-section boundary-at-infinity reduction.  This is noncollision evidence, not a priority
  certification.

## Lean realization

The source-independent integrating-factor and finite triangular-cone theorems are:

```text
formal/GaloisForLFunctions/HTGeometry/LinearDifferentialCone.lean

HTGeometry.nonnegativeOn_Icc_of_deriv_sub_reaction_nonnegative
HTGeometry.finiteTriangularCone_nonnegative
```

The completed-zeta theta specialization and the single paper capstone are:

```text
formal/GaloisForLFunctions/RHTower/
  PrimeArchThetaGaussianApertureFiniteSectionMaximum.lean

RHTower.thetaCuspGaussianApertureRatioCurvature_finiteSection_nonnegative
RHTower.thetaCuspGaussianApertureBalance_nonnegative_of_finiteSection
RHTower.thetaCuspGaussianAperture_curvatureTransportLocalizationCapstone
```

The capstone states in one theorem the finite-section maximum principle, the exact
response-centered leading-channel concentration, and the resolution-safe contraction of the
complete higher-atom tail against the literal first atom.

## Gates

- [x] exact statement and source definitions
- [x] complete integrating-factor proof
- [x] hostile flat-crossing audit
- [x] parent-theory classification of the abstract maximum principle
- [x] source-specialized paper theorem
- [x] unconditional Lean theorem
- [x] axiom audit and narrow module build
- [ ] independent specialist priority audit

## Log

- 2026-07-20 -- The local zero-boundary derivative slogan was rejected as insufficient.  The full
  reaction equation supplies an integrating factor, yielding the dependency-closed finite-section
  maximum principle and identifying the cofinal boundary condition as the exact positive survivor.
