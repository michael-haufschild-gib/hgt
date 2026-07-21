# Affine-Gamma parabolicity rigidity law

- **ID:** `affine-gamma-parabolicity-rigidity-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) + THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [LITERATURE NONCOLLISION] [NOT AN RH PROOF]`
- **Source:** internal theta Gaussian-aperture curvature flow, abstract exponential moment ladders
- **Statement:** Affine/Pochhammer normalizations are exactly the index normalizations that turn
  exponential moment-ratio evolution into a local one-sided parabolic flow for second discrete
  curvature.

## Goal

Classify, rather than merely exhibit, the normalization behind the theta Gaussian-aperture
curvature equation.  The target must explain why the Gamma shape `j + 1/2` appears and which part
of the inward curvature orientation is universal.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement, algebraic attack, internal noncollision
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: exact Lean theorem, narrow leaf check, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and external priority audit

## Setup

Let `a=(a_j)_{j>=0}` be a real normalization-weight sequence and let `q=(q_j)_{j>=0}`.
The universal adjacent-ratio vector field is

```text
V_j(a,q)=q_j(a_(j+1) q_(j+1)-a_j q_j).               (1)
```

If positive differentiable moments obey `M_j'=M_(j+1)` and

```text
q_j=M_(j+1)/(a_j M_j),
```

then `q_j'=V_j(a,q)`.  This Riccati/one-sided-Volterra parent is classical and is not the
candidate theorem.

Put

```text
C_j(q)=q_j-2q_(j+1)+q_(j+2).                          (2)
```

Call the weight quadruple `(a_j,...,a_(j+3))` *curvature-parabolic* when there are constants
`kappa,tau` such that, for every four-state `x=(x_0,x_1,x_2,x_3)` on the boundary
`x_0-2x_1+x_2=0`,

```text
V_0-2V_1+V_2
 = kappa (x_0-x_1)^2
   + tau x_2 (x_1-2x_2+x_3).                          (3)
```

Thus the boundary velocity is allowed only a carré-du-champ production term and transport from
the next curvature coordinate; no hidden lower-order state is available on the boundary.

## Master theorem `[PROVED HERE]`

For every real sequence `a`, the following are equivalent.

1. Every consecutive weight quadruple is curvature-parabolic in the sense of `(3)`.
2. The weights are affine:

```text
a_j=alpha+h j                                                   (4)
```

for fixed `alpha,h`.

In that case the coefficients in `(3)` are forced and unique:

```text
kappa=4h,                 tau=a_(j+3),                           (5)
```

and the full off-boundary identity is

```text
C_j'
 =4h(q_j-q_(j+1))^2
  +a_(j+3) q_(j+2) C_(j+1)
  +C_j R_j,                                                    (6)

R_j=-(a_j+4h)q_j+(h-a_j)q_(j+1)+(a_j+4h)q_(j+2).               (7)
```

Consequently, if `h>=0`, `a_(j+3)>=0`, `C_j=0`, and `C_(j+1)>=0`, then `C_j'>=0`.  If `h>0`,
the gap production is strictly positive unless `q_j=q_(j+1)`.  Conversely, any local law of the
form `(3)` forces

```text
a_j-2a_(j+1)+a_(j+2)=0,
a_(j+1)-2a_(j+2)+a_(j+3)=0.                                  (8)
```

The normalizing products are therefore Pochhammer/Gamma products:

```text
N_0 arbitrary nonzero,
N_(j+1)=a_j N_j
=> N_j=N_0 product_(k<j)(alpha+h k),                            (9)
```

and, for `h>0`,

```text
N_j=N_0 h^j Gamma(j+alpha/h)/Gamma(alpha/h).                   (10)
```

For the completed-theta aperture, `alpha=1/2` and `h=1`; `(6)` is exactly the existing theta
curvature-transport equation.

## Complete proof

### 1. Universal ratio flow

Let `M_j(lambda)` be differentiable, nonzero, and satisfy

```text
d M_j/dlambda=M_(j+1).
```

For nonzero weights `a_j`, put

```text
q_j=(M_(j+1)/M_j)/a_j.
```

The quotient rule gives

```text
q_j'
 =(M_(j+2)M_j-M_(j+1)^2)/(a_j M_j^2)
 =q_j(a_(j+1)q_(j+1)-a_jq_j)=V_j(a,q).              (13)
```

This proves the analytic bridge from every shifted moment ladder to `(1)`.

### 2. Necessity of affine weights

Fix one index and abbreviate its four weights by `A,B,C,D`.  Assume `(3)` holds with some
`kappa,tau`.  Its left side is `(11)`.  Evaluate the boundary identity at the following four
zero-curvature states:

```text
(x,y,z,w)=(1,0,-1,0),
            (0,1, 2,0),
            (1,1, 1,0),
            (1,1, 1,1).
```

They give

```text
-A-C             = kappa-2 tau,                       (14)
 2B-8C           = kappa-6 tau,                       (15)
 3B-A-3C         = -tau,                              (16)
 3B-A-3C+D       = 0.                                 (17)
```

Subtracting `(16)` from `(17)` gives `tau=D`.  Eliminating `kappa,tau` from `(14)`--`(17)`
then gives

```text
A-2B+C=0,
B-2C+D=0.                                             (18)
```

Substitution back into `(14)` gives

```text
kappa=4(B-A).                                         (19)
```

Thus one local carré-parabolic boundary law forces the four weights into an arithmetic
progression and uniquely fixes both coefficients.

### 3. Sufficiency and the full reaction term

Conversely, suppose `(18)` holds and set `h=B-A`.  Then

```text
C=A+2h,
D=A+3h.
```

Expanding the right side of

```text
4h(x-y)^2
+(A+3h)z(y-2z+w)
+(x-2y+z)(-(A+4h)x+(h-A)y+(A+4h)z)                  (20)
```

and collecting the six quadratic monomials `x^2,xy,y^2,yz,z^2,zw` gives respectively the
coefficients in `(11)`.  Hence `(20)` equals `(11)` identically.  On the boundary
`x-2y+z=0`, the reaction term vanishes, proving `(3)` with the forced coefficients `(5)`.

If `h>=0`, `A+3h>=0`, `z>=0`, and the next curvature is nonnegative, both surviving boundary
terms are nonnegative.  If `h>0` and `x!=y`, the square term is strictly positive.  This proves
the claimed inward orientation and its strict form.

### 4. Global rigidity

If the local law holds at every index, Step 2 gives

```text
a_j-2a_(j+1)+a_(j+2)=0                               (21)
```

for every `j`.  Therefore the first differences are constant:

```text
a_(j+1)-a_j=a_1-a_0=:h.
```

Induction yields `a_j=a_0+jh`, proving `(4)`.  Conversely an affine sequence has both local
second differences zero, so Step 3 supplies the local law at every index.  This proves the global
equivalence.

Finally, if `N_(j+1)=a_jN_j`, induction and the affine formula give

```text
N_j=N_0 product_(k<j)(alpha+hk),
```

which is `(9)`.  The standard Gamma recurrence `Gamma(u+1)=u Gamma(u)` rewrites this product as
`(10)` when its parameters avoid the poles (in particular for `alpha,h>0`).  No measure-specific
or theta-specific property enters the classification.  QED.

## Formal theorem surface

Permanent module:

```text
formal/GaloisForLFunctions/HTGeometry/AffineGammaMomentCurvature.lean
```

It proves, without hypotheses hidden behind interfaces:

- `localCarreParabolicClosure_forces_affine_and_coefficients`;
- `localCarreParabolicClosure_iff_affine`;
- `localCarreParabolicClosure_coefficients_unique`;
- `affineGamma_ratioSecondCurvatureVelocity_eq`;
- both weak and strict inward-boundary laws;
- `curvatureParabolicAt_all_iff_affine`;
- `normalization_eq_affinePochhammerProduct`;
- `hasDerivAt_normalizedMomentRatio`;
- `hasDerivAt_normalizedMomentRatioCurvature_of_affineWeights`.

The direct leaf check passes.  The final module build and axiom report are recorded after umbrella
registration.

## Algebraic attack

At one index write

```text
A=a_j, B=a_(j+1), C=a_(j+2), D=a_(j+3),
x=q_j, y=q_(j+1), z=q_(j+2), w=q_(j+3).
```

Then

```text
P:=V_j-2V_(j+1)+V_(j+2)
  =Bxy-Ax^2-2Cyz+2By^2+Dzw-Cz^2.                              (11)
```

Under `x-2y+z=0`, so `z=2y-x`, coefficient comparison in the free variables `x,y,w` forces
`tau=D` and two linear conditions on `A,B,C,D`.  Eliminating `D` yields

```text
A-2B+C=0,
B-2C+D=0.                                                     (12)
```

The remaining square coefficient is then `kappa=4(B-A)`.  Conversely `(12)` substituted into
`(11)` gives `(6)`--`(7)` by direct expansion.  Induction on `(12)` gives `(4)` globally.

## Anti-theatre / parent audit

- Exponential moment differentiation and the adjacent-ratio Riccati chain are classical.
- Volterra/Toda moment and Hankel-determinant flows are classical; Chen--Hu--Müller-Hoissen
  (2018) explicitly treat Riccati systems for Volterra hierarchies.
- Gamma-normalized total positivity is also a known moment-representation mechanism; the recent
  Salazar order-moment transport theorem is a direct comparison point.
- The candidate content is the **if and only if normalization rigidity** `(3) <=> (4)`, including
  the forced carré-du-champ coefficient and the full reaction law.  Exact searches for the formula,
  “curvature transport” with moment ratios, affine/Pochhammer normalization with Volterra flow,
  and discrete-convexity preservation found no primary-source collision.  This is literature
  noncollision, not a priority claim.

## RH relevance

The theorem does not prove the theta curvature sign and does not prove RH.  It identifies a forced
carrier law: any source-independent, local, one-sided curvature propagation mechanism for an
exponentially tilted moment ladder must use an affine-Gamma normalization.  In the Connes/theta
route it turns the archimedean Gamma factor from a chosen normalization into the unique local
parabolic normalization; the remaining RH-bearing datum is the cofinal boundary condition at
degree infinity for the actual prime--archimedean source.

## Log

- 2026-07-20 — created in Stage 1 after internal search and targeted Volterra/Gamma-normalization
  literature audit.
- 2026-07-20 — both directions, coefficient uniqueness, the full reaction law, global affine
  rigidity, Pochhammer accumulation, and the abstract differentiable-moment bridge proved on paper
  and in Lean.
- 2026-07-21 — connected the abstract theorem to the literal completed-theta source in
  `PrimeArchThetaGaussianApertureCurvatureFlow.lean`.  The source ratio derivative now invokes
  `hasDerivAt_normalizedMomentRatio`, and
  `hasDerivAt_thetaCuspGaussianApertureRatioCurvature_affineGamma` specializes the full abstract
  curvature law at `a_j=j+1/2`; the older derivative equation is its corollary.  Focused build
  `8809/8809`, downstream finite-section check, standard-axiom audit, and formal lint all pass.
