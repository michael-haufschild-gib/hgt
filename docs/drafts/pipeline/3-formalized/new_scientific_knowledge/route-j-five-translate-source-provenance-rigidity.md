# Route J: sharp five-translate regular sources are target-informative

**Status:** `[PAPER+LEAN-PROVED] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

## Frontier advance

The sharp regular survivor used five equal rectangle bumps at spacing `L` and a mask chosen from
the local damping radius `r=exp(cL)`. This note classifies that whole source class rather than only
the exhibited vector.

For arbitrary real coefficients on the five translates:

1. all four physical reflected value/first-moment rows vanish exactly when the mask polynomial has
   double roots at `r` and `r^(-1)`;
2. every such coefficient vector is a scalar multiple of
   `(X-r)^2(X-r^(-1))^2`;
3. one nonzero fixed mask can serve a second radius `s` only if `s=r` or `s=r^(-1)`;
4. on the physical branch `r,s>1`, only `s=r` remains;
5. at fixed positive translate spacing, one nonzero physical source therefore serves at most one
   positive damping.

This is a class-complete cross-fibre no-go for the minimal regular extremizer family. It proves
that the sharp five-bump survivor is necessarily target-informative, not merely that the displayed
construction happened to use local parameters.

It does not classify arbitrary four-change densities or phase-node singular sources. Route J
remains open.

## Arbitrary five-translate source

Fix `L>0`. Let `b` be the rectangle bump

```text
b(t)=1_((L/4,3L/4])(t),                                (1)
```

and let `b_j(t)=b(t-jL)` for `j=0,...,4`. For an arbitrary coefficient vector
`a=(a_0,...,a_4)`, define

```text
p_a(t)=sum_(j=0)^4 a_j b_j(t),                         (2)
A_a(X)=sum_(j=0)^4 a_j X^j.                            (3)
```

Write

```text
V(q)=integral exp(qt)b(t) dt,
T(q)=integral t exp(qt)b(t) dt.                        (4)
```

Translation by `jL` gives

```text
integral exp(qt)b_j(t) dt
  =exp(qjL)V(q),                                       (5)

integral t exp(qt)b_j(t) dt
  =exp(qjL)(T(q)+jL V(q)).                             (6)
```

Therefore every coefficient vector, not only the canonical one, satisfies

```text
integral exp(qt)p_a(t) dt
  =V(q)A_a(exp(qL)),                                   (7)

integral t exp(qt)p_a(t) dt
  =T(q)A_a(exp(qL))
   +L V(q) exp(qL) A_a'(exp(qL)).                     (8)
```

The base transform never vanishes on the real axis:

```text
V(q)>0 for every real q,                               (9)
```

because `exp(qt)` is strictly positive and `(L/4,3L/4]` has positive length.

## Complete coefficient-kernel classification

Let `c>0` and

```text
r=exp(cL)>1.                                           (10)
```

The four reflected physical rows are

```text
integral exp( ct)p_a(t) dt = 0,
integral t exp( ct)p_a(t) dt = 0,
integral exp(-ct)p_a(t) dt = 0,
integral t exp(-ct)p_a(t) dt = 0.                     (11)
```

By `(7)`, `(9)`, and `exp(-cL)=r^(-1)`, the two value rows in `(11)` are equivalent to

```text
A_a(r)=A_a(r^(-1))=0.                                 (12)
```

After `(12)`, equation `(8)` and `L V(plus-or-minus c)!=0` make the two first-moment rows
equivalent to

```text
r A_a'(r)=r^(-1) A_a'(r^(-1))=0.                     (13)
```

Both radii are nonzero, so `(12)--(13)` say that `r` and `r^(-1)` are double roots. Since `r>1`,
they are distinct. Since `deg A_a<=4`,

```text
A_a(X)=lambda (X-r)^2(X-r^(-1))^2.                   (14)
```

The leading coefficient in `(14)` is `lambda=a_4`. Expanding proves the exact kernel formula

```text
(a_0,...,a_4)
=a_4(1,
     -2(r+r^(-1)),
     r^2+r^(-2)+4,
     -2(r+r^(-1)),
     1).                                               (15)
```

Thus the four physical rows have a one-dimensional coefficient kernel, and it is exactly the
sharp survivor ray.

The Lean proof does not appeal to factorization as a black box. It subtracts the vector in `(15)`,
obtains a cubic `B`, and uses the value and derivative equations at `r,r^(-1)`. With
`x=r+r^(-1)>2`, the residual coefficients `b_j` satisfy

```text
2b_2+3x b_3=0,
b_1-3b_3=0,
b_1+x b_2+(x^2-1)b_3=0.                              (16)
```

Their exact linear combination gives

```text
(4-x^2)b_3=0.                                         (17)
```

Since `x>2`, equations `(16)--(17)` force `b_3=b_2=b_1=0`; either value row then gives `b_0=0`.
This is an unconditional coefficient-level proof of `(15)`.

## Transverse orbit rigidity

Suppose one nonzero coefficient vector satisfies the four rows for two positive noncentral radii
`r` and `s`. Applying `(15)` twice and comparing the `X^3` coefficient gives

```text
r+r^(-1)=s+s^(-1).                                    (18)
```

Clearing denominators yields the exact orbit equation

```text
(r-s)(rs-1)=0.                                        (19)
```

Hence

```text
s=r or s=r^(-1).                                      (20)
```

If `r,s>1`, the reciprocal alternative is impossible, so `s=r`. In physical parameters, if the
same nonzero five-bump source with the same spacing `L>0` cancels at positive dampings `c,d`, then

```text
exp(cL)=exp(dL),                                       (21)
```

and injectivity of the real exponential gives

```text
c=d.                                                   (22)
```

This is stronger than checking the displayed canonical mask: `(15)` first proves that every
possible five-tap solution is canonical, and only then derives `(19)--(22)`.

## Scientific consequence

The minimal regular survivor has the same information-capacity defect previously found for the
minimal four-atom phase-node survivor:

```text
fixed minimal source profile
  -> one reciprocal damping orbit
  -> one positive damping.                            (23)
```

For the sharp construction, support spacing already fixes the chosen carrier chamber scale, while
the coefficient ray fixes `r+r^(-1)` and hence `cL`. A source law chosen before the divisor cannot
reuse one nonzero five-bump profile at two distinct reflected targets. Any viable coherent regular
construction must therefore:

- change support geometry or increase translate arity across fibres;
- leave the identical-bump translate class;
- or derive its target-dependent mask from a genuinely pre-divisor global source mechanism.

Repeating the five-bump construction independently at each zero is not source provenance.

## Novelty and theatre audit

- `[LITERATURE]` Polynomial factorization by prescribed roots and multiplicities is classical.
- `[LITERATURE]` Exponential finite differences, exponential B-splines, and cancellation-operator
  symbols encode exponential annihilation through mask factors; see M. Unser and T. Blu,
  *Cardinal Exponential Splines: Part I---Theory and Filtering Algorithms*, IEEE TSP 53 (2005).
- `[LITERATURE]` Minimal annihilators and symbol factorization for polynomial/exponential Hermite
  data are explicit in M. Cotronei and N. Sissouno, *A note on Hermite multiwavelets with
  polynomial and exponential vanishing moments*, arXiv:1702.01007.
- `[LITERATURE]` Minimal-support symmetric subdivision symbols reproducing exponential polynomial
  spaces are developed by C. Conti, L. Gemignani, and L. Romani, *Exponential Splines and
  Pseudo-Splines: Generation versus Reproduction of Exponential Polynomials*,
  arXiv:1404.6624.
- `[BRIDGE]` Equations `(5)--(9)` and the abstract fact that four prescribed root multiplicities
  determine a quartic receive no standalone novelty claim.
- `[CORPUS AUDIT]` Internal search found the constructed Route-J five-bump extremizer and the
  analogous four-atom transverse theorem, but no arbitrary-coefficient physical classification of
  the regular extremizer family.
- `[EXTERNAL AUDIT]` Targeted searches found the general mask-factorization and minimal-annihilator
  technology above, but not the Route-J conjunction of both reflected real Fourier--Laplace
  value/first-moment rows, the sharp four-variation survivor, and positive damping-orbit
  injectivity.
- `[CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]` Candidate content is the exact physical equivalence
  `(7)--(13)`, complete Route-J kernel classification `(15)`, and cross-fibre consequence
  `(19)--(22)`.
- `[THEATRE CHECK]` This closes only the fixed-spacing, identical-five-translate extremizer class.
  It does not exclude arbitrary four-change regular profiles, variable support geometry,
  phase-node/singular measures, or relation-valued carriers. Those remain live on Route J.

## Lean certificate

Formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedContinuumFiveTranslateRigidity.lean
  XiCTaylorSignedContinuumFiveTranslatePhysicalRigidity.lean
```

Principal declarations:

```text
routeJFiveCoeffReflectedRows_classification
routeJFiveCoeffReflectedRows_iff
routeJFiveCoeffReflectedRows_transverse_orbit
routeJFiveCoeffReflectedRows_damping_injective
integral_exp_mul_routeJFiveBumpPhaseDensityWithCoeff
integral_t_mul_exp_mul_routeJFiveBumpPhaseDensityWithCoeff
routeJFiveBumpPhysicalRows_iff_coeffReflectedRows
routeJFiveBumpPhysicalRows_damping_injective
```

Both files pass direct `lake env lean <file>` checks. Exact-module builds pass for

```text
GaloisForLFunctions.RHTower.XiCTaylorSignedContinuumFiveTranslateRigidity
GaloisForLFunctions.RHTower.XiCTaylorSignedContinuumFiveTranslatePhysicalRigidity
```

Both modules are wired into `GaloisForLFunctions/RHTower.lean`. A scratch `#print axioms` audit of
all eight principal declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.
