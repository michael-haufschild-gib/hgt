# Xi Taylor theta-tail core source cancellation

- **ID:** `xi-taylor-theta-tail-core-source-cancellation`
- **Stage:** 3-formalized
- **Type:** EXACT FINITE SOURCE IDENTITY / REDUCTION
- **Scientific status:** `[BRIDGE] [NOT A PRODUCER]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreCancellation.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedSource.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedFeedback.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorOrientedCoefficientCurrent.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailOrientedDefect.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailMomentLogConvex.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreLaguerreAtomNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailSeamJets.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailDensityAtoms.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailArithmeticTranslate.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailArithmeticPairCurrent.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailMobiusConstraint.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailBalancedMobiusPairCurrent.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreCurrentEquivalence.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailScoreCovariance.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailSurvivalPolarization.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailSurvivalMixedCurrent.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailSurvivalMobiusReflection.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedSurvivalRemainder.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedSurvivalTransform.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedPotential.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailSquareIndexPolarization.lean`
- **Parent target:**
  `../../1-in-progress/xi-taylor-theta-tail-core-density-current.md`

## Statement

For

```text
rho(x)=4T''(x),
S_d(z,x)=sum_(k=0)^d (-1)^k z^(2k)x^(2k+2)/(2k+2)!,
C_d(z,x)=sum_(k=0)^d (-1)^k(zx)^(2k)/(2k)!,
H_d(z,x)=1-(z^2+1/4)S_d(z,x),
```

the finite sections satisfy

```text
partial_x^2 S_d(z,x)=C_d(z,x),
partial_x^2 H_d(z,x)=-(z^2+1/4)C_d(z,x),                 (1)

integral rho(x)H_d(z,x)dx
 =1-4(z^2+1/4)integral T(x)C_d(z,x)dx.                  (2)
```

Writing `D_d=partial_z H_d`, the oriented core current has the exact mixed form

```text
J_(U_d)(z)
 =(1/4)integral Im(rho(x)D_d(z,x))dx
  -integral integral rho(x)T(y)
     Im(D_d(z,x)conjugate((z^2+1/4)C_d(z,y)))dxdy.       (3)
```

There is also a one-derivative survival polarization.  If `eta=-4T'` and

```text
B_d(z)=integral eta(x) partial_x H_d(z,x)dx,
A_d(z)=integral eta(x) partial_x partial_z H_d(z,x)dx,
```

then Lean proves the mixed source derivative, all endpoint and integrability obligations, and

```text
U_d(z)=(1/2)(1+B_d(z)),  U_d'(z)=(1/2)A_d(z),
J_(U_d)(z)=(1/4)Im A_d(z)+(1/4)Im(A_d(z)conjugate(B_d(z))). (3a)
```

This retains the truncated-sine kernel after one integration by parts.  Since `A_d` is the
spectral derivative of `B_d`, it is an exact coordinate for the same current, not a separate
positive source term.

Lean also proves the all-order survival moment shift

```text
(m+1) integral x^m eta(x)dx = integral x^(m+1) rho(x)dx.
```

Hence `eta` supplies no independent coefficient sequence: it reindexes the canonical density
moments by one source derivative.

There is, however, an exact positive complement.  If

```text
g(x)=exp(-x/2)-eta(x),
```

then termwise Gaussian-polynomial comparison proves `rho_n>=(1/2)eta_n` on `x>=0`.  Therefore
`exp(x/2)eta(x)` is decreasing from one and `g>=0`.  Lean formalizes the atom comparison, summed
hazard bound, odd reflection `g(-x)=-g(x)`, and completed-remainder positivity.  The elementary
exponential moments also give

```text
integral rho(x)H_d(z,x)dx
 =(-4z^2)^(d+1)-integral g(x)partial_x H_d(z,x)dx.
```

The transform identity is exact and formalized with all integrability obligations.  Its positive
term is not an error: it cancels the explicit top monomial and therefore must remain polarized in
any current estimate.

This remainder is the decreasing derivative of the even completed potential

```text
p(x)=(1/2)exp(-x/2)-T(x),
p(-x)=p(x), p(x)>=0, p(x)->0,
p'(x)=-(1/4)g(x), p''(x)-(1/4)p(x)=-Phi(x).
```

Writing `G_d=integral g partial_x H_d` and `M_d=(-4z^2)^(d+1)`, Lean differentiates the exact
finite polynomial relation and proves

```text
2U_d=M_d-G_d,
2U_d'=M_d'-G_d',
J_(U_d)=(1/4)Im((M_d'-G_d')conjugate(M_d-G_d)).
```

No differentiation under the integral is assumed.  This proves that the favorable monomial and
the positive-remainder transform cancel at both value and derivative level.  Separate norm bounds
on their cross terms therefore discard the full canonical cancellation rather than control it.

Differentiating the theta reflection also gives the complementary survival law

```text
eta(-x)=-eta(x)+exp(x/2)+exp(-x/2).
```

The two endpoint zeros of the completion-balanced Möbius symbol kill both elementary characters,
so the reflected balanced right survival packet is exactly the negative left packet.  The source
and mixed source--spectral core derivatives are odd in `x`; their second minus sign restores the
original orientation.  The corresponding positive-half/negative-half integral identities are
formalized in `XiCTaylorThetaTailSurvivalMobiusReflection.lean`.  Thus survival bilateralization
is exact but does not by parity alone make the current antisymmetric.

The finite sections also obey the completion identity

```text
z^2S_d(z,x)=1-C_(d+1)(z,x),
z^2H_d(z,x)=(z^2+1/4)C_(d+1)(z,x)-1/4.                  (4)
```

Finally, for every complex polynomial `P`,

```text
J_(z^2P)(z)
 =|z|^4 J_P(z)-2|z|^2 Im(z)|P(z)|^2.                    (5)
```

The exact canonical density also splits as

```text
rho(x)=T(x)+4 Phi(x),
Phi(x)=T''(x)-(1/4)T(x),                                  (6)
```

with `Phi` the completed even theta-cusp source.

The finite completed-source transform is exactly the canonical Taylor section:

```text
2 integral Phi(x)C_d(z,x)dx=P_(2d+1)(z),

z^2[2 integral Phi(x)H_d(z,x)dx]
 =(z^2+1/4)P_(2(d+1)+1)(z)-(1/4)P_1(0),

z^4[2 integral Phi(x)partial_z H_d(z,x)dx]
 =z^2(z^2+1/4)P'_(2(d+1)+1)(z)
  +(z/2)(P_1(0)-P_(2(d+1)+1)(z)).                       (7)
```

At the central completion seam point the raw seam is strictly favorable:

```text
U_d(i/2)=1/2,
J_(U_d)(i/2)=-(1/2)A_d(1/4)<0,                          (8)
```

where every coefficient of the raw tail polynomial `A_d` is strictly positive.

The coefficient telescope gives a stronger axis law.  If

```text
B_d(w)=1/2+(w-1/4)A_d(w),
```

then `B_d` is exactly the next Xi magnitude section plus a positive top monomial.  Its value and
derivative are therefore strictly positive for every `w>=0`, and Lean proves

```text
J_(U_d)(iy)=-2y B_d'(y^2)B_d(y^2)<0  for every y>0.       (8a)
```

Lean also proves the exact current reflections

```text
J_(U_d)(conjugate z)=-J_(U_d)(z),
J_(U_d)(-z)=-J_(U_d)(z),
J_(U_d)(-conjugate z)=J_(U_d)(z).                         (8b)
```

Thus reflection across the imaginary axis preserves the unknown off-axis current and supplies no
pair cancellation.  On the source side, with
`h(x)=(exp(x/2)-exp(-x/2))/2`, the exact laws are

```text
T(-x)=T(x)+h(x),
rho(-x)=rho(x)+h(x),
(rho-T)(-x)=(rho-T)(x)=4 Phi(x).                          (8c)
```

The elementary defect is not integrable against the finite polynomial section on a full line;
subtracting it leaves the even completed-source channel already identified with the circular
Taylor feedback `(7)`.

The completed reflection also determines every odd raw-tail seam jet.  For odd `m`, Lean proves

```text
Phi^(m)(0)=0,
T^(m+2)(0)=(1/4)T^m(0),
T^(2r+1)(0)=-4^(-(r+1)).                                  (8d)
```

Thus repeated integration by parts introduces no unknown boundary coefficient.  This closes the
seam-data ambiguity, but not the sign problem: after the explicit boundary telescope, the
surviving bulk is either the raw two-variable mixed correlation `(3)` or the completed-source
feedback `(7)`.

The differentiated density also has an exact positive integer-atom expansion.  If `rho_n` is its
`n`th Gaussian atom, then Lean proves

```text
rho=sum_(n>=1) rho_n,
rho_n(x)>0  for x>=0,
integral rho_n(x)dx=(8pi n^2-2)exp(-pi n^2).              (8e)
```

In particular the first atom has the exact mass `(8pi-2)exp(-pi)`.  This certifies the dominant
atom coordinate without turning dominance into a current sign.

The same module proves the source-pure pointwise comparison

```text
rho_n(x) <= 5 n^4 exp(-pi(n^2-1)) rho_1(x),  x>=0.        (8f)
```

This transfers to absolute moments and kernel majorants.  It does not transfer to a relative
bound by the oscillatory first-atom transform, so it supplies no current sign at a cancellation
point.  Lean also formalizes the transfer for every raw moment:

```text
M_(n,m) <= 5 n^4 exp(-pi(n^2-1)) M_(1,m),
M_(n,m)=integral x^m rho_n(x)dx.                           (8g)
```

The exact arithmetic translate law is also formalized:

```text
rho_n(x)=n^(-1/2)rho_1(x+log n),
rho(x)=sum_(n>=1)n^(-1/2)rho_1(x+log n),

integral_(0..infinity)rho_n(x)K(x)dx
 =n^(-1/2)integral_(log n..infinity)rho_1(u)K(u-log n)du. (8g')
```

Thus any surviving cancellation estimate can be stated using one fixed density profile and the
full logarithmic-integer pair phases; the absolute domination theorem deliberately discards this
information.

The ordered pair version is also formalized.  If `K_d(z;x,y)` is the symmetric core pair current,
then the full product density is exchanged with the ordered atom-pair sum under an explicit `L^1`
majorant, giving

```text
J_(U_d)(z)
 =(1/4)sum_(m,n>=1) integral integral
    rho_m(x)rho_n(y)K_d(z;x,y)dxdy
 =(1/4)sum_(m,n>=1)(mn)^(-1/2) integral integral
    rho_1(x+log m)rho_1(y+log n)K_d(z;x,y)dxdy.            (8g'')
```

This is a complete justified expansion, not a pointwise or formal manipulation.  It retains the
off-diagonal interference but proves no sign by itself.

The arithmetic translate operator also has an absolutely convergent critical Möbius inverse on
the actual Gaussian density:

```text
rho_1(x)=sum_(n>=1)mu(n)n^(-1/2)rho(x+log n),  x>=0.       (8g''')
```

Lean proves the required Gaussian geometric majorant, absolute double Lambert summability, and
the divisor regrouping.  Applying `(8g''')` inside `(8g'')` returns the original full-density pair
integral by `sum_(d|k)mu(d)=[k=1]`; it supplies no sign or coercive remainder.

The finite inverse has a sharper completion-balanced form.  If

```text
M_N=sum_(n<=N)mu(n), H_N=sum_(n<=N)mu(n)/n,
a=N+1, b=N+2,
alpha_N=a M_N-ab H_N, beta_N=ab H_N-b M_N,
```

then `M_N+alpha_N+beta_N=0` and
`H_N+alpha_N/a+beta_N/b=0`.  Adding the two translates at labels `a,b` therefore kills both
reflection characters exactly:

```text
sum_n c_n n^(-1/2)rho(-x+log n)
 =sum_n c_n n^(-1/2)rho(x-log n).                        (8g'''')
```

This identity is formalized in `XiCTaylorThetaTailMobiusConstraint.lean`.  It avoids every
Mertens-sign input and makes the finite packet reflection-compatible.  The same module proves
`|alpha_N|+|beta_N|<=4(N+2)^3`, a geometric majorant for the translated full-density rows, an
`O((N+2)^4 exp(-pi N/2))` majorant for the balancing correction, and convergence of that majorant
to zero at every `x>=0`.  Thus exact reflection balance costs asymptotically nothing on the
positive half-line.

It is infrastructure, not
yet the current sign: `XiCTaylorThetaTailBalancedMobiusPairCurrent.lean` proves that the core atom,
its spectral derivative, and the pair-current kernel are even in each source coordinate.  Hence
the reflected right/right packet is exactly the left/left packet with the *same* orientation, not
its negative.  The coefficient functional now also records the two exact endpoint-symbol zeros
`C_N(0)=C_N(1)=0`, and the balanced pair module identifies the left value and derivative
half-integrals with the negative-half integrals of the right packet.  Polarization still leaves the
full right/left shifted pair kernel.

The exact moment relations also exclude a direct Theorem-M endpoint-atom representation of the
core.  For core degree `N>=4`, log-convexity of the first `N` completed theta moments and Hausdorff
monotonicity force

```text
p <= M_N <= M_3 <= 8/[N(N-1)(N-2)] <= 1/3.               (8h)
```

Lean proves all-order moment positivity, adjacent log-convexity, ratio monotonicity, and the final
abstract bound `thetaCoreCriticalLaguerre_endpointAtom_le_third`.  Therefore the `p>1/2`
sign-copy mechanism cannot apply to the core even though its added top coefficient differs from
the raw moment section.

The density dilation has an exact mean-zero score.  With

```text
g(x)=rho(x)+x rho'(x),
```

Lean proves

```text
integral g=0,
integral x^m g(x)dx=-m integral x^m rho(x)dx,
x partial_x S_d=z partial_z S_d+2S_d,
z partial_z H_d=x partial_x H_d+(1/2)S_d,

(z^2+1/4)z U_d'(z)
 =-(1/2)(z^2+1/4) integral g(x)H_d(z,x)dx
   +1/4-(1/2)U_d(z).                                    (8i)
```

All integration-by-parts boundary limits and polynomial integrability claims are included in the
formal theorem.  The score coordinate is exact but does not create new moment data.  Lean also
rules out its simplest pointwise sign mechanism: at `d=2`, `z=2+i/5`, the cross phase of `H_d`
is negative on the ordered pair `(1/10,0)` and positive on `(11/5,9/10)`.  Therefore a proof from
`(8i)` must cancel the fully weighted phase reversals rather than invoke scalar Chebyshev ordering.

For any complex polynomial `P`, the current is also the vertical value derivative

```text
d/dy |P(x+iy)|^2=-2J_P(x+iy).                            (9)
```

Because the theta-tail core is the complex lift of a real polynomial, the entire real boundary has
zero current and Lean proves the exact fibre integral

```text
J_(U_d)(x)=0,

J_(U_d)(x+iy)
 = integral_(0..y) [Re(U_d'' conjugate(U_d))-|U_d'|^2](x+it)dt.  (10)
```

Lean also expands the integrand in the raw coordinate `U_d(z)=B_d(-z^2)` as

```text
-2 Re(B_d' conjugate(B_d))
-4 Re(w B_d'' conjugate(B_d))
-4 |z|^2 |B_d'|^2,  w=-z^2.                              (11)
```

The last term is favorable.  No sign has been proved for the integrated sum of the first two.
The combined raw integral is the Lean declaration
`orientedPolynomialCurrent_evenMagnitudeLift_eq_integral_rawDefect`.

The full square-index density packet has two additional exact signed polarizations.  For
`X=pi m^2 exp(2x)` and `Y=pi n^2 exp(2y)`, Lean proves

```text
(1-24X+16X^2)(1-24Y+16Y^2)
 =16(X+Y-3/4-12XY)^2-8(1-16XY)^2.
```

It also splits the full packet by exact `2`-adic valuation.  If
`F_k=2^(-k/2)rho(x+log(2^k))`, `O_k=F_k-F_(k+1)`, and
`V_k=2F_(k+1)-F_k`, then for every finite `N`,

```text
rho(x)rho(y)
 =sum_(k<N)(2^(k+1)O_k(x)O_k(y)-2^k V_k(x)V_k(y))
  +2^N F_N(x)F_N(y).
```

Both identities are lifted exactly to the symmetric core kernel and its oriented-current
integral.  The parity reflection

```text
V_0(-x)=2^(1/2)O_0(x-log 2)
  +2^(1/2)R(x-log 2)-R(x)
```

is formalized as `thetaSquareIndexParityDensity_neg_reflection`.
The dyadic top row has the explicit Gaussian majorant
`C_x 2^k exp(-pi 2^k/2)`, and both the row and the weighted two-variable remainder are proved to
tend pointwise to zero on the closed positive source half-line.

## Scope

Equations `(1)`--`(11)` retain the boundary seam and separate the completion radial cost from the
cosine correlation.  Equation `(7)` proves that the completed-source channel is a feedback copy of
the unknown Taylor section, so treating it as an independently positive correction is circular.
Equation `(8a)` signs the positive imaginary axis, not the general vertical fibres in the open
strip.  The remaining producer is exactly the raw `T` mixed correlation plus seam in `(3)` away
from that axis.  The signed square-index and dyadic Haar identities expose cofinal arithmetic
cancellation, but the same oriented pair kernel multiplies both channels.  Their reflection also
translates the finite cosine section, so a termwise sign would be an additional hypothesis rather
than a consequence of the polarization.  Therefore this package is a formalized reduction, not the sublinear-current
producer and not an RH proof.  The exact boundary theorem
`xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis` proves that, on every
source-selected odd super-accurate schedule, the remaining core-current predicate is equivalent to
RH.  Its RH-to-current direction is a logical strength audit, not an unconditional source sign.

## Verification

- Targeted module build passes.
- Formal lint passes with no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- The principal declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- The axis theorem is
  `xiCTaylorThetaTailCorePolynomial_current_mul_I_neg`; the source reflections are
  `thetaCuspTailSecondDensity_neg` and `thetaCuspTailSecondDensity_sub_tail_neg`.
