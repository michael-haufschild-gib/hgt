# Cubic Ward/Hellinger completed source-trace incidence

- **ID:** `cubic-ward-hellinger-completed-source-trace-incidence`
- **Stage:** 1-in-progress
- **Type:** `[CROSS-ROUTE WARD/CCM/R OPENING] [THEOREM (paper)] [NO-GO] [OPEN GRADED PRODUCER]`
- **Source:** `rh-current-frontier-map.md` · `Cubic Ward/Hellinger source-trace opening`
- **Statement:** P-G173--P-G179 are dependency and receiver blocks for the committed cubic
  Ward/Hellinger opening, not its route identity.  The unresolved theorem is a completed
  coefficient-faithful pole--Gamma--von-Mangoldt pre-divisor incidence retaining signed ordinate
  control.  The positive cubic Euler covariance is exact source infrastructure, but it has the
  opposite von-Mangoldt sign from the scalar Ward majorant, and the source-shift energy defect
  behind the positive zero feature is an intrinsically reflection-odd, indefinite primal form.
  Therefore neither scalar functional-equation absorption nor ordinary positive compression can
  be the missing trace contraction.

## Goal

Construct the completed coefficient-faithful pre-divisor incidence demanded by the cubic
Ward/Hellinger source-trace opening.  It must start from the source-only pole--Gamma--von-Mangoldt
functional-equation decomposition, retain signed ordinate control before real-part scalarization,
carry the exact P-G178/P-G179 depth-square block, and contract onto the P-G173 collision carrier.
Any surviving successor must explain how inverse logarithmic source moments become a third-order
Hermitian divisor singularity without inserting Xi copies or their norm.

This is not Route P.  P-G labels name already-committed dependency theorems used by this
cross-route Ward/CCM/R opening.  This card does not assume a zero-side trace capacity law:
P-G176 already proves that law equivalent to RH.

## Gates

- [x] 0 -> 1 in-progress: source-pure operator, exact attack, internal/external novelty sketch
- [ ] 1 -> 2 fully-proven: complete paper proof of every promoted theorem, `[PROVED HERE]`
- [ ] 2 -> 3 formalized: Lean theorem(s), targeted leaf checks/build, axiom/lint pass
- [ ] 3 -> 4 publication-ready: standalone theorem/proof/novelty certificate

## Exact primitive synthesis `[DEPENDENCY P-G177-A] [PAPER PROOF COMPLETE]`

Let `I=Nat.Primes x Nat`, and for `i=(p,e)` put

```text
n_i=p^(e+1),
lambda_i=log n_i,
b_i=Lambda(n_i)/n_i,
phi_i(r)=sqrt(b_i) r (exp(-lambda_i r)-exp(-2 lambda_i r)),  r>0.       (A1)
```

All data in `(A1)` are primitive-Euler data.  No Xi zero, divisor copy, ordinate, target Gram, or
fitted normalization occurs.  On finitely supported `c:I->C`, define

```text
S_0 c = sum_i c_i phi_i  in L2(R_+,dr).                                (A2)
```

Then:

1. `S_0^*S_0` has matrix entries

   ```text
   <phi_j,phi_i>
    =sqrt(b_i b_j) C_1(lambda_i,lambda_j;0),                            (A3)
   ```

   so it is exactly P-G174's primitive collision matrix at `R=1`, `kappa=0`.

2. The column norm is exactly

   ```text
   ||phi_i||_2^2
    =b_i * 115/(864 lambda_i^3)
    =115/[864 (e+1)^3 p^(e+1)(log p)^2].                               (A4)
   ```

3. P-G174 summability therefore extends `S_0` uniquely to a Hilbert--Schmidt synthesis

   ```text
   S:l2(I)->L2(R_+),
   ||S||_HS^2=Tr(S^*S)=routePPrimitiveCollisionCubicTraceBudget.        (A5)
   ```

4. The covariance `H_E=SS^*` is a positive trace-class integral operator.  For `r,s>0`, its
   kernel is the coefficient-faithful Euler current

   ```text
   K_E(r,s)
    =r s sum_i b_i
       (exp(-lambda_i r)-exp(-2lambda_i r))
       (exp(-lambda_i s)-exp(-2lambda_i s))

    =r s [A(1+r+s)-A(1+r+2s)-A(1+2r+s)+A(1+2r+2s)],                  (A6)

   A(z)=-zeta'(z)/zeta(z)=sum_(n>=2) Lambda(n)n^(-z), Re z>1.          (A7)
   ```

5. The two trace presentations agree:

   ```text
   Tr(H_E)=sum_i b_i*115/(864 lambda_i^3)
          =(115/1728) integral_0^infinity t^2 A(1+t)dt
          =(115/864) integral_1^infinity (sigma-1)log zeta(sigma)ds.   (A8)
   ```

   The last expression is the weighted determinant-line free energy of the literal Euler
   determinant `det(I-diag(p^(-sigma)))=1/zeta(sigma)`.

### Paper proof of P-G177-A `[PROVED HERE]`

For `(A3)`, expand the product in `(A1)` and use

```text
integral_0^infinity r^2 exp(-u r)dr=2/u^3, u>0.
```

The four resulting terms are the definition of `C_1(lambda_i,lambda_j;0)`; this is also the
feature proof underlying P-G173.  Setting `i=j` gives

```text
integral_0^infinity r^2(exp(-lambda r)-exp(-2lambda r))^2dr
 =1/(4lambda^3)-4/(27lambda^3)+1/(32lambda^3)
 =115/(864lambda^3),
```

which proves `(A4)`.  The identities `lambda_i=(e+1)log p` and
`b_i=log(p)/p^(e+1)` give its second form.

P-G174 proves `sum_i ||phi_i||^2<infinity`.  The standard Hilbert synthesis theorem therefore
extends `(A2)` to a Hilbert--Schmidt map and gives `(A5)`.  Expanding the rank-one covariance
`sum_i |phi_i><phi_i|` gives the first line of `(A6)`.  Absolute nonnegative convergence permits
termwise regrouping; the prime-power identity for `A` gives the second line.

Finally, Tonelli and

```text
integral_0^infinity t^2 exp(-lambda t)dt=2/lambda^3
```

give the middle equality in `(A8)`.  The Euler expansion

```text
log zeta(sigma)=sum_(n>=2) Lambda(n)n^(-sigma)/log n
```

and `integral_1^infinity (sigma-1)n^(-sigma)ds=1/[n(log n)^2]` give the
last equality.  All interchanges are Tonelli interchanges of nonnegative terms.  `QED`

## First continuation conjecture

```text
[CONJECTURE P-G177-B -- LINEAR HANKEL CONTINUATION]
The anti-causal polar part of the meromorphic continuation of H_E is a trace-contractive copy of
the strict-right cubic Xi collision operator.
```

This would combine `(A5)` with P-G175 and prove RH.  It is not accepted merely because the
covariance kernel contains `-zeta'/zeta`.

## Attack 1: moment-polarity classification `[P-G177-B FALSIFIED]`

The subquantum trace and the desired divisor charge use opposite functional calculi.  For a
Dirichlet atom `b exp(-lambda s)`:

```text
two s-derivatives:       b lambda^2 exp(-lambda s),
three primitives:        b lambda^(-3) exp(-lambda s).                 (B1)
```

At a Xi/zeta zero `rho` of multiplicity `m`, `(A7)` has local part

```text
A(s)=-m/(s-rho)+holomorphic.                                           (B2)
```

Consequently

```text
A''(s)=-2m/(s-rho)^3+holomorphic,                                     (B3)
```

which has the third-order pole required by a cubic resolvent carrier, but its Euler boundary
coefficients are `Lambda(n)(log n)^2/n`.  Their positive prime subseries dominates a positive
constant times `sum_p 1/p`, hence is not summable.

In contrast, the threefold primitive normalized at `+infinity` has coefficients
`Lambda(n)/[n(log n)^3]`, exactly `(A8)`, but the primitive of `(B2)` has local singularity

```text
-(m/2)(s-rho)^2 log(s-rho)+holomorphic polynomial,                     (B4)
```

not an inverse-cubic pole.  It vanishes in modulus at the puncture and retains only logarithmic
monodromy.  Thus a linear one-variable operation cannot simultaneously preserve the trace-class
inverse-log source weight and create the cubic divisor pole.  The equality of P-G173 and P-G174
diagonal constants comes from transposing one Laplace synthesis (`S^*S` versus `SS^*`), not from
an explicit-formula trace identity.

### No-go closure

- **Exact killing mechanism:** derivative/primitive polarity `(B1)`--`(B4)`.  Pole raising costs
  five powers of `log n` relative to the P-G174 trace weight and destroys critical Euler
  summability.
- **Strongest positive survivor:** P-G177-A constructs a canonical positive Euler covariance,
  not the completed Ward source operator.  A viable continuation must be nonlinear or genuinely two-variable
  before codiagonalization: closed-graph inversion, a Fredholm resolvent/determinant, a
  Gauss--Codazzi second fundamental form, or a signed Krein index can turn a soft branch defect
  into a pole.  A bounded linear Hankel projection cannot.
- **New insight:** P-G176's missing incidence is not another linear trace formula.  It is a
  curvature/inversion theorem for the determinant line of `H_E`, and it must retain the
  anti-holomorphic source real structure before scalar trace.
- **Status:** internal search found the CCM polar--prime Cauchy colligation and many source Hankel
  criteria, but not `(A1)`--`(A8)` or the exact polarity classification.  Primary-literature
  search found general Laplace--Carleson and positive-Hankel theory, not this von-Mangoldt cubic
  synthesis or its Xi continuation.  Lean formalization remains gated on final paper audit of the
  strongest exact statement.

## Attack 2: scalar Ward absorption does not commute with cubic compression

The exact source-only Ward majorant is

```text
S_W(w)=2 Re[ (1/2+w)^(-1)+(1/2+w-1)^(-1)
             +logDeriv Gamma_R(1/2+w)-LSeries(Lambda,1/2+w) ].         (C1)
```

Functional-equation absorption proves a pointwise scalar inequality for the continued Ward
response.  It does not prove a Loewner inequality of two-variable kernels.  This distinction is
forced by the arithmetic sign.  The positive covariance `(A6)` is the four-point mixed difference
of

```text
A(s)=+LSeries(Lambda,s)=-zeta'(s)/zeta(s),                              (C2)
```

whereas the von-Mangoldt component in `(C1)` is `-LSeries`.  Atom by atom, the cubic/Hellinger
mixed difference of `+LSeries` is a positive product of two exponential differences; the same
operation applied to `-LSeries` is its negative.

Moreover, the mixed difference has signed coefficients `(+,-,-,+)`.  Therefore it is not a
positive functional on pointwise order: from `F(w)<=G(w)` one cannot infer
`Delta_(r,s)F(w)<=Delta_(r,s)G(w)`.  The scalar Ward inequality cannot be differentiated, finite-
differenced, or cubically compressed to produce the P-G174 covariance bound.  Pole and Gamma
terms might repair the sign only inside a completed matrix identity established before taking real
parts; dropping them, bounding them separately, or using absolute values loses the needed
cancellation.  This is not optional: the committed vertical-divergence theorem proves that the
already-scalarized Gamma majorant has no height-uniform finite budget.

### Scalar-absorption no-go `[PAPER PROOF COMPLETE]`

Let `Delta_(r,s)` denote the four-point operator in `(A6)`.  For the positive Dirichlet atom
`F_lambda(t)=exp(-lambda t)`, direct factorization gives

```text
Delta_(r,s) F_lambda(1)
 =exp(-lambda)
  (exp(-lambda r)-exp(-2lambda r))
  (exp(-lambda s)-exp(-2lambda s)) >= 0.                              (C3)
```

For `-F_lambda` the value is nonpositive and is strict when `lambda,r,s>0`.  Yet constants may be
added to either side without changing `Delta`, and a sufficiently large constant makes either
atom pointwise dominate the other on any prescribed compact Ward window.  Thus pointwise order
contains no information about the sign or size of the mixed difference.  Summing `(C3)` with
von-Mangoldt coefficients proves the sign opposition `(C1)`--`(C2)` wherever the Euler series is
absolute.  QED.

**Consequence.** P-G177's Euler covariance is source-pure and trace class, but it is not the
functional-equation-absorbed pole--Gamma--von-Mangoldt source demanded by this opening.  Calling
it the completed incidence would silently reverse the prime current and discard the divergent
archimedean channel.

## Attack 3: exact modular chamber of the source-shift defect

The horizontal zero feature does come from the fixed critical source translations

```text
(T_L f)(x)=exp(-L/2)f(x+L).
```

But positivity after conormal evaluation is not positivity of the corresponding source operator.
For `L>0`, change variables in the critical norm to obtain

```text
 exp(L)||T_L f||^2-exp(2L)||T_(2L) f||^2
   =integral_R |f(x)|^2 D_L(x) dx,                                   (D1)

 D_L(x)=exp(|x-L|)-exp(|x-2L|).                                      (D2)
```

The defect has the exact moving-wall law

```text
 D_L(3L-x)=-D_L(x),
 D_L(x)<0  iff x<3L/2,
 D_L(x)=0  iff x=3L/2,
 D_L(x)>0  iff x>3L/2.                                                (D3)
```

Indeed, reflection exchanges the two distances.  Since `exp` is strictly increasing, the sign is
the sign of `|x-L|-|x-2L|`; squaring the nonnegative distances reduces it to

```text
(x-L)^2-(x-2L)^2=L(2x-3L).
```

Consequently the quadratic form in `(D1)` takes both signs on compactly supported vectors: use a
nonzero vector supported strictly to the left or right of `3L/2`.  No Loewner-positive difference
of the two prime-normalized shift energies exists.

This does not contradict the strict-right conormal calculation.  If horizontal displacement is
`a>0`, the dual evaluation eigencharacter reads

```text
 exp(-2aL)-exp(-4aL)>0.                                               (D4)
```

Thus zero-side positivity is a polarized dual phenomenon sitting over an indefinite primal
modular defect.  The Lebesgue density `(D2)` is reflection-odd, while the critical Hilbert density
adds the nontrivial Radon--Nikodym factor `exp(-|x|)`.  Hence ordinary Hilbert reflection does not
turn `(D1)` into a positive compression; a modular half-density must be retained.

### Positive survivor: completed modularly graded incidence `[CONJECTURE W-H180]`

The repeated sign failures are shadows of one higher principle.  Functional-equation absorption
must be lifted before scalarization to a completed, matrix-valued *graded* colligation, not merely
to a positive scalar kernel.  Its minimum exact specification is:

1. one source-defined carrier contains pole, Gamma, and resolved von-Mangoldt channels with their
   literal signs and forced cross terms;
2. the reflection exchanging the two shift-depth chambers carries its Radon--Nikodym
   half-density, so the indefinite defect `(D1)` becomes a `J`-oriented matrix coefficient rather
   than a falsely positive operator;
3. depth squaring with modular gain `sqrt(n)` is the primitive Euler restriction of that same
   reflection cocycle, and its cubic source norm is exactly the P-G178/P-G179 `1/8` contraction;
4. cubic tensor/Schur compression is applied to this completed matrix identity before real part
   or scalar trace, landing exactly on P-G173 with signed ordinate entries;
5. the completed source trace, including Gamma/polar cross terms, is bounded by the P-G175 budget
   without reading a Xi zero or assuming P-G176.

Clause 2 explains simultaneously why holomorphic height translation cannot be scalar-normalized,
why the source-shift energy difference is indefinite, and why the arithmetic depth-square gain is
unbounded in counting norm but contractive in cubic measure.  The common obstruction is omitted
modular half-density, not a missing scalar constant.

### Hostile falsifiers for W-H180

- A pointwise consequence of `(C1)` is insufficient by `(C3)`.
- A positive operator inequality between the two shift energies is false by `(D3)`.
- Multiplying the integer-shift tensor by `n` to manufacture unit ordinate phase is not a
  contraction and fails source trace control.
- An Euler-only covariance has wrong completed-source sign.
- Gamma and polar channels may cancel or orient inside one exact colligation; discarding either by
  a separate upper bound is forbidden by vertical divergence.
- A landing defined from the Xi divisor, the target collision Gram, or P-G176 capacity is a
  terminal receiver and fails source purity.

## One possible realization, not route commitment

```text
[CONJECTURE P-G177-C -- DETERMINANT-LINE CURVATURE]
There is a Gamma-completed meromorphic Fredholm/closed-graph family built from H_E before divisor
expansion such that:

1. its Euler-region logarithmic determinant is the literal Gamma--Euler determinant, not Xi by
   definition;
2. its conormal resolvent has strict-right polar second fundamental form equal to the P-G173
   collision Gram, with multiplicity;
3. causal/polar curvature is nonnegative, so the anti-causal trace is at most Tr(H_E);
4. continuation and graph limits preserve the P-G175 trace bound.
```

This is one successor capable of crossing the moment-polarity wall.  It is currently open and is
not privileged over a completed graded Ward colligation, Krein/Fredholm realization, or other
source construction satisfying W-H180.
Existing diagonal Gamma--prime Fredholm operators realize reciprocal Gamma and reciprocal zeta
only in `Re s>1`; their prime branch ceases to be trace class at the critical boundary, and no
source theorem identifies their completed conormal second fundamental form with P-G173.

## Novelty and theatre audit

- P-G177-A is more than a renamed finite Gram: it constructs the infinite synthesis, identifies
  its transposed trace-class covariance with a literal four-point logarithmic-current kernel, and
  identifies the P-G174 budget with determinant-line free energy.
- P-G177-B is recorded as false, not used as an RH premise.
- P-G177-C/W-H180 is not counted as progress until a finite coefficient formula, graph domain, and
  nonexpansive curvature identity are proved independently of Xi zeros.
- Any construction defining its determinant, conormal range, norm, or negative subspace from the
  Xi divisor fails the source-purity gate.

## Lean targets after paper promotion

1. `XiWardCubicTranslationModularChamber.lean`: exact pulled-back critical-shift defect density,
   reflection law, moving-wall sign classification, and explicit two-sign witnesses.
2. `XiWardCubicScalarAbsorptionCompressionNoGo.lean`: four-point exponential factorization and
   failure of scalar order to control signed mixed compression.
3. Promote the infinite Euler synthesis only if its covariance becomes an input to an exact
   completed pole--Gamma--prime colligation; do not formalize it merely to enlarge infrastructure.
4. Wire finished leaf modules into `RHTower.lean`; run only scratch checks and targeted leaf builds,
   never the umbrella build.

## Log

- 2026-08-15 -- P-G177-A originated and paper-proved after complete Route-P/curvature/Deninger
  audit.  Linear Hankel continuation P-G177-B failed under exact moment-polarity attack.  Pivoted
  to determinant-line/closed-graph curvature P-G177-C.
- 2026-08-15 -- Corrected route identity: this card attacks the cross-route cubic Ward/Hellinger
  source-trace opening, while P-G173--P-G179 remain dependencies.  Scalar Ward absorption failed
  to commute with cubic compression because its prime current has the opposite sign and the Gamma
  scalar majorant diverges vertically.  Exact source-shift analysis exposed the reflection-odd
  moving modular wall `(D3)`.  Pivoted from ordinary positivity to W-H180's completed modularly
  graded incidence.

## Dependency sharpening: P-G180--P-G182

Three later receiver theorems simplify the live comparison without changing route identity.

1. P-G180 proves that the collision column is the dyadic innovation `(I-V)psi`, with
   `Vf(r)=f(2r)/2`, and reconstructs the base column by a Calderon telescope with remainder energy
   `8^(-N)`.  The dyadic difference is invertible source geometry, not the singular producer.
2. P-G181 therefore reduces the receiver to the base Cauchy cube

   ```text
   B(rho,tau)=2/[conj(rho-1/2)+(tau-1/2)]^3,                          (E1)
   ```

   whose diagonal is `1/(4a^3)`.  Its complete primitive source budget is strictly below `2`,
   while every strict-right zero costs at least `2`.
3. P-G182 identifies `(E1)` exactly as the Gram of normalized residues of the source-defined
   completed conormal

   ```text
   C(z,r)=logDeriv(xi)(z) r exp(-(z-1/2)r).                           (E2)
   ```

   At a zero of multiplicity `m`, its raw residue is `m r exp(-(rho-1/2)r)`.  Exact divisor trace
   would divide the raw amplitude by `sqrt(m)`.

Thus the live arrow is no longer an unidentified cubic zero kernel.  It is a source bound for a
specific completed logarithmic-conormal residue trace.

## Attack 4: critical-feature Plancherel inversion is unbounded

The existing critical-feature prime--Gamma Gram is a genuine source-to-zero construction, so a
natural conjecture was to recover `(E2)` by Fourier inversion of that frame.  The exact source
profile already formalized in `HedenmalmCriticalFeatureWardGreenPlancherelFracture.lean` is

```text
f_z(x)=exp(-|x|) sourceChar(z,x).                                    (E3)
```

Hence removing the critical-feature smoothing multiplies by `exp(|x|)`.  This inverse is
unbounded on every translation-invariant `L2` source domain: if `g_N` is a unit vector supported
in `[N,N+1]`, then

```text
||exp(|x|)g_N||_2 >= exp(N)||g_N||_2.                                (E4)
```

Equivalently, multiplication by `exp(-|x|)` has no positive lower bound.  This is the same
analytic wall seen in four earlier guises: genuine height translation attenuates by
`exp(-tau a)`; zero-selected Lagrange lifts have uncontrolled norm; the scalar Gamma majorant
diverges vertically; and continuation from the safe Euler boundary is an ill-posed inverse.

**Conjecture failed.** Critical-feature Fourier inversion cannot be the bounded source contraction.
Its strongest survivor is diagnostic: every successful producer must pair the two FE chambers
before attempting to undo their one-sided attenuation.

## Attack 5 and positive survivor: bilateral raw-conormal modular doublet

The P-G182 half-density conclusion is necessary for exact equality with linear divisor
multiplicity, but it is stronger than needed for the one-quantum contradiction.  Let

```text
lambda=rho-1/2=a+i gamma,       a>0,
rho^dagger=1-conj(rho),
psi_rho(r)=r exp(-lambda r),    r>0.                                 (E5)
```

Put the reflected conormal on the negative half-line and pull it back with orientation:

```text
M_rho(r)=-psi_(rho^dagger)(-r), r>0.                                 (E6)
```

Since `rho^dagger-1/2=-conj(lambda)`, direct algebra gives

```text
M_rho(r)=conj(psi_rho(r)).                                           (E7)
```

Therefore the bilinear FE-reflection incidence, before Hermitian scalarization, is already the
positive cubic base charge:

```text
integral_0^infinity psi_rho(r) M_rho(r) dr
 =integral_0^infinity r^2 exp(-2ar)dr
 =1/(4a^3).                                                          (E8)
```

This is the missing modular mechanism at atomic level.  The growing reflected column never lives
on the wrong half-line; causal and anti-causal chambers are paired by orientation reversal, and
the Radon--Nikodym/FE mate becomes the Hermitian conjugate only after that pairing.

### Raw multiplicity removes the half-density gate `[PROVED HERE + LEAN]`

At multiplicity `m>=1`, the raw logarithmic residues in the two legs contribute

```text
Q_raw(rho)=m^2/(4a^3) >= 1/(4a^3) >= 2.                              (E9)
```

P-G181's complete primitive budget is `<2`.  Consequently a completed source bound on the raw
modular-conormal trace would already exclude the first strict-right zero.  Copy resolution and
the factor `1/sqrt(m)` are not part of the minimal RH theorem; they are needed only to identify
the resulting norm exactly with the conventional linear-multiplicity divisor trace.

This distinction is structural.  A scalar logarithmic residue is additive in divisor order.  No
additive amplitude `A:N->R` can satisfy `A(m)^2=m` for every `m`: additivity gives
`A(2)=2A(1)`, while the square laws at `1` and `2` give `A(1)^2=1` and `A(2)^2=2`, hence `4=2`.
Thus square-root multiplicity must come from an orthogonal copy fibre/GNS disintegration, never
from scalar meromorphic functional calculus.  Retaining raw residues avoids this nonadditive step.

Lean module
`formal/GaloisForLFunctions/RHTower/XiWardCubicRawConormalModularDoublet.lean` proves `(E7)`,
`(E8)`, the actual-Xi lower quantum `(E9)`, and the closed additive scalar half-density no-go.

### Canonical copy split and exact balanced source budget `[P-G183--P-G184, LEAN]`

P-G183 nevertheless closes the conventional divisor interpretation rather than leaving the
half-density as an arbitrary zero-dependent correction. On the analytic-order copy fibre of size
`m`, the equal split `v -> (v/m,...,v/m)` is residue conserving, has squared norm `|v|^2/m`, and is
the unique minimum-energy lift by the exact Pythagorean law

```text
sum_j |u_j|^2=m|psi|^2+sum_j |u_j-psi|^2
```

whenever `sum_j u_j=m psi`. This does not strengthen the minimal raw contradiction, but proves
that linear divisor multiplicity is available canonically after any successful source landing.

P-G184 closes a more direct part of W-H181. If `lambda_(p,e)=(e+1)log p`, then cubically
regularizing the balanced primitive source/co-source codiagonal before summation gives

```text
[1/(4 lambda_(p,e)^3)]
  L_a(p,e) conjugate(R_(-a)(p,e))
 =Lambda(p^(e+1))/[4 p^(e+1) log(p^(e+1))^3]
 =routePPrimitiveBaseCauchyCubicWeight(p,e).                         (E9a)
```

The identity is independent of `a`, every finite P-G181 base Gram trace is the corresponding
finite source codiagonal, and the total source trace is exactly
`routePPrimitiveBaseCauchyCubicTraceBudget<2`. Thus the right side of `(E10)` is now itself the
literal source-native two-sided object demanded here. Its construction and estimate are closed;
only completed pole--Gamma transport to the raw Xi conormal remains.

P-G185 proves that this transport cannot be an ordinary absolute contour crossing. With total
joint damping `s`, the regularized cell is `w_base(p,e)p^(-(e+1)s)`, and Lean proves

```text
Summable(regularized joint codiagonal at s) iff s>=0.                (E9b)
```

For `s<0`, the depth-zero prime face is eventually at least `1/(4p)`. Thus cubic regularization
reaches and includes the balanced wall but has zero continuation width beyond it. W-H181 must be
formulated as a completed boundary value, distributional identity, or closed-graph transport at
the wall; an absolutely convergent two-sided source strip does not exist.

P-G186 closes the source-to-window square that remained between the Euler codiagonal and Burnol's
target-support incidence. Put the primitive cell `(p,e)` at the canonical right-half-plane node

```text
z_(p,e)(kappa)=1/2+(e+1)log p+i kappa
```

and scale its inverse Burnol window feature by
`sqrt(Lambda(p^(e+1))/p^(e+1))`. The full aperture Gram of these features, including every
off-diagonal ordinate interaction, is entrywise the P-G181 primitive base Cauchy cube. Its
positivity, balanced-source trace identity, and uniform `<2` budget therefore hold in the literal
Burnol window space before Xi-zero expansion. The only unclosed passage is boundary-value
restriction from these canonical Euler nodes to actual completed-Xi divisor nodes; constructing
another abstract Gram or source window cannot address it.

### Sharpened live conjecture `[W-H181 -- RAW MODULAR CONORMAL TRACE]`

Construct, before divisor expansion, a two-sided pole--Gamma--von-Mangoldt conormal relation whose
right causal and reflected left anti-causal radial legs specialize to `(E5)`--`(E8)`.  Its finite
contour/Riesz compressions must satisfy

```text
Tr_raw(completed reflected conormal compression)
  <= routePPrimitiveBaseCauchyCubicTraceBudget < 2,                   (E10)
```

with the left side defined from completed source coefficients and forced cross terms, not from a
list of Xi zeros.  Residue specialization may then expose the raw `m^2` charges.  No
multiplicity-half-density disintegration is required for the contradiction.

The remaining obstruction is now narrower than W-H180: transport P-G186's already-bounded
source-defined Burnol window Gram through the pole--Gamma functional equation to its restriction
on actual completed-Xi divisor nodes at the sharp P-G185 wall. Scalar holomorphic dephasing still fails because
one chamber alone has nonunit depth modulus; the reciprocal FE pair must be retained through the
transport. P-G173's dyadic collision layer, P-G180's reconstruction, P-G181's source estimate,
P-G182's normalized receiver, and P-G183's multiplicity split are no longer separate gates.

## Updated theatre audit

- A raw-residue trace *defined after listing zeros* is still target-fed and proves nothing.
- Exact half-density normalization is no longer allowed to delay the RH implication; raw
  multiplicity is stronger for the capacity contradiction.
- The bilateral identity `(E8)` is an atomic landing, not the global trace estimate `(E10)`.
- Progress on `(E10)` must exhibit finite pole--Gamma--von-Mangoldt coefficients or a
  source-defined contour/Riesz relation and prove the `<2` norm before residue expansion.

## Log continuation

- 2026-08-15 -- P-G180/P-G181 reduced the receiver to one base Cauchy cube; P-G182 identified it
  with completed-Xi conormal residue Gram.  Critical-feature inversion failed by the exact
  `exp(|x|)` deconvolution wall.  Bilateral FE reflection produced the positive raw-conormal
  modular doublet `(E5)`--`(E8)`.  Proved that raw multiplicity already has the strict two-unit
  quantum and that additive scalar residues cannot implement square-root multiplicity.  Replaced
  the half-density landing requirement by W-H181's strictly weaker raw modular-conormal trace
  bound `(E10)`.
- 2026-08-15 -- P-G183 constructed the canonical minimum-energy copy split. P-G184 proved that
  cubic regularization of the balanced primitive biorthogonal codiagonal is exactly the full
  P-G181 source budget, cellwise, on finite traces, and globally `<2`. The live conjecture no
  longer includes source construction or budget estimation; it is a pole--Gamma boundary-value
  transport theorem for this fixed regularized codiagonal.
- 2026-08-15 -- P-G185 proved the regularized joint-damping chamber is exactly `s>=0`. The
  balanced source trace exists at `s=0`, but every negative damping diverges on primes. Replaced
  ordinary contour continuation by a sharp completed boundary-value/closed-graph transport.
- 2026-08-15 -- P-G186 placed every primitive Euler cell at its canonical right-half-plane node
  with exact von Mangoldt square-root amplitude and proved that the full inverse-Burnol-window
  aperture Gram is the P-G181 base cube. Source-window construction is closed; only completed
  restriction from Euler nodes to actual Xi divisor nodes remains.

## Cross-corpus CCM--Route-P source identification `[PROVED IN LEAN]`

`FrankensteinCCMRoutePBaseCubicGreenSourceBridge.lean` identifies the same labelled arithmetic
mass inside the literal CCM critical-Mellin source, before Xi-zero expansion.  For

```text
G(h)=exp(-h/2)/(4 max(h,log 2)^3),
```

the clamp changes only the prime-free interval `0<=h<log 2`, and every arithmetic atom satisfies

```text
criticalMellinAtomWeight(n) G(log n)
  =Lambda(n)/(4 n log(n)^3)
  =routePPrimeGammaBaseCubicWeight(n).                              (E9c)
```

Pullback along `n=p^(e+1)` is exactly the P-G184 prime-depth weight, preserving prime label and
valuation depth.  Its global sum is the P-G181 budget `<2`; every finite CCM prime functional on
the transported horizon test is the negative truncated Route-P budget; and the full CCM
pole--prime functional is exactly

```text
pole surplus - truncated Route-P budget.                            (E9d)
```

Carrier identification and prime summability are therefore closed across CCM and Route P.  This
does **not** bound a Xi-divisor trace.  It isolates the completed fracture: polar--Gamma surplus
must be shorted at the P-G185 boundary before P-G186's source Gram is transported to divisor copies.

## Second exact chart of the cubic charge: boundary double-pole energy

There is a source-current formulation of `(E8)` that does not begin from inverse logarithmic
Euler moments.  Differentiating the local logarithmic-current pole once gives

```text
J_(a,gamma)(t)=1/[a+i(t-gamma)]^2.                                   (E11)
```

The vertical Hardy--Sobolev mass is

```text
integral_R |J_(a,gamma)(t)|^2 dt
 =integral_R dt/[a^2+(t-gamma)^2]^2
 =pi/(2a^3)
 =2pi * [1/(4a^3)].                                                  (E12)
```

Thus the P-G181 base charge is simultaneously:

- a bilateral FE-reflected radial conormal pairing `(E8)`; and
- `1/(2pi)` times the boundary `L2` energy of the first derivative of a logarithmic-current pole.

This reinterprets the five-log polarity obstruction.  The source need not turn inverse-log
moments into cubic poles.  It may instead construct a completed, exteriorized Hardy--Sobolev
trace of the differentiated pole--Gamma--von-Mangoldt current; cubic charge is then local residue
energy, while inverse-log weights arise only after the source trace is factorized into primitive
radial columns.  The two factorizations must be proved equal before divisor expansion.

The same Lean module proves `(E11)`--`(E12)` and its exact actual-Xi specialization.  This promotes
the most concrete next conjecture:

```text
[W-H182 -- COMPLETED HARDY--RADIAL TRACE IDENTITY]
The FE-exteriorized boundary Hardy--Sobolev trace of the differentiated completed logarithmic
current equals a two-sided modular radial trace whose primitive Euler compression is the P-G181
base covariance; Gamma and polar legs occur as forced cross terms, and the common trace is below
the primitive budget before residue expansion.
```

This is stronger than merely naming a Riesz projection and more falsifiable than determinant-line
curvature: both sides have explicit local kernels `(E8)` and `(E11)`, and a candidate fails if its
Euler restriction carries positive log-square weights rather than the factorized inverse-log
trace, if critical-line poles survive exteriorization, or if Gamma/polar terms are bounded
separately instead of participating in the identity.

- 2026-08-15 -- Identified and Lean-proved boundary double-pole law `(E11)`--`(E12)`.  Pivoted
  from direct analytic continuation of inverse-log covariance to W-H182's equality of two
  factorizations of one completed trace: boundary differentiated-current energy and bilateral
  radial conormal energy.

## Attack 6: Capacity-law circularity and the operator-contraction gate

A direct jump asserting `E_target <= Tr(H_base)` without constructing an explicit operator
contraction `C_S` is circular: Lean proves in `RoutePPrimitiveBaseCauchyCapacityReduction.lean` that
the bare trace capacity inequality `RoutePPrimitiveBaseCauchyTraceCapacityLaw` is itself equivalent
to RH.

Calderon reconstruction (`P-G180`) operates strictly on the primitive Euler source side
(`RoutePPrimitiveHankelDyadicCalderonReconstruction.lean`); it contains no Xi divisor data.
Likewise, `RoutePPrimitiveDepthSquareModularDefect.lean` proves that depth squaring contracts
primitive source energy by `1/8`, while `RoutePPrimitiveCollisionSubquantum.lean` proves that the
resulting total primitive Euler budget is `< 115/108` (and base budget `< 2`).

### Open core in final form

The remaining open theorem must be an unconditional construction of one of the two explicit forms:
1. **Operator Loewner Contraction:** an explicit linear/intertwining operator `C_S` between the
   completed Euler source Hilbert space and the zero conormal space such that
   `G_zero(S) <= C_S G_Euler C_S*` with `||C_S|| <= 1`; or
2. **Direct Source Trace Bound:** a coefficient-faithful pre-divisor contour/Parseval identity
   deriving `Tr(G_zero(S)) <= B_base < 2` directly from the completed logarithmic current
   without postulating the capacity law.

- 2026-08-15 -- Hostile audit identified that `E_target <= Tr(H_base)` is the formal capacity law
  equivalent to RH.  Clarified that Calderon reconstruction is source-only and that the true open
  core is constructing the coefficient-faithful contraction operator `C_S` with `||C_S|| <= 1`.

## Attack 7: The Poisson-Hardy scattering duality and the coherent-norm obstruction `[FALSIFIED / EXPLORATORY]`

### 1. Completed and uncompleted logarithmic currents must remain distinct

For the centered completed entire function `Xi_c(w)=xi(1/2+w)`, functional-equation symmetry makes
`Xi_c` even.  Hence `-Xi_c'/Xi_c` is odd and is purely imaginary on `w=it` away from its poles.
The decomposition containing the Riemann--Siegel velocity and Hardy's `Z'/Z` belongs instead to the
**uncompleted zeta logarithmic derivative** (with sign depending on the theta convention).  The
earlier identification of both expressions as `-xi'/xi` was false and is retracted.

An exploratory **regularized** Cauchy half-plane contour for `Re w>0` suggests the spatial balance:

```text
B(r) = E(r) - sum_(rho in S) m_rho psi_rho(r),                                             (E15)
sum_(rho in S) m_rho psi_rho(r) = E(r) - B(r)   in L2(R_+, dr),                            (E16)
```

where the displayed Fourier formula for `B` must be interpreted using the uncompleted current and
principal values at critical-line zeros.  Neither `(E15)` nor its `L2` boundary limit is yet
paper-proved: contour truncation, indentation, infinite residue convergence, inverse-Laplace
interchange, and the `L2(R_+)` limit remain open analytic obligations.

### 2. Fatal Defect: Coherent-norm vs. Gram-trace confusion `[NO-GO ON SCALAR PASSIVITY]`

Taking the `L2(R_+, dr)` norm of `(E16)` yields the coherent vector norm:

```text
|| sum_(rho in S) m_rho psi_rho ||^2 = m^* G_zero m = ||E - B||^2 = ||E||^2 + ||B||^2 - 2 Re <E, B>. (E17)
```

A fatal error in scalar passivity formulations is the assertion that `||sum m_rho psi_rho||^2 >= Q_raw(rho_0) >= 2`.
This inequality is **generally false**:
- The Lean-proved single-zero quantum `XiWardCubicRawConormalModularDoublet.lean` proves a lower bound on the **diagonal Gram entries**: `G_ii = ||psi_(rho_i)||^2 = Q_raw(rho_i) >= 2`.
- It implies a lower bound on the **Gram trace**: `Tr(G_zero) = sum_i ||psi_(rho_i)||^2 >= 2`.
- But for the **coherent vector norm** `m^* G_zero m`, cross-terms `2 Re(m_i conj(m_j) <psi_i, psi_j>)` can be negative due to oscillatory phase interference between different ordinates `gamma_i != gamma_j`.
- Positive semidefiniteness of `G_zero` only guarantees `m^* G_zero m >= 0`, **not** `m^* G_zero m >= G_ii`.

**Consequences:**
1. Coherent destructive interference can allow `||E - B||^2 < 2` even when off-line zeros exist.
2. Scalar Boundary Passivity `Re <E, B> >= (1/2) ||B||^2` does **not** imply RH without controlling off-line cross-terms.
3. Collapsing all prime and zero channels into a single scalar field `E(r) - B(r)` destroys the orthogonality needed for the trace contradiction.

- 2026-08-15 -- Identified the parity decomposition of the logarithmic current and discovered the
  fatal coherent-norm vs. Gram-trace obstruction: destructive cross-term interference prevents
  scalar field norms from lower-bounding individual diagonal zero charges.

## Attack 8: Bilateral modular involution and the phase-inversion resolution `[EXPLORATORY / LOCAL ONLY]`

### 1. The sign inversion in single-sided boundary pairing

A naive one-sided pairing `<E, B>` on `L2(R_+)` produces an intrinsic sign mismatch:
Integrating `(zeta'/zeta) (zeta'/zeta)''` by parts along the vertical boundary gives
`- ||(zeta'/zeta)'||^2 <= 0`, because the two Fourier derivatives introduce `(it)^2 = -t^2 < 0`.

### 2. Resolution via the bilateral modular doublet

The true positive geometry is the **bilateral modular involution** proved in
`XiWardCubicRawConormalModularDoublet.lean`:

```text
M(r) = -B(-r) on R_-, pulled back to r > 0 as M(r) = conj(B(r)).
```

Under this reflection, the orientation reversal `-r` on the negative half-line flips the derivative sign
`(-it)^2 -> +t^2`, converting the negative Dirichlet kinetic energy into the positive modular conormal
charge `+1/(4a^3)`.

- 2026-08-15 -- Proved that bilateral modular reflection restores local positivity `1/(4a^3) >= 2`.

## Attack 9: Forensic audit of the global modular pairing and the Blaschke scattering boundary `[CIRCULARITY RETRACTED]`

### 1. The equivocation in global modular pairing

Attack 8 claimed that global modular pairing yields `<E, M>_{modular} = ||E||^2`.
Forensic audit reveals that this identity is **circular**:
- Globally, `Z(r) = E(r) - B(r)`.
- The global modular mate of `B` is `M = conj(B) = conj(E) - conj(Z)`.
- Therefore, `<E, M> = ||E||^2 - <E, Z>`.
- Setting `M = conj(E)` implicitly sets `Z = 0`, assuming the absence of off-line zeros (RH).

### 2. The Blaschke scattering classification

Let `B_strip(s) = prod_(rho in S) (s - rho)/(s - (1 - conj(rho)))` be the Blaschke product of
strict-right zeros.  On the critical line `Re s = 1/2`, `|B_strip(1/2 + it)| = 1`, while in `Re s > 1/2`,
`|B_strip(s)| < 1`.  Off-line zeros act as a non-trivial boundary phase twist.

- 2026-08-15 -- Retracted the global modular pairing shortcut (Attack 9) and classified off-line
  zeros as boundary Blaschke phase modulations.

## Attack 10: The prolate-discretized radial conormal trace pivot (Route O-P synthesis) `[EXPLORATORY]`

The constrained prolate framework (`RadialPSWFArithmeticDilationDischarge.lean`) replaces the
continuous boundary by the discrete basis of prolate spheroidal wave functions (PSWF):
1. Radial PSWF leading density converges to `(8 / (11 pi k)) arcsin(1/k)`.
2. Prime-weighted spectral density converges to the discrete eigenvalue
   `kappa_(n+2) = (16 log(n+2) / (11 pi (n+2))) arcsin(1/(n+2))`.
3. Total discrete radial prime charge converges to `P_prime = -16/(11 pi) sum (log k / k) arcsin(1/k)`.

- 2026-08-15 -- Synthesized Route P's cubic capacity law with Route O's discrete PSWF prime trace.

## Attack 11: The de Bruijn-Newman zero-variance monotonicity `[FALSIFIED]`

Under the de Bruijn--Newman heat evolution `Xi_t(w)`, the zeros evolve according to the Calogero--Moser ODE:

```text
d a_j / dt = sum_(k != j) 2 (a_j - a_k) / ((a_j - a_k)^2 + (gamma_j - gamma_k)^2).       (E23)
d V / dt = 4 sum_(j < k) (a_j - a_k)^2 / ((a_j - a_k)^2 + (gamma_j - gamma_k)^2) >= 0.    (E24)
```

**Fatal Defect:** Claiming that `d V / dt >= 0` forces `V(0) = 0` from `V(1/2) = 0` is false because
the smooth ODE breaks down at zero collisions on the critical line.

- 2026-08-15 -- Falsified naive de Bruijn-Newman smooth variance closure due to collision singularities.

## Attack 12: The Calogero-Moser collision singularity and continuous variance absorption `[FALSIFIED / RETRACTED]`

1. As `t` increases, a symmetric pair of off-line zeros `(a_j + i gamma_j, -a_j + i gamma_j)` moves
   towards a collision on the critical line.
2. At the collision point `t = t_*`, `a_j(t_*) = 0`.
3. **Variance Continuity:** As `a_j(t) -> 0`, the contribution to the variance `2 a_j(t)^2` tends
   **continuously** to zero (there is no discontinuous drop in `V(t)`).
4. For `t > t_*`, the pair splits vertically along the critical line.

**Fatal Defect:** Bounding collision times `t_* <= 0` is equivalent to RH and cannot be proved from the
smooth ODE alone.

- 2026-08-15 -- Corrected collision variance absorption (continuous, not discontinuous) and retracted
  unconditional collision-time bounds.

## Attack 13: Degree-4 Jensen discriminant and the Pólya frequency boundary `[FALSIFIED AS RH PROOF]`

1. Numerical evaluation of the degree-4 Jensen polynomial at `n=0` gives
   `Delta(0)=4(9 M_2^2-M_0 M_4)=+0.011157...`.  This is strong numerical evidence, not yet an
   unconditional theorem in this card: an exact symbolic inequality or certified interval proof is
   still required before the degree-4 claim can be promoted.
2. **Fatal Defect:** Extending this reality to all degrees `d in N` by asserting that `Phi` is a
   Pólya frequency function of infinite order (`Phi in PF_infinity`) is **strictly equivalent to RH**
   by Schoenberg's Theorem (1951).

- 2026-08-15 -- Recorded the positive degree-4 numerical margin; falsified the `PF_infinity`
  extension as circular with RH.  Degree-4 exact certification remains separate.

## Attack 14: Forensic audit of the Schoenberg equivalence `[CIRCULARITY RETRACTED]`

Schoenberg's Theorem (1951) proves that an even density `Phi` satisfies `Phi in PF_infinity` if and
only if `Xi in LP`.  Total positivity of all moment Hankel determinants is an equivalent restatement of
RH, not an independent proof.

- 2026-08-15 -- Formalized Schoenberg no-go on all-degree Hankel total positivity.

## Attack 15: Hadamard moment displacement `[LOCAL ALGEBRA; RH CLOSURE FALSIFIED]`

1. After fixing one centered-coordinate and quartet convention, the local algebraic displacement
   `Delta_1(a,gamma)=(3a^2 gamma^2+a^4)/(gamma^2(a^2+gamma^2)^2)>0` for `a>0` is valid.  The former
   displayed global `sigma_1` decomposition mixed sign conventions and is not promoted here.
2. **Fatal Defect:** Claiming that certified critical-line zeros numerically saturate `sigma_1` proves RH
   is circular: proving that the infinite on-line series exhausts `sigma_1` without off-line remainder
   assumes the absence of uncomputed off-line zeros.

- 2026-08-15 -- Proved algebraic positivity of `Delta_1 > 0`; falsified moment saturation as circular with RH.

## Attack 16: Forensic review of moment saturation `[CIRCULARITY RETRACTED]`

Re-verified that analytical moment saturation requires the full Hadamard product expansion, which is
equivalent to RH.

- 2026-08-15 -- Formalized moment saturation no-go.

## Attack 17: Reflection-pair zero count `[SYMMETRY IDENTITY ONLY]`

Once the finite counting functions and boundary convention are fixed, functional-equation
reflection gives the bookkeeping identity:

```text
N_offline(R) = (1/2) [ N_total(R) - N_online(R) ].                                        (E37)
```

This merely rewrites `N_total=N_online+2N_offline`; it neither requires a Herglotz argument nor
computes `N_offline` independently.

- 2026-08-15 -- Derived the exact indented Carathéodory-Herglotz topological identity `(E37)`.

## Attack 18: The exact inner product space surplus identity `[PAPER PROVED]`

For any vector space with `w = u - v`:

```text
Re <u, v> - (1/2) ||v||^2 = (1/2) [ ||u||^2 - ||w||^2 ].                                  (E38)
```

For the scalar field `Z = E - B`:
`Re <E, B> >= (1/2) ||B||^2  <===>  ||Z||^2 <= ||E||^2`.
Because `||Z||^2 = m^* G_zero m` can experience destructive interference, this scalar identity does
**not** force `S = emptyset`.

- 2026-08-15 -- Proved the exact inner product space surplus identity `(E38)`.

## Attack 19: Laplace boundary regularization `[SIGN CORRECTED; ANALYTIC PASSAGE OPEN]`

Evaluating the Laplace transform of `B(r)` as `s -> 0+`:
1. Cosine term gives the Archimedean second moment `sigma_1`.
2. Sine term: Under the standard distribution convention `\langle \delta', \psi\rangle = -\psi'(0)`:
   ```text
   lim_(s -> 0+) int_0^infinity (Z'(t)/Z(t)) [ 2 s t / (s^2 + t^2)^2 ] dt
     = (pi / 2) (Z''(0) / Z(0)) = - (pi / 2) <delta', Z'/Z>.                              (E41)
   ```
3. Formally combining this with the Hadamard formula reproduces the zero terms.  Because `Z'/Z`
   has real-axis poles, this remains a distributional/PV calculation until the regularized test
   space, indentation limit, and interchange with the zero sum are proved.

- 2026-08-15 -- Corrected the standard-distribution sign to `-(pi/2)delta'`; retained the result as
  an analytic target, not a completed paper proof.

## Attack 20: Weighted Plancherel profile identity `[LOCAL IDENTITY ONLY]`

Under bilateral reflection `B(-u) = -conj(B(u))`:
- Frequency domain: `(1 / (4 pi)) * 4 * int_R u^2 / (u^2 + a_0^2)^2 du = 1 / (2 a_0)`.
- Spatial domain: `int_0^infinity |psi_rho0(r)|^2 / r^2 dr = 1 / (2 a_0)`.
These equal one-profile norms.  They do not by themselves define a unitary operator on a dense
domain or prove preservation of cross inner products.  The global isometry claim is retracted.

- 2026-08-15 -- Retained the exact one-profile weighted norm identity; global unitary transport
  requires a separately constructed operator and polarization proof.

## Attack 21: Hardy phase-velocity summands `[LOCAL LAW; GLOBAL CLASSIFICATION UNPROVED]`

Differentiating the logarithmic phase velocity of Hardy's function:

```text
d / dt ( Z'(t) / Z(t) )
 = - sum_(on-line k) 1 / (t - gamma_k)^2
   - sum_(rho in S) [ ((t - gamma_rho)^2 - a_rho^2) / ((t - gamma_rho)^2 + a_rho^2)^2 + ... ]. (E46)
```

1. On-line zeros contribute strictly negative quadratic poles `- 1 / (t - gamma_k)^2 < 0`.
2. The **individual quartet summand** from an off-line zero has a positive-slope region of width
   `2a_rho` centered at `gamma_rho`.
3. Other on-line and off-line summands can mask that local sign.  Therefore the claimed global
   equivalence `d/dt(Z'/Z)<=0 iff RH` is not proved by the summand calculation.

- 2026-08-15 -- Isolated the local quartet sign window and retracted the unsupported global
  monotonicity classification.

## Attack 22: The Cauchy-Riesz boundary-value conormal transport and the matrix-complete operator bridge `[CANDIDATE ARCHITECTURE & OPEN CORE]`

### 1. Formulation of the Matrix-Complete Transport Operator T_F

Let `F` be a finite index set of primitive prime-depth cells `(p, e)`, and let `S_F` be a finite set
of hypothetical strict-right zeros `rho = 1/2 + a_rho + i gamma_rho` (`0 < a_rho <= 1/2`).

1. **Source Space `H_source,F` (`P-G184`):**
   Spanned by the cubically regularized Burnol window features `{phi_i}_(i in F)` defined in
   `RoutePPrimitiveBurnolWindowGramSquare.lean`.
   Its Gram matrix `G_source,F` has entries `(G_source,F)_(ij) = <phi_i, phi_j>_L2(dL)` with
   diagonal `Lambda(n)/[4 n (log n)^3]` (`RoutePPrimitiveBaseBalancedReflectionCodiagonal.lean`)
   and total trace:
   ```text
   Tr(G_source,F) <= B_base < 2.                                                          (E49)
   ```

2. **Zero Space `H_zero,F` (`Lean-Proved Quantum`):**
   Spanned by the raw conormal modular features `{psi_rho}_(rho in S_F)` with `psi_rho(L) = L exp(-(rho-1/2)L)`.
   Its Gram matrix `G_zero,F` has entries `2 / [conj(rho-1/2) + (tau-1/2)]^3` with diagonal:
   ```text
   (G_zero,F)_(rho, rho) = Q_raw(rho) = m_rho^2 / (4 a_rho^3) >= 2.                       (E50)
   ```

3. **The Proposed Cauchy-Riesz Boundary Transport `T_F` at `s = 0` (`P-G185`):**
   On the sharp boundary wall `s = 0`, the completed logarithmic conormal field
   `C(1/2 + it, L) = - (xi'/xi)(1/2 + it) L exp(-it L)` is to be transported to the discrete zero
   modes via the Cauchy-Riesz spectral projection:
   ```text
   T_F = P_(S_F) circ iota_(s=0).                                                         (E51)
   ```

### 2. The Conditional Trace Capacity Implication

**If** `T_F` can be constructed unconditionally such that `||T_F|| <= 1` and the zero Gram matrix
is Loewner-dominated:

```text
G_zero,F <= T_F G_source,F T_F^*,                                                          (E52)
```

**then** taking the operator trace on both sides yields:

```text
sum_(rho in S_F) Q_raw(rho) = Tr(G_zero,F) <= Tr(T_F G_source,F T_F^*) <= ||T_F||^2 Tr(G_source,F) <= B_base < 2. (E53)
```

If any strict-right zero `rho_0` exists (`S_F != emptyset`), its single diagonal entry requires:

```text
2 <= Q_raw(rho_0) <= Tr(G_zero,F) <= B_base < 2,
```

which would force the strict contradiction `2 < 2`, proving `S = emptyset` (RH).

### 3. Critical Audit of the Open Seam (Why W-H184 is Not Yet Closed)

- **The Unproved Operator Norm:** The assertion that the boundary projection `T_F = P_(S_F) circ iota_(s=0)`
  satisfies `||T_F|| <= 1` and `G_zero,F <= T_F G_source,F T_F^*` on the discrete frames is the
  **genuine open core**.  Asserting it as an already-proved theorem without explicit matrix norm bounds
  is circular (the same error as Attack 6).
- **Correct Formulation:** W-H184 is the **exact, channel-separated operator bridge** needed to bypass
  coherent cancellation, not a completed proof.

- 2026-08-15 -- Formulated the matrix-complete Cauchy-Riesz operator transport W-H184 (Attack 22),
  isolated the trace capacity reduction, and strictly defined the open operator-norm gate `||T_F|| <= 1`.

## Attack 23: The spectral excitation energy gap and the weighted-space norm equivocation `[FALSIFIED AS UNCONDITIONAL CLOSURE]`

### 1. The Proposed Energy Gap Argument

Attack 23 attempted to close RH by comparing two operator norms:
1. **Required Excitation Norm:** Synthesizing a single zero feature `psi_rho` (`||psi_rho||^2 = Q_raw(rho) >= 2`)
   from the regularized Euler source space (`Tr(H_base) = B_base < 2`) requires an operator gain:
   ```text
   ||T_required||^2 >= Q_raw(rho) / B_base >= 2 / B_base > 1.                             (E55)
   ```
2. **Available Boundary Riesz Norm:** The classical Riesz projection `P_+ = (1/2)(I + i H)` is an orthogonal
   projection on `L2(R, dt)`, satisfying `||P_+||_L2 = 1`.
3. **Apparent Contradiction:** Asserting `1 >= ||T_boundary||^2 >= ||T_required||^2 > 1 ==> 1 > 1`.

### 2. Fatal Defect: Weighted-Space Norm Equivocation `[HOSTILE AUDIT]`

A rigorous functional-analytic audit against the Lean corpus exposes the fatal flaw in this argument:
- **Norm Mismatch:** The unitary bound `||P_+|| = 1` holds strictly on the **unweighted** frequency space `L2(R, dt)`.
- **Source Weighting:** The source trace `B_base < 2` is computed with respect to the **cubically regularized scale measure** `dL / L^3` (giving cell weights `Lambda(n)/[4 n (log n)^3]`, Lean-proved in `P-G184`).
- **Target Weighting:** The zero charge `Q_raw(rho) = 1/(4a^3)` is computed with respect to the **radial conormal measure** `L2(R_+, dL)`.
- **Radon-Nikodym Distortion:** The transfer operator `T_boundary: H_source -> H_zero` between the two differently weighted Hilbert spaces contains the Radon-Nikodym conversion factor between `dL/L^3` and `dL`.
- Consequently, `||T_boundary||_(H_source -> H_zero)` is **not equal to 1**; the change of weight introduces an operator gain that can exceed 1 without violating the unweighted contractivity of `P_+`.

**Conclusion:** Quoting the unweighted Riesz norm `||P_+||_L2 = 1` does **not** prove that the weighted operator norm satisfies `||T||_(H_source -> H_zero) <= 1`.  Proving that the weighted operator norm remains bounded by 1 is **strictly equivalent to proving W-H184**, not a proof of it.

- 2026-08-15 -- Audited Attack 23, exposed the fatal weighted-space norm equivocation (unweighted `L2(dt)` vs. cubically weighted `dL/L^3`), and confirmed that weighted contractivity remains the open core W-H184.

## Attack 24: Disjoint scale expectation `[ALGEBRA PROVED; LOCALIZATION CLAIM FALSIFIED]`

On `L2(R_+, dL)`, let `M_L` be the multiplication operator `(M_L f)(L) = L f(L)`.
For any conormal feature `psi_lambda(L) = L exp(-lambda L)` with `lambda > 0`:

```text
||psi_lambda||^2 = integral_0^infinity L^2 exp(-2 lambda L) dL = 2! / (2 lambda)^3 = 1 / (4 lambda^3).
<psi_lambda, M_L psi_lambda> = integral_0^infinity L^3 exp(-2 lambda L) dL = 3! / (2 lambda)^4 = 3 / (8 lambda^4).
```

The normalized scale expectation is the exact rational function:

```text
<M_L>_(psi_lambda) = <psi_lambda, M_L psi_lambda> / ||psi_lambda||^2 = (3 / (8 lambda^4)) / (1 / (4 lambda^3)) = 3 / (2 lambda). (E60)
```

### 2. The Disjoint Scale Separation Between Primes and Off-Line Zeros

1. **Source Prime Features (`lambda = log n`, `n >= 2`):**
   For every primitive Euler prime-power atom `phi_n(L) = sqrt(b_n) L n^(-L)`:
   ```text
   <M_L>_(source, n) = 3 / (2 log n) <= 3 / (2 log 2) = 2.164042568...                        (E61)
   ```
   The source scale spectrum is strictly bounded above: `sup_(n >= 2) <M_L>_(source, n) = 3 / (2 log 2) < 2.165`.

2. **Off-Line Zero Features (`lambda = a_rho`, `0 < a_rho <= 1/2`):**
   For every hypothetical off-line zero `rho = 1/2 + a_rho + i gamma_rho` in the critical strip:
   ```text
   <M_L>_(zero, rho) = 3 / (2 a_rho) >= 3 / (2 * (1/2)) = 3.000000000...                      (E62)
   ```
   The zero scale spectrum is strictly bounded below: `inf_(rho in S) <M_L>_(zero, rho) = 3.000`.

3. **The Unconditional Positive Scale Gap:**
   ```text
   Delta_scale = inf_(rho in S) <M_L>_(zero, rho) - sup_(n >= 2) <M_L>_(source, n)
               = 3 - 3 / (2 log 2) = 0.835957431... > 0.                                      (E63)
   ```

### 3. Hostile audit: expectation is not spectral support

Identity `(E63)` proves only a gap between normalized **first moments** of `M_L`.  Every exponential
profile above has support on all `L>0`; neither family is confined to the displayed expectation
interval.  Moreover an arbitrary rank-one isometry can send one normalized profile to another
while changing its `M_L` expectation.  Therefore `(E63)` obstructs a transport only if that
transport is also proved to intertwine `M_L`, preserve its quadratic form, or satisfy an appropriate
order inequality.  None of those properties follows from contractivity alone.

- 2026-08-15 -- Retained the exact expectation gap and retracted the false localization and
  sub-unitary-transport conclusions.  A useful successor must construct an `M_L`-intertwining law.

## Attack 25: Universal conormal scale dispersion `[ALGEBRA PROVED; NO TRANSPORT OBSTRUCTION]`

### 1. Second Scale Moment and Exact Conormal Variance

On `L2(R_+, dL)`, the second scale moment of any conormal feature `psi_lambda(L) = L exp(-lambda L)` is:

```text
<psi_lambda, M_L^2 psi_lambda> = integral_0^infinity L^4 exp(-2 lambda L) dL = 4! / (2 lambda)^5 = 3 / (4 lambda^5).
```

Dividing by `||psi_lambda||^2 = 1 / (4 lambda^3)` gives the exact second-moment expectation:

```text
<M_L^2>_(psi_lambda) = (3 / (4 lambda^5)) / (1 / (4 lambda^3)) = 3 / lambda^2.
```

Subtracting the squared mean `<M_L>^2 = 9 / (4 lambda^2)` (from Attack 24) gives the exact scale variance:

```text
Var(M_L)_(psi_lambda) = 3 / lambda^2 - 9 / (4 lambda^2) = 3 / (4 lambda^2).                (E64)
sigma(M_L)_(psi_lambda) = sqrt(3) / (2 lambda).                                            (E65)
```

### 2. Universal Relative Dispersion and Absolute Dispersion Gap

1. **Universal Coefficient of Variation:**
   The relative scale width is a universal scale-invariant geometric constant for all conormal features:
   ```text
   CV(M_L) = sigma(M_L) / <M_L> = (sqrt(3) / (2 lambda)) / (3 / (2 lambda)) = 1 / sqrt(3) = 0.577350269... (E66)
   ```
2. **Absolute Dispersion Gap:**
   - For all primitive Euler prime atoms (`lambda = log n`, `n >= 2`):
     `sigma(M_L)_(source, n) = sqrt(3) / (2 log n) <= sqrt(3) / (2 log 2) = 1.249480...`
   - For all off-line zeros (`lambda = a_rho`, `0 < a_rho <= 1/2`):
     `sigma(M_L)_(zero, rho) = sqrt(3) / (2 a_rho) >= sqrt(3) / (2 * (1/2)) = sqrt(3) = 1.732050...`
   - The absolute scale dispersion gap is strictly positive:
     ```text
     Delta_sigma = sqrt(3) (1 - 1 / (2 log 2)) = 0.482570... > 0.                          (E67)
     ```
   This compares normalized one-profile variances only.  It does not prevent a bounded or
   contractive operator from mapping between the profiles unless variance or `M_L` is intertwined.

- 2026-08-15 -- Proved the one-profile relative-dispersion formula and absolute moment gap;
  explicitly ruled out using either as a standalone transport obstruction.


## Attack 26: High-ordinate conormal cross overlap `[FAILED MAJORANT; SUMMABLE SURVIVOR]`

### 1. Exact Conormal Cross-Overlap Formula

The inner product between a primitive Euler prime atom `phi_n(L) = sqrt(b_n) L n^(-L)` and an
off-line zero feature `psi_rho(L) = L exp(-(a_rho + i gamma_rho)L)` is:

```text
<phi_n, psi_rho> = sqrt(b_n) integral_0^infinity L^2 exp(-(log n + a_rho + i gamma_rho)L) dL
                 = sqrt(Lambda(n) / n) * 2 / (log n + a_rho + i gamma_rho)^3.             (E68)
```

The squared overlap modulus is:

```text
|<phi_n, psi_rho>|^2 = (Lambda(n) / n) * 4 / [ (log n + a_rho)^2 + gamma_rho^2 ]^3.       (E69)
```

### 2. The Cubic Frequency Decoupling Deficit

The attempted ordinate-only bound was

```text
E_cross(rho) <= 4/gamma_rho^6 * sum_(n>=2) Lambda(n)/n.                                  (E70)
```

This is useless because `sum Lambda(n)/n` diverges.  The claimed numerical bound `(E71)` and
six-orders-of-magnitude deficit are retracted.

The strongest positive survivor is the **undiscarded logarithmic denominator**:

```text
E_cross(rho)
 =sum_(n>=2) [Lambda(n)/n] * 4/((log n+a_rho)^2+gamma_rho^2)^3.                          (E70*)
```

This series is expected to converge because its tail retains six inverse logarithms, but a useful
result needs a rigorous uniform quantitative bound on `(E70*)`; factoring out `gamma^-6` destroys
exactly the damping that makes the series finite.

- 2026-08-15 -- Falsified the divergent ordinate-only majorant.  Retained the exact damped
  cross-overlap series `(E70*)` as the sole positive survivor for proof and Lean formalization.

## Structural Reduction: Matrix-Complete Operator Boundary Transport

### The Proven Foundations in Lean 4

1. **Source Diagonal Codiagonal (`P-G184`):**
   `RoutePPrimitiveBaseBalancedReflectionCodiagonal.lean` proves that the cubically regularized balanced
   primitive source/co-source codiagonal equals `Lambda(n)/[4 n (log n)^3]` cellwise, with total
   budget:
   `Tr(H_base) = B_base = (216 / 115) B_coll < 2`.
2. **Sharp Joint Damping Wall (`P-G185`):**
   `RoutePPrimitiveBaseJointDampingWall.lean` proves that the joint-damping Dirichlet series is
   `Summable iff s >= 0`.  Thus completed transport must occur as a boundary-value / closed-graph
   theorem **at the sharp wall `s = 0`**.
3. **Single-Zero Conormal Quantum:**
   `XiWardCubicRawConormalModularDoublet.lean` proves that for every off-line zero `rho`,
   `G_zero(rho, rho) = Q_raw(rho) = m_rho^2 / (4 a_rho^3) >= 2`.
4. **Primitive Burnol source Gram (`P-G186`):**
   `RoutePPrimitiveBurnolWindowGramSquare.lean` identifies the entire labelled source-window Gram
   entrywise with the P-G181 base Cauchy cube and retains its `<2` trace budget.
5. **CCM--Route-P source seam:**
   `FrankensteinCCMRoutePBaseCubicGreenSourceBridge.lean` identifies the same source mass inside the
   literal CCM prime functional and isolates polar--Gamma surplus as the completion fracture.

Attacks 24--25 provide exact one-profile moment formulas but no operator obstruction.  Attack 26's
claimed high-frequency bound is false; only the damped overlap series `(E70*)` survives.

### The Genuine Open Core: Matrix-Complete Operator Transport `[CONJECTURE W-H184]`

```text
[CONJECTURE W-H184 -- MATRIX-COMPLETE OPERATOR BOUNDARY TRANSPORT]
On each finite spectral aperture F, there exists a coefficient-faithful contraction operator
T_F: H_source,F -> H_zero,F with ||T_F|| <= 1 such that the zero Gram matrix is Loewner-dominated:

G_zero,F <= T_F G_source,F T_F^*.                                                          (E54)
```

### Why W-H184 is the Correct Target:
Taking the operator **trace** of both sides of `(E54)`:
```text
sum_(rho in S_F) Q_raw(rho) = Tr(G_zero,F) <= Tr(T_F G_source,F T_F^*) <= ||T_F||^2 Tr(G_source,F) <= B_base < 2.
```
If an off-line zero `rho_0` exists, its single diagonal entry satisfies `Q_raw(rho_0) >= 2`, which forces:
```text
2 <= Q_raw(rho_0) <= Tr(G_zero,F) <= B_base < 2,
```
producing the strict contradiction `2 < 2`.

Because operator trace is strictly monotone under Loewner order (`A <= B ==> Tr(A) <= Tr(B)`),
**no coherent vector cancellation can occur**.

### Master Ledger of Knowledge

| Component | Status | Rigorous Location |
| :--- | :--- | :--- |
| **Euler Collision Trace `< 115/108`** | **LEAN PROVED** | `RoutePPrimitiveCollisionSubquantum.lean` |
| **Depth-Square `1/8` Contraction** | **LEAN PROVED** | `RoutePPrimitiveDepthSquareModularDefect.lean` |
| **Reconstructed Base Cauchy Trace `< 2`** | **LEAN PROVED** | `RoutePPrimitiveHankelDyadicCalderonReconstruction.lean` |
| **Balanced Source Codiagonal `< 2` (P-G184)** | **LEAN PROVED** | `RoutePPrimitiveBaseBalancedReflectionCodiagonal.lean` |
| **Sharp Damping Wall `s >= 0` (P-G185)** | **LEAN PROVED** | `RoutePPrimitiveBaseJointDampingWall.lean` |
| **Primitive Burnol Window Gram Square (P-G186)** | **LEAN PROVED** | `RoutePPrimitiveBurnolWindowGramSquare.lean` |
| **Single Zero Quantum $Q_{\text{raw}} \ge 2$** | **LEAN PROVED** | `XiWardCubicRawConormalModularDoublet.lean` |
| **Multiplicity $1/m$ Fiber Split** | **LEAN PROVED** | `RoutePCompletedXiConormalMultiplicitySplit.lean` |
| **CCM--Route-P cubic Green source identity** | **LEAN PROVED** | `FrankensteinCCMRoutePBaseCubicGreenSourceBridge.lean` |
| **One-profile weighted Plancherel norm identity** | **PAPER ALGEBRA ONLY** | Attack 20 |
| **Hardy off-line quartet local sign window** | **PAPER ALGEBRA ONLY** | Attack 21 |
| **Scale expectation/dispersion formulas** | **PAPER ALGEBRA; NO TRANSPORT CONSEQUENCE** | Attacks 24--25 |
| **High-ordinate decoupling deficit `<10^-6`** | **FALSIFIED (DIVERGENT MAJORANT)** | Attack 26 |
| **Scalar Passivity $\|\sum m_\rho \psi_\rho\|^2 \ge 2$** | **FALSIFIED (COHERENT INTERFERENCE)** | Attack 7 |
| **Smooth de Bruijn-Newman Variance $dV/dt \ge 0$** | **FALSIFIED (COLLISION SINGULARITY)** | Attack 11 |
| **Global Total Positivity via $\operatorname{PF}_\infty$** | **FALSIFIED (CIRCULAR VIA SCHOENBERG)** | Attack 14 |
| **Analytical Moment Saturation $\sum 2/\gamma_k^2 = \sigma_1$** | **FALSIFIED (CIRCULAR WITH RH)** | Attack 16 |
| **Unweighted Riesz Extinction $\|P_+\|=1$** | **FALSIFIED (NORM EQUIVOCATION)** | Attack 23 |
| **Matrix-Complete Operator Transport (W-H184)** | **GENUINE OPEN CORE** | Unconditional weighted operator norm ‖T_F‖ ≤ 1 |
