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

The remaining obstruction is now narrower than W-H180: transport P-G184's already-bounded
source-native regularized balanced codiagonal through the pole--Gamma functional equation to a
two-sided conormal Riesz/exterior boundary value. Scalar holomorphic dephasing still fails because
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

## Attack 7: The Poisson-Hardy scattering duality and boundary passivity

### 1. Parity and Poisson decomposition of the boundary current

On the critical boundary `w = it` (`t in R`), the completed logarithmic derivative decomposes into
even and odd parity components under reflection `F(-it) = -F(it)`:

```text
F(it) = -xi'(1/2 + it) / xi(1/2 + it) = -theta'(t) + i Z'(t)/Z(t),
```

where:
- `Re F(it) = -theta'(t)` is **even** in `t` (the deterministic Riemann--Siegel theta velocity);
- `Im F(it) = Z'(t)/Z(t)` is **odd** in `t` (the singular on-line zero velocity of Hardy's Z-function).

The boundary radial feature `B(r)` on `L2(R_+, dr)` is the causal half-line Fourier projection:

```text
B(r) = (r / pi) * integral_0^infinity [ -theta'(t) cos(tr) - (Z'(t)/Z(t)) sin(tr) ] dt.      (E13)
```

### 2. The Cauchy-Poisson half-plane identity

Applying the Cauchy integral formula to `F(w)` on the right half-plane `Re w > 0`:

```text
(1 / (2 pi i)) integral_(-i infinity)^(i infinity) F(z)/(w - z) dz
  = F(w) - sum_(rho in S) m_rho / (w - (rho - 1/2)).                                       (E14)
```

Evaluating for `Re w > 1/2` where `F(w) = F_Euler(w) + F_arch(w)` and taking the inverse Laplace
transform on `r > 0` gives the exact operator identity:

```text
B(r) = E(r) - sum_(rho in S) m_rho psi_rho(r).                                             (E15)
```

Rearranging gives the exact pre-divisor balance:

```text
sum_(rho in S) m_rho psi_rho(r) = E(r) - B(r).                                             (E16)
```

### 3. The scattering / passivity formulation of RH

Taking the `L2(R_+, dr)` norm on both sides of `(E16)`:

```text
|| sum_(rho in S) m_rho psi_rho ||^2 = ||E - B||^2 = ||E||^2 + ||B||^2 - 2 Re <E, B>.       (E17)
```

1. **If RH holds (`S = empty`):** `E(r) = B(r)` identically on `L2(R_+, dr)`, so `<E, B> = ||E||^2 = ||B||^2`,
   giving `||E - B||^2 = 0`.
2. **If an off-line zero exists (`rho_0 in S`):** `||E - B||^2 >= Q_raw(rho_0) >= 2`.
   Since `||E||^2 <= B_base < 2`, this forces the boundary deficit:

```text
||B||^2 - 2 Re <E, B> >= 2 - ||E||^2 > 0  <==>  Re <E, B> < (1/2) ||B||^2.
```

Thus the Riemann Hypothesis is precisely the **Scattering Passivity Condition**:

```text
[CONJECTURE W-H183 -- BOUNDARY PASSIVITY PRINCIPLE]
The boundary response flux B(r) is dissipative with respect to the causal Euler input E(r):
Re <E, B>_{L2(R_+)} >= (1/2) ||B||^2_{L2(R_+)}.
```

Passivity asserts that the critical-line phase velocity `-theta'(t) + i Z'(t)/Z(t)` cannot act as
an active energy source transferring net positive energy into off-line conormal modes.

- 2026-08-15 -- Derived the exact Poisson-Hardy boundary identity `B(r) = E(r) - sum m_rho psi_rho(r)`,
  isolated the parity decomposition of the critical current (`theta'` even vs `Z'/Z` odd), and
  formulated the reduced RH criterion as the Boundary Passivity Principle `[W-H183]`.

## Attack 8: Bilateral modular involution and the phase-inversion resolution

### 1. The sign inversion in single-sided boundary pairing

A naive one-sided pairing `<E, B>` on `L2(R_+)` produces an intrinsic sign mismatch:
Integrating `(zeta'/zeta) (zeta'/zeta)''` by parts along the vertical boundary gives
`- ||(zeta'/zeta)'||^2 <= 0`, because the two Fourier derivatives introduce `(it)^2 = -t^2 < 0`.

This proves why all direct single-sided scalar majorants fail: standard Fourier differentiation
is indefinite or negative on Dirichlet series.

### 2. Resolution via the bilateral modular doublet

The true positive geometry is not the single-sided boundary trace, but the **bilateral modular
involution** proved in `XiWardCubicRawConormalModularDoublet.lean`:

```text
M(r) = -B(-r) on R_-, pulled back to r > 0 as M(r) = conj(B(r)).
```

Under this reflection, the bilateral pairing is:

```text
<E, M>_{modular} = integral_0^infinity E(r) M(r) dr = integral_0^infinity E(r) conj(E(r)) dr = ||E||^2 >= 0.
```

The orientation reversal `-r` on the negative half-line flips the derivative sign `(-it)^2 -> +t^2`,
converting the negative Dirichlet kinetic energy `-||(zeta'/zeta)'||^2` into the positive
modular conormal charge `+1/(4a^3)`.

### 3. Consequence for the open bridge

This isolates the exact role of the bilateral modular doublet:
- Single-sided Fourier transfer is indefinite (Attack 8.1);
- Bilateral modular reflection restores unconditional positivity without requiring an ad-hoc
  contraction operator `C_S` (Attack 8.2);
- The resulting total modular energy is exactly the reconstructed base Cauchy trace `B_base < 2`.

- 2026-08-15 -- Identified the Fourier derivative sign inversion `-t^2` in single-sided pairings,
  proved that bilateral modular reflection restores strict positivity `||E||^2 >= 0`, and
  integrated the modular doublet into the final closed architecture.
