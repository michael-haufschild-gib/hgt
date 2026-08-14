# Route P cubic Euler Hankel transpose and moment-polarity wall

- **ID:** `route-p-cubic-euler-hankel-transpose-moment-polarity`
- **Stage:** 1-in-progress
- **Type:** `[THEOREM (paper)] [FALSIFIED LINEAR SUCCESSOR] [OPEN NONLINEAR PRODUCER]`
- **Source:** `rh-current-frontier-map.md` · `Cubic Ward/Hellinger source-trace opening`
- **Statement:** The P-G174 primitive collision Gram completes to a canonical Hilbert--Schmidt
  Euler synthesis whose covariance is an explicit four-point finite difference of
  `-zeta'/zeta`; however, its subquantum trace is a third *negative* logarithmic moment, whereas
  a cubic divisor pole is produced by two *positive* logarithmic derivatives.  Linear
  one-variable continuation therefore cannot be the missing P-G176 producer.

## Goal

Replace the unnamed "completed coefficient-faithful incidence" in P-G176 by the earliest literal
pre-divisor operator supplied by the cubic source itself.  Then attack, rather than assume, the
claim that analytic continuation of this operator contracts onto the strict-right Xi collision
carrier.  Any surviving successor must explain how inverse logarithmic source moments become a
third-order Hermitian divisor singularity without inserting Xi copies or their norm.

This card does not assume a zero-side trace capacity law.  P-G176 already proves that law
equivalent to RH.

## Gates

- [x] 0 -> 1 in-progress: source-pure operator, exact attack, internal/external novelty sketch
- [ ] 1 -> 2 fully-proven: complete paper proof of every promoted theorem, `[PROVED HERE]`
- [ ] 2 -> 3 formalized: Lean theorem(s), targeted leaf checks/build, axiom/lint pass
- [ ] 3 -> 4 publication-ready: standalone theorem/proof/novelty certificate

## Exact primitive synthesis `[CONJECTURE P-G177-A] [PAPER PROOF COMPLETE]`

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
- **Strongest positive survivor:** P-G177-A constructs the first canonical completed pre-divisor
  operator in this lane.  A viable continuation must be nonlinear or genuinely two-variable
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

## Second successor conjecture

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

This is the first successor capable of crossing the moment-polarity wall.  It is currently open.
Existing diagonal Gamma--prime Fredholm operators realize reciprocal Gamma and reciprocal zeta
only in `Re s>1`; their prime branch ceases to be trace class at the critical boundary, and no
source theorem identifies their completed conormal second fundamental form with P-G173.

## Novelty and theatre audit

- P-G177-A is more than a renamed finite Gram: it constructs the infinite synthesis, identifies
  its transposed trace-class covariance with a literal four-point logarithmic-current kernel, and
  identifies the P-G174 budget with determinant-line free energy.
- P-G177-B is recorded as false, not used as an RH premise.
- P-G177-C is not counted as progress until a finite coefficient formula, graph domain, and
  nonexpansive curvature identity are proved independently of Xi zeros.
- Any construction defining its determinant, conormal range, norm, or negative subspace from the
  Xi divisor fails the source-purity gate.

## Lean targets after paper promotion

1. `RoutePPrimitiveCollisionHankelSynthesis.lean`: feature Gram, exact column norm, covariance
   finite-difference kernel, and trace identities.
2. `RoutePCubicMomentPolarityNoGo.lean`: derivative versus primitive coefficient law, local pole
   order, and divergence of the derivative-weight prime current.
3. Wire both completed leaf modules into `RHTower.lean`; run only scratch checks and targeted leaf
   builds, never the umbrella build.

## Log

- 2026-08-15 -- P-G177-A originated and paper-proved after complete Route-P/curvature/Deninger
  audit.  Linear Hankel continuation P-G177-B failed under exact moment-polarity attack.  Pivoted
  to determinant-line/closed-graph curvature P-G177-C.
