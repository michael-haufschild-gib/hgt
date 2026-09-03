# Cubic aperture-gauged Euler--continuum synthesis

- **ID:** ULF-CAGC-001
- **Stage:** 2-fully-proven
- **Type:** unconditional operator theorem
- **Parents:** `ULF-RUCRI-001`, `ULF-ETRS-001`
- **Purpose:** construct the operator-valued Gaussian continuum leg on the same Burnol carrier as
  literal Euler atoms.  Ordinary Hilbert synthesis diverges at continuum log-frequency zero;
  the third aperture defect is the minimal trace-class gauge.

## 1. The wall

Let

```text
H_B=L2((0,infinity),dr),
f_lambda(r)=r exp(-lambda*r),  lambda>0.
```

The exact Cauchy-cubic Gram is

```text
<f_lambda,f_mu>=2/(lambda+mu)^3,
||f_lambda||^2=1/(4*lambda^3).                         (CAGC.1)
```

This is the common Burnol radial feature already present in
`routePXiBaseConormalResidueFeature`.  Literal integers occupy the gapped set
`lambda=log n>=log 2`.  The Gaussian continuum zero-mode occupies every `lambda>=0`.  Therefore
the naive continuum field has nonintegrable Hilbert mass `d lambda/(4 lambda^3)` at zero.  A
negative Krein sign does not define an infinity-minus-infinity supertrace; regularization must
occur before formation of either covariance.

## 2. Canonical cubic aperture gauge

For `x,c>0`, define

```text
h_x(lambda)=exp(-pi*x*exp(2*lambda)),
d_c(lambda)=1-exp(-2*c*lambda),
g_(x,c,lambda)=sqrt(h_x(lambda))*d_c(lambda)^(3/2)*f_lambda.  (CAGC.2)
```

The exponent `3/2` is positive real functional calculus on the scalar label semigroup.  Its
squared multiplier is the third defect of Burnol energy damping.

Define the continuum synthesis

```text
A_(0,x,c) : L2((0,infinity),d lambda) -> H_B,
A_(0,x,c) a = integral a(lambda) g_(x,c,lambda) d lambda.      (CAGC.3)
```

For literal integer formation define, on `n>=2`,

```text
a_(n,x,c)
  = sqrt(Lambda(n)/n)*exp(-pi*x*n^2/2)
      *(1-n^(-2*c))^(3/2),
g_(E,x,c,n)=a_(n,x,c) f_(log n),
A_(E,x,c) : ell2({n>=2}) -> H_B.                       (CAGC.4)
```

The square root is only the Hilbert realization of the unsquared positive coefficient:
`a_n^2` contains `Lambda(n)/n`, not `Lambda(n)^2`.

## 3. Minimal trace-class theorem

**Theorem CAGC-A.** For every `x,c>0`, `A_(0,x,c)` is Hilbert--Schmidt and

```text
||A_(0,x,c)||_HS^2
  = (1/4) integral_0^infinity
      h_x(lambda)*d_c(lambda)^3/lambda^3 d lambda < infinity. (CAGC.5)
```

More generally, replacing the power `3` in the energy by an integer `q>=0` gives a finite
continuum Hilbert mass if and only if `q>=3`.  Cubic defect order is minimal.

**Proof.** Equation `(CAGC.1)` follows from

```text
integral_0^infinity r^2 exp(-(lambda+mu)r)dr=2/(lambda+mu)^3.
```

For `0<lambda<=1`,

```text
0<=d_c(lambda)<=2*c*lambda,
h_x(lambda)*d_c(lambda)^3/(4*lambda^3)<=2*c^3.
```

For `lambda>=1`, `d_c<=1`, while `h_x(lambda)` has double-exponential decay; even
`lambda^(-3)` alone is integrable.  This proves `(CAGC.5)`.

For minimality, continuity gives `h_x(lambda)>=h_x(0)/2>0` on a sufficiently small interval.
Also `1-exp(-2c lambda)>=c lambda` there.  The order-`q` integrand is therefore bounded below by
a positive multiple of `lambda^(q-3)`, which is nonintegrable exactly for `q<=2`.  QED.

**Theorem CAGC-B.** `A_(E,x,c)` is Hilbert--Schmidt and

```text
||A_(E,x,c)||_HS^2
 = (1/4) sum_(n>=2)
     Lambda(n)/n * exp(-pi*x*n^2)
       *(1-n^(-2*c))^3/log(n)^3
 <= B_base < 1.                                       (CAGC.6)
```

**Proof.** Apply `(CAGC.1)` at `lambda=log n`.  Both new multipliers lie in `[0,1]`; termwise
domination by `Lambda(n)/(4n log(n)^3)` and `ULF-RUCRI-001` give `(CAGC.6)`.  QED.

## 4. One matrix-complete graded carrier

Put the two label spaces in one domain and use the **row synthesis**

```text
A_(x,c)=[A_(E,x,c)  A_(0,x,c)] : ell2({n>=2}) directSum L2(d lambda) -> H_B,
J=diag(+1,-1).                                         (CAGC.7)
```

Both range covariances are now honest nuclear operators:

```text
K_E=A_E A_E*,
K_0=A_0 A_0*,
K_rel=A_(x,c) J A_(x,c)*=K_E-K_0 in S_1.              (CAGC.8)
```

The label Gram `A_(x,c)* A_(x,c)` retains all blocks.  In particular,

```text
<g_E(n),g_E(m)>
  = 2 a_n a_m/(log n+log m)^3,                         (CAGC.9)

<g_E(n),g_0(lambda)>
  = 2 a_n sqrt(h_x(lambda))d_c(lambda)^(3/2)
      /(log n+lambda)^3.                               (CAGC.10)
```

Distinct-prime and atomic--continuum entries are nonzero before supertrace.  Doubling by complex
conjugation gives the four-leg functional-equation carrier with grading
`diag(+,-,+,-)` required by `ULF-ETRS-001`.

**Theorem CAGC-C.** The four-leg cubic-gauged synthesis is Hilbert--Schmidt, its full Gram and
relative supercovariance are well-defined, and

```text
Str K_four=2*(Tr K_E-Tr K_0).                          (CAGC.11)
```

Every term in `(CAGC.11)` is finite separately.  Therefore anomaly subtraction is performed
inside a legitimate nuclear category, not by subtracting divergent scalar traces.

## 5. Interpretation

The two independently forced cubic laws are now on the same carrier:

```text
source continuum wall:
  lambda^(-3) requires third aperture-energy defect for nuclearity;

completed Hardy wall:
  S_2 projection displacement requires third odd power for nuclear integrality.
```

Thus cubic is not a frequently recurring exponent.  It is the minimal relative-completion grade
on both sides of formation:

```text
K_rel^(3)(x,c)  --missing cyclic transgression-->  mathsf T_D.
```

The left object is a prime-mixed, Gaussian atomic--continuum, nuclear source field.  The right
object is the formation-anchored integral--nuclear homotopy defect `ULF-FACHD-001`.

## 6. Exact remaining theorem

This card constructs the previously missing operator-valued continuum leg but does not prove
positive theta reduction.  `ULF-OCSE-001` proves that orthogonal shorting by its completed range
is impossible because that range is dense; `ULF-ZDIA-001` relocates the distinction to the
unbounded inverse graph norm; `ULF-MHPD-001` derives the minimal two-channel Hadamard carrier.
Required next law is therefore a coefficient-native bivariant cyclic boundary map on that derived
carrier.  `ULF-CFPO-001` proves that the relative covariance is orientation-even, so it cannot
produce `mathsf T_D` alone.  It must be paired with a source-derived reflection-odd
prime--Gamma/Maurer--Cartan current:

```text
tau_D : (K_rel^(3)(x,c),j_EG) -> mathsf T_D            (CAGC.12)
```

such that its positive reduced action satisfies

```text
0<=Tr mathsf T_D<=Tr K_E<=B_base<1.                   (CAGC.13)
```

`tau_D` may not discard `(CAGC.9)`--`(CAGC.10)`, use a divisor, assert positivity before four-leg
reduction, or quotient by the closed continuum output range.  Constructing it would close RH.

## 7. Literature boundary

Higher-order spectral-shift theory constructs trace formulas only after subtracting lower Taylor
jets; third-order formulas are available for Hilbert--Schmidt perturbations, and modern
resolvent-comparable theory determines higher shifts only modulo low-degree polynomial anomalies.
This supports the category—relative trace after lower-grade subtraction—but does not supply the
arithmetic multiplier `(CAGC.2)`, its sharp order-three threshold, or the Euler--continuum Gram.

Restricted Schatten Grassmannians have Fredholm-index components and weak symplectic structures
for `1<=p<=2`.  They provide the ambient geometry, not the coefficient-native boundary map
`(CAGC.12)`.

No located source combines Gaussian atomic-minus-continuum formation, Burnol aperture damping,
minimal cubic nuclear regularization, and a relative-index boundary character.

## 8. Hostile audit

1. A bare negative continuum leg is invalid: its covariance is not defined.
2. One or two energy defects remain nonintegrable.  Third order is sharp, not chosen to match the
   target after the fact.
3. Nuclearity of both source legs does not imply positivity of their difference.
4. The scalar supertrace does not determine the mixed Gram or the target index.
5. The cubic gauge acts on pre-divisor log-frequency labels and retains unsquared Euler
   coefficients.
6. The construction is not a bounded source-to-Xi landing.  The cyclic boundary map `(CAGC.12)`
   remains open.

## Status

Paper proof dependency-closed.  Lean formalization deferred by current read-only research phase.
