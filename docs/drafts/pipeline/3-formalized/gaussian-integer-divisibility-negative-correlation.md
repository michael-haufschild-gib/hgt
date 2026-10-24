# Gaussian integer mass has nonpositive coprime divisibility correlations

- **ID:** gaussian-integer-divisibility-negative-correlation
- **Stage:** 3-formalized
- **Type:** THEOREM; Lean 4 verified
- **Source:** TG Gaussian-correlation conjecture; the actual theta kernel's
  proved global log-concavity in `ThetaCuspKernelLogConcavity.lean`.
- **Scope:** a source-specific consequence of theta log-concavity. No external
  novelty claim; external searches and novelty checks excluded by instruction.

## Statement

For `sigma>=0` and `y>0`, define the literal integer Gaussian mass

```
Z_sigma(y) = sum_(n>=1) n^(-sigma) exp(-y n^2).
```

For arbitrary real `a,b>=1`, the literal masses satisfy

```
Z_sigma(y) Z_sigma(a^2 b^2 y)
  <= Z_sigma(a^2 y) Z_sigma(b^2 y).
```

This is the four-point log-concavity law in logarithmic scale. Together
with continuity and positivity it implies that
`t -> log Z_sigma(exp(2t))` is concave on the whole real line. The Lean
endpoint states the four-point law directly; it does not introduce a
separate `ConcaveOn` declaration for this equivalent reformulation.

Consequently, under the probability mass
`P_y(n)=n^(-sigma) exp(-y n^2)/Z_sigma(y)`, indicators of divisibility
by any two coprime positive natural numbers have nonpositive covariance.
This statement uses the same Gaussian integer measure for both events.
It does not replace the integers by independent prime variables.

## Paper proof

Write `Theta` for the actual Riemann theta kernel, with normalization

```
Theta(t) = exp(t/2) sum_(n>=1)
  (4 pi^2 n^4 exp(4t) - 6 pi n^2 exp(2t)) exp(-pi n^2 exp(2t)).
```

The corpus proves that `Theta` is positive and globally log-concave, and
that it and all derivatives decay faster than every exponential. These
are unconditional inputs about this particular source.

### 1. A positive Green representation

Let `Z_0(u)=sum_(n>=1) exp(-u n^2)`. Gaussian majorants justify two
derivatives on every compact subinterval of `u>0`. The source equation is

```
4u^2 Z_0''(u) + 6u Z_0'(u)
  = (pi/u)^(1/4) Theta((log(u/pi))/2).
```

Both `Z_0` and `u^(3/2) Z_0'` vanish at infinity, by their Gaussian series.
Integrating `(u^(3/2) Z_0'(u))'` from infinity, and then integrating once
more, gives

```
Z_0(y) = pi^(1/4)/2 * integral_(v=y)^infinity
  (y^(-1/2)-v^(-1/2)) v^(-3/4) Theta((log(v/pi))/2) dv.
```

All terms of this final integral are nonnegative. Equivalently,

```
Z_0(pi exp(2t)) = exp(-t/2) * integral_0^infinity
  (exp(w/2)-exp(-w/2)) Theta(t+w) dw.
```

### 2. The same positive representation for every power weight

Set `alpha=sigma/2`. For `alpha>0`, the gamma integral and Tonelli give

```
Z_sigma(y) = 1/Gamma(alpha) * integral_y^infinity
  (u-y)^(alpha-1) Z_0(u) du.
```

Insert the positive Green representation and exchange the two integrals
by Tonelli. The inner integral is

```
integral_y^v (u-y)^(alpha-1) (u^(-1/2)-v^(-1/2)) du
  = 1/(2alpha) * integral_y^v (z-y)^alpha z^(-3/2) dz.
```

This follows by writing the parenthesis as
`(1/2) integral_u^v z^(-3/2) dz` and applying Tonelli again. With
`y=pi exp(2t)` and `v=y exp(2w)`, the result is

```
Z_sigma(pi exp(2t))
  = pi^alpha/Gamma(alpha+1) * exp((sigma-1/2)t)
      * integral_0^infinity K_sigma(w) Theta(t+w) dw,

K_sigma(w) = exp(w/2) * integral_0^w
  (exp(2r)-1)^(sigma/2) exp(-r) dr,  w>0.
```

For `sigma=0` this is exactly the Green formula in step 1, since
`K_0(w)=exp(w/2)-exp(-w/2)` and `Gamma(1)=1`. Thus no singular gamma
factor is used at `sigma=0`.

The integrals are finite: `K_sigma(w)` is bounded by a polynomial times
an exponential on the positive ray, while `Theta(t+w)` decays faster
than every exponential. The gamma identity also verifies equality to
the literal, absolutely convergent integer series.

There is a uniform version which avoids a separate case at `sigma=0`.
Put `Q(y)=sum_(n>=1) n^2 exp(-y n^2)` and
`A(t)=integral_0^infinity exp(v/2) Theta(t+v) dv`. One integration
of the source equation gives

```
A(t) = (1/2) T_0(t)-T_0'(t)
     = 2pi exp(5t/2) Q(pi exp(2t)),
T_0(t) = exp(t/2) Z_0(pi exp(2t)).
```

For every `alpha>=0`, the ordinary gamma integral, now at `alpha+1`,
gives the positive identity

```
Gamma(alpha+1) Z_(2alpha)(y)
  = integral_0^infinity u^alpha Q(y+u) du.
```

Termwise integration is justified by Tonelli; the resulting series is
`Gamma(alpha+1)` times the convergent literal Gaussian mass. Substituting
`u=pi exp(2t)(exp(2r)-1)` gives directly

```
Z_(2alpha)(pi exp(2t))
  = pi^alpha/Gamma(alpha+1) exp((2alpha-1/2)t)
      * integral_0^infinity
          (exp(2r)-1)^alpha exp(-r/2) A(t+r) dr.
```

Thus only two successive causal integral compositions are required:
first the causal exponential against `Theta`, then the causal power
kernel against `A`. All their integrability conditions follow from the
displayed positive identities. This uniform representation is the one
used in the formalization.

### 3. Log-concavity of the integration kernel

On `r>0`, put
`f_sigma(r)=(exp(2r)-1)^(sigma/2) exp(-r)`. Its logarithmic derivative is

```
(log f_sigma)'(r) = sigma exp(2r)/(exp(2r)-1) - 1,
(log f_sigma)''(r) = -2sigma exp(2r)/(exp(2r)-1)^2 <= 0.
```

The positive primitive `F(w)=integral_0^w f_sigma(r) dr` is log-concave.
For completeness, decreasing `f'/f` gives, for `0<r<w`,
`f'(w) f(r) <= f(w) f'(r)`. Integrating and taking the lower endpoint
to zero gives `f'(w) F(w) <= f(w)(f(w)-f(0+)) <= f(w)^2`.
The limit is `f(0+)=0` when `sigma>0`, and `1` when `sigma=0`;
the derivative is integrable at zero in the former case. Hence
`(log F)''<=0`. Multiplication by `exp(w/2)` preserves log-concavity.
Extend `K_sigma` by zero to `w<=0`; its support is convex and the
extension remains log-concave in the multiplicative inequality sense.

An algebraic proof gives the same kernel property without differentiating
at the lower endpoint. For `x>0` and `a,b>=0`, the four-point difference
for `exp(2x)-1` is

```
(exp(2(x+a))-1)(exp(2(x+b))-1)
  -(exp(2x)-1)(exp(2(x+a+b))-1)
  = exp(2x)(exp(2a)-1)(exp(2b)-1) >= 0.
```

Nonnegative powers and exponential factors preserve this inequality.
The zero extension to the negative ray also preserves it. Finally,
`K_sigma` is the convolution of the causal exponential `exp(w/2)`
with the causal function `(exp(2w)-1)^(sigma/2) exp(-w/2)`.
Step 4 therefore proves its four-point inequality directly. This is
the route used in the formalization.

### 4. Positive convolution preserves the needed four-point inequality

The convolution of two nonnegative log-concave functions is log-concave
where finite. Here is the two-by-two proof needed here, so no sign or
regularity input is left implicit. A log-concave function `f` has

```
f(x1-u) f(x2-v) - f(x1-v) f(x2-u) >= 0
```

when `x1<=x2` and `u<=v`; this follows by adding the two concavity
inequalities for the inner points of an interval. For the convolution
kernel `C(x,y)=integral f(x-u) g(u-y) du`, expansion and Fubini give

```
2 det(C(x_i,y_j))_(i,j=1,2)
 = integral integral
   det(f(x_i-u_j))_(i,j=1,2)
   det(g(u_i-y_j))_(i,j=1,2) du dv.
```

The two determinants have the same sign whether `u<=v` or `v<=u`.
Their product is nonnegative. Absolute integrability follows by
expanding into the four products of the finite one-variable integrals.
The resulting four-point inequality is equivalent to log-concavity for
the positive continuous convolution in step 2. Reflection of an
argument preserves log-concavity, so the `Theta(t+w)` convention causes
no change. The positive constant and the exponential factor in step 2
also preserve log-concavity. Translating `t` removes the factor `pi`.

### 5. Literal divisibility events

For every positive integer `a`, reindexing multiples gives
`P_y(a|n)=a^(-sigma) Z_sigma(a^2 y)/Z_sigma(y)`.
For coprime `a,b`, the simultaneous event is divisibility by `ab`.
Its covariance is therefore

```
(ab)^(-sigma)/Z_sigma(y)^2 *
  (Z_sigma(y) Z_sigma(a^2 b^2 y)
    - Z_sigma(a^2 y) Z_sigma(b^2 y)),
```

which is nonpositive by the four-point inequality.

The inequality also iterates. If `d_1,...,d_k` are pairwise coprime
positive integers, then

```
P_y(d_1...d_k | n) <= product_i P_y(d_i | n).
```

At each induction step apply the two-factor inequality to the product
of the preceding moduli and the next modulus. The power prefactors
multiply exactly, and the common normalizing mass is positive.
Expanding `product_i (1+c_i 1_(d_i|n))` with `c_i>=0` therefore also
gives the corresponding product bound on its expectation. This is a
statement about nonnegative coefficients and intersections; it does
not establish a sign for inclusion-exclusion or arbitrary signed tests.

## TG limit

This supplies a sign for actual mixed coprime Gaussian statistics,
uniformly in both moduli and in positive damping. It does not prove
positivity of an arbitrary signed matrix combination, preservation of
the sign under all finite Euler inversions, or nonnegative area of TG's
completed residual. Those transfers must be proved separately; no
assumption standing for one of them enters the theorem above.

## Formalization

Paper proof complete. All three Lean modules pass direct source checks;
the transitive dependency audit passes.

The implementation is divided into three modules:

- `HTGeometry/LogConcaveIntegralComposition.lean`: exact determinant
  identity and preservation of the four-point law under integral composition.
- `RHTower/GaussianIntegerLogConcavity.lean`: actual theta flux, gamma
  transform, integrability, and `integerGaussianMass_log_four_point` /
  `integerGaussianMass_scale_submultiplicative` for the literal series.
- `RHTower/GaussianDivisibilityCorrelation.lean`: exact multiples and
  normalized event sums, `divisibilityCovariance_nonpos`, and the stronger
  product-modulus inequality `divisibilityProbability_finset_prod_le`.

Only domain conditions `sigma>=0`, `y>0`, positive moduli, and the stated
coprimality of the two actual events enter the endpoints. Integrability,
summability, normalization, and source identities are proved internally.

The exported analytic endpoint is the four-point law. The `ConcaveOn`
and positive-coefficient expectation reformulations above are paper
corollaries, not separately named Lean declarations.

## Verification

All commands ran from `formal/`, one Lean process at a time:

```
lake --old env lean GaloisForLFunctions/HTGeometry/LogConcaveIntegralComposition.lean
lake --old env lean GaloisForLFunctions/RHTower/GaussianIntegerLogConcavity.lean
lake --old env lean GaloisForLFunctions/RHTower/GaussianDivisibilityCorrelation.lean
```

The source-copy `#print axioms` audit covered integral composition, the
actual theta kernel's strict log-concavity, the gamma/source identity,
both Gaussian four-point endpoints, exact multiples, probability
normalization, coprime covariance, and the finite-product inequality.
Every audited declaration depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

No placeholders, extra analytic premises, trusted-computation shortcuts,
or resource-limit overrides occur in the three modules. Imports are wired
into the `HTGeometry` and `RHTower` umbrellas; no umbrella build was run.
