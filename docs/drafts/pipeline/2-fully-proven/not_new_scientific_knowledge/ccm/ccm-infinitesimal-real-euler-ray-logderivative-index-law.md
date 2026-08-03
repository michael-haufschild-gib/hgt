# The infinitesimal real Euler ray has exact off-line log-derivative index

- **ID:** `ccm-infinitesimal-real-euler-ray-logderivative-index-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** centered Hadamard factorization, generalized Nevanlinna kernels, and
  `ccm-real-euler-ray-loewner-index-law.md`

## Statement

Put

```text
X(z)=xi(1/2+z),
Q(z)=X'(z)/X(z).                                          (1)
```

For real `x,y>1/2`, define

```text
J(x,y)=(Q(x)+Q(y))/(x+y).                                (2)
```

Then

```text
ind_-(J)
 =sum_(xi(rho)=0, Re rho>1/2)multiplicity(rho),          (3)
```

including the value `+infinity`. Consequently

```text
RH
 iff J is positive semidefinite on (1/2,infinity)
 iff every rational-node matrix (J(x_j,x_k)) is positive semidefinite. (4)
```

Every entry of `(2)` uses the completed logarithmic derivative only at real points

```text
s=1/2+x>1,                                               (5)
```

where its prime expansion is absolutely convergent.

## 1. Exact zero-packet factorization

The centered entire function `X` is even and of order one. Pairing its divisor under
`lambda -> -lambda` gives

```text
Q(z)
 =sum_(lambda mod +/-)
   [1/(z-lambda)+1/(z+lambda)],                          (6)
```

with the usual locally uniform symmetric summation and multiplicities. A zero at the origin would
add `m/z`; for Xi this term is absent.

For one paired parameter `lambda`, put

```text
q_lambda(z)=1/(z-lambda)+1/(z+lambda)
            =2z/(z^2-lambda^2).                         (7)
```

Its contribution to `(2)` is

```text
[q_lambda(x)+q_lambda(y)]/(x+y)
 =2(xy-lambda^2)
   /((x^2-lambda^2)(y^2-lambda^2)).                     (8)
```

If `lambda=i gamma` is on the imaginary axis, `(8)` is

```text
2 [x/(x^2+gamma^2)] [y/(y^2+gamma^2)]
+2 [gamma/(x^2+gamma^2)] [gamma/(y^2+gamma^2)],         (9)
```

a positive rank-at-most-two kernel.

If `lambda` is not imaginary, combine `(8)` with the conjugate parameter. The resulting Hermitian
packet is congruent to one positive and one negative rank-one square for each zero in the right
half of the centered plane. For a real positive `lambda=a`, this is visible directly:

```text
2(xy-a^2)/((x^2-a^2)(y^2-a^2))
 =2 [x/(x^2-a^2)] [y/(y^2-a^2)]
  -2 [a/(x^2-a^2)] [a/(y^2-a^2)].                      (10)
```

The general conjugate quartet is the complex Hermitian version of `(10)` and contributes two
negative squares, matching its two right-half zeros.

The congruence has an exact causal/anti-causal form.  For a right-half zero
`lambda=a+i gamma`, put

```text
f_lambda(x)=1/(x-lambda),
g_lambda(x)=1/(x+conjugate(lambda)).
```

The Hermitian packet attached to `lambda` and `-conjugate(lambda)` is

```text
f_lambda(x)conjugate(g_lambda(y))
 +g_lambda(x)conjugate(f_lambda(y))
 =|u_lambda><u_lambda|-|v_lambda><v_lambda|,
```

where `u_lambda=(f_lambda+g_lambda)/sqrt(2)` and
`v_lambda=(f_lambda-g_lambda)/sqrt(2)`.  Under Laplace transformation, `v_lambda` is the
hyperbolic-odd mode `exp(i gamma t)sinh(a t)`, while `g_lambda` is the decaying residue mode whose
norm gives the four-unit boundary trace cost.  This source-by-source dictionary is proved in
`ccm-quartet-resolvent-bilateral-polarization-law.md`.

## 2. Exact negative index

Equations `(6)`--`(10)` give a positive-minus-negative factorization with one negative coordinate
per right-half zero. The corresponding rational feature functions for distinct zeros are linearly
independent on every nonempty real interval, by uniqueness of exponential/rational partial
fractions. The Krein--Langer minimal factorization theorem therefore gives `(3)` when the off-line
count is finite. If it is infinite, every finite packet produces a negative subspace of its own
cardinality, so the index is infinite.

The interval `(1/2,infinity)` is a uniqueness set for the meromorphic kernel obtained from `(6)`.
Restriction from the right half-plane to this interval therefore preserves the negative index.
Choosing a dense rational sequence and using principal-matrix interlacing proves the last
equivalence in `(4)`. `QED`

## 3. Infinitesimal shifted-quotient derivation

The same kernel is the source derivative of the real shifted quotient. From

```text
f_omega(x)=X(x-omega)/X(x+omega),                        (11)
```

one has locally uniformly for `x>1/2`

```text
f_omega(x)=1-2omega Q(x)+O(omega^2).                     (12)
```

Therefore the shifted Cauchy--Loewner kernel satisfies

```text
lim_(omega->0+)
  1/(2omega)
  [1-f_omega(x)f_omega(y)]/(x+y)
 =J(x,y).                                                (13)
```

Thus `(2)` is not a new criterion attached after the fact. It is the exact infinitesimal boundary
form of the completed CCM weighted-contraction family.

## 4. Euler-source formula

For `s=1/2+x>1`,

```text
Q(x)=xi'(s)/xi(s)
 =1/s+1/(s-1)-(1/2)log pi
  +(1/2)psi(s/2)+zeta'(s)/zeta(s),                      (14)

zeta'(s)/zeta(s)
 =-sum_(n>=2)Lambda(n)n^(-s).                           (15)
```

Hence every rational-node matrix in `(4)` is computed from explicit real Gamma values and an
absolutely convergent real von-Mangoldt series. No shift parameter, complex sampling point,
critical-strip continuation, or zero ordinate enters its construction.

## Positive CCM obligation

The full cofinal shifted family has collapsed to one source kernel:

```text
completed logarithmic derivative on s>1
  -> J(x,y)=(Q(x)+Q(y))/(x+y)
  -> prove complete positivity
  -> RH.                                                  (16)
```

The positive target is stronger than `Q(x)>0`. The diagonal identity

```text
J(x,x)=Q(x)/x                                            (17)
```

is unconditionally positive outside the classical zero strip, while off-line zeros are detected
only by multi-point negative squares. A successful proof must establish the complete kernel order,
not scalar monotonicity of Xi.

Under RH, `(9)` supplies an explicit positive feature map indexed by the critical-line ordinates.
The source-side challenge is to prove the same positivity directly from `(14)`--`(15)` without
reading that divisor.

`[PROVED HALF-UNIT NORMAL FORM]` The classical zero strip already makes

```text
[Q(x)+Q(y)]/(x+y-1)
```

positive. Passing to `J` changes only the denominator from `x+y-1` to `x+y`, but the corresponding
scalar Schur ratio `(x+y-1)/(x+y)` has a strictly negative determinant on every pair of distinct
nodes. Hence the remaining half-unit cannot be transported by a universal scalar kernel factor;
it requires source-specific Euler--Gamma covariance. This is proved in
`ccm-infinitesimal-half-unit-cauchy-seam-law.md`.

## Relation to the aperture Morse charge

Combining `(3)` with the cofinal index-exhaustion theorem gives the exact three-way identity

```text
ind_-(J)
 =sup_(a>0)kappa(a)
 =sup_(omega>0)dim K(B_omega).                           (18)
```

Thus the infinitesimal real Euler kernel already carries the complete determinant-line/Morse
charge of the CCM route.

## Scope and classification

The zero-packet factorization is the logarithmic-derivative form of the classical
Krein--Langer/generalized Nevanlinna index theorem. Restriction to a real uniqueness interval and
Euler-region evaluation are routine consequences. This is a route bridge, not new scientific
knowledge.

The unconditional Xi Hadamard divisor and logarithmic derivative now exist in the Lean tree:
`XiC_eq_constant_mul_canonicalProduct` is multiplicity-exact, and
`logDeriv_XiC_eq_relativeResolventTrace` identifies the pole-free logarithmic derivative with the
summed divisor resolvent.  These two former prerequisites are discharged.  What remains absent is
the analytic Krein--Langer negative-index minimality theorem, including preservation of the exact
index under restriction to the real Euler uniqueness interval.  The finite rational packet
algebra alone would not prove that step, so no wrapper is added.

## Gates

- [x] shifted Euler-ray family differentiated at the critical seam
- [x] one fixed real log-derivative kernel isolated
- [x] critical-line zero packets proved positive
- [x] each right-half zero proved to contribute one negative square
- [x] exact total off-line index recovered
- [x] dense rational Euler matrices proved index-exhausting
- [x] aperture Morse and Hardy defect charges identified with the infinitesimal kernel index
- [x] exact infinitesimal half-unit seam and its scalar indefiniteness isolated
- [ ] prove `J>=0` directly from the Euler--Gamma source
- [ ] RH
