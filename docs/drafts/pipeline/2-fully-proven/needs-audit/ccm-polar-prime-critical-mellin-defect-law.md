# The finite-aperture CCM symbol carries an exact polar--prime critical Mellin defect

- **ID:** `ccm-polar-prime-critical-mellin-defect-law`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / SOURCE-CORRECTION AND CARRIER LAW
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [ERRATUM CANDIDATE] [NOT AN RH PROOF]`
- **Lean status:** `[PARTIALLY FORMALIZED]` — the unconditional finite-dimensional kernel,
  signature, corrected zero-frequency multiplier, full real-cutoff Abel identity `(12)`, its
  von Mangoldt specialization, the zero-frequency defect `(13)`, and the infinite real-ray
  Laplace colligation `(22)`--`(25)` are verified in
  `formal/GaloisForLFunctions/RHTower/PolarPrimeMellinDefect.lean`; the distributional source-sign
  derivation, autocorrelation identities, and full complex Stieltjes continuation remain paper-level
- **Parent source:** Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096,
  equations (2.5), (2.7), and (2.11)
- **Statement:** The exact finite-aperture Fourier symbol contains an aperture-dependent rank-two
  polar multiplier. Its value at zero cancels the full prime-number-theorem main term, leaving
  exactly a critical Mellin integral of the Chebyshev error. Consequently every valid sign or
  characteristic-crossing theorem is forced to carry that critical Mellin defect in addition to
  the leading prime mass.

## 1. Exact sign and polar multiplier

Use Suzuki's Fourier convention

```text
hat(v)(xi)=integral_R v(x)exp(i xi x)dx.                         (1)
```

In the local expansion of the screw function, the polar term is

```text
r_0(t)=-4(exp(t/2)+exp(-t/2)-2)=-8(cosh(t/2)-1),
r_0''(t)=-2cosh(t/2).                                           (2)
```

The distributional kernel is `-g''`. Therefore the contribution of `r_0` to the restricted
quadratic form is `-r_0''`, not `r_0''`. Since `x-y` belongs to `(-2a,2a)` for
`x,y in (-a,a)`, its exact Fourier multiplier is

```text
P_a(xi)
 =Fourier[2cosh(t/2) 1_(-2a,2a)(t)](xi)
 =[2sinh(a)cos(2a xi)+4xi cosh(a)sin(2a xi)]/(xi^2+1/4).        (3)
```

The apparent poles in `(3)` are removable because the defining kernel is compactly supported.
In particular,

```text
P_a(0)=8sinh(a).                                                (4)
```

Let

```text
m(xi)=Re psi(1/4+i xi/2)-log pi,
S_a(xi)=2 sum_(n<=exp(2a)) Lambda(n)n^(-1/2)cos(xi log n).       (5)
```

Then the exact restricted symbol is

```text
W_a(xi)=m(xi)-S_a(xi)+P_a(xi),                                 (6)

QW_a(v,v)=1/(2pi) integral_R W_a(xi)|hat(v)(xi)|^2dxi          (7)
```

for zero-extended `v in H_0^1(-a,a)`.

### Source-sign audit

Suzuki's equations (2.5) and (2.11) both contain the term `-r''`, which forces `(3)`--`(7)`.
The displayed `+hat(r_a'')` in equation (2.7), followed by `+hat(r_(0,a)'')`, has the opposite
sign. The same page computes

```text
hat(r_1'')=-Re psi(1/4+i xi/2)+log|xi|-log 2.                   (8)
```

Substitution into the preceding `log|xi|-log(2pi)` term produces `m(xi)` only with
`-hat(r_1'')`. Thus the distributional formula, the direct integration-by-parts derivation, and
the digamma simplification all agree on the minus sign. Equations `(6)`--`(7)` are the corrected
normalization.

## 2. Rank-two bilateral polarization

On the physical interval the polar block has kernel

```text
2cosh((x-y)/2)
 =2cosh(x/2)cosh(y/2)-2sinh(x/2)sinh(y/2).                     (9)
```

Hence its compressed operator has rank at most two and quadratic form

```text
2|inner(v,cosh(. /2))|^2-2|inner(v,sinh(. /2))|^2.             (10)
```

It is positive rank one on the even sector and negative rank one on the odd sector. The polar
factor is therefore an exact bilateral boundary carrier, not a scalar constant and not a
globally positive reference multiplier.

### Lean verification of the finite-dimensional core

The module
`formal/GaloisForLFunctions/RHTower/PolarPrimeMellinDefect.lean` verifies, without project axioms:

```text
polarKernel_eq_rankTwo
polarQuadraticForm_eq_rankTwo
polarEnergy_eq_signature
polarEnergy_nonneg_of_sinhFeature_eq_zero
polarEnergy_nonpos_of_coshFeature_eq_zero
polarMultiplier_zero
polarMultiplier_zero_pos
polarMultiplier_zero_eq_sqrtExp
abelSqrtWeight_identity
integral_invSqrt_Ioc
integral_criticalMain_Ioc
criticalMellinError_identity
vonMangoldt_criticalMellinError_identity
polarPrimeZero_defect_identity
criticalMellinDefect_cancellation
continuousPolarLaplaceChannel_eq
vonMangoldtPrimeLaplaceChannel_eq_logDeriv
vonMangoldtPrimeLaplaceChannel_pos
cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
cauchyKernel_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
```

Thus Lean checks the exact `(+,-)` two-channel signature, the positive zero-frequency sign for
positive aperture, the exact real-cutoff Abel formula for every coefficient sequence with zero
constant term, its specialization to the von Mangoldt coefficients, the complete finite
polar--prime cancellation `(13)` for `X=exp(2a)`, the Euler-region zeta logarithmic derivative,
strict positivity of the resolved prime channel, and the infinite real-kernel colligation `(25)`.
The formal theorem deliberately does not claim the source-level distributional sign derivation,
the autocorrelation Stieltjes carrier, or the full complex Stieltjes continuation of `(22)`.

## 3. Critical Mellin defect at zero

Put

```text
X=exp(2a),
Psi(X)=sum_(n<=X)Lambda(n),
E(X)=Psi(X)-X,
S(X)=sum_(n<=X)Lambda(n)n^(-1/2).                               (11)
```

Stieltjes partial summation gives the exact identity

```text
S(X)
 =2sqrt(X)-1+E(X)/sqrt(X)
   +(1/2)integral_1^X E(t)t^(-3/2)dt.                          (12)
```

Since `P_a(0)=4sqrt(X)-4/sqrt(X)`, equations `(4)`--`(6)` yield

```text
W_a(0)
 =m(0)+2-4/sqrt(X)
  -2E(X)/sqrt(X)-integral_1^X E(t)t^(-3/2)dt.                  (13)
```

Thus the `4sqrt(X)` prime main term cancels the `4sqrt(X)` polar main term exactly. The surviving
quantity is the endpoint-renormalized Mellin transform of the prime-number-theorem error at the
critical exponent `1/2`.

The ordinary prime number theorem gives only `E(X)=o(X)`, which does not determine the sign or
limit of `(13)`. A sign theorem at zero must therefore control the endpoint-renormalized critical
Mellin transform in `(13)`; the asymptotic `S(X)~2sqrt(X)` omits the polar term of the same leading
size in `(4)`.

## 4. Exact autocorrelation carrier

For a zero-extended aperture vector `v`, define its positive-lag autocorrelation

```text
C_v(h)=integral_R v(x+h)conjugate(v(x))dx,       0<=h<=2a.     (14)
```

Put

```text
A(h)=sum_(n<=exp(h))Lambda(n)n^(-1/2),
R(h)=4sinh(h/2)-A(h).                                         (15)
```

The continuous polar shift measure is

```text
d[4sinh(h/2)]=2cosh(h/2)dh,                                  (16)
```

while the prime shift measure is

```text
dA(h)=sum_(n>=2)Lambda(n)n^(-1/2)delta_(log n).               (17)
```

Therefore the complete polar--prime part of the aperture quadratic form is exactly

```text
Q_(polar-prime,a)(v,v)
 =2 Re integral_(0,2a) C_v(h)dR(h).                           (18)
```

The same signed measure gives the complete corrected symbol, not only its value at zero:

```text
W_a(xi)
 =m(xi)+2 Re integral_(0,2a) exp(i xi h)dR(h).                 (18a)
```

Thus polar--prime main-term cancellation occurs at every real frequency. The entire arithmetic
remainder is the finite Fourier--Stieltjes transform of the cumulative critical Mellin error `R`.

For smooth aperture vectors, `C_v(2a)=0` and `R(0)=0`, so Stieltjes integration by parts also gives

```text
Q_(polar-prime,a)(v,v)
 =-2 Re integral_0^(2a) R(h)dC_v(h).                          (19)
```

Using `(12)` with `X=exp(h)`, the cumulative carrier has the exact critical-error form

```text
R(h)
 =1-2exp(-h/2)-exp(-h/2)E(exp(h))
  -(1/2)integral_1^(exp(h))E(t)t^(-3/2)dt.                    (20)
```

In particular,

```text
W_a(0)-m(0)=2R(2a).                                           (21)
```

Thus the same object controls both the zero-frequency defect and every aperture autocorrelation
through `(18)`. This is the exact signed boundary measure underlying the parity-Hankel carrier in
`ccm-finite-prime-parity-hankel-carrier.md`.

Its Laplace transform identifies the divisor-sensitive source it carries. For `Re z>1/2`,

```text
integral_0^infinity exp(-z h)dR(h)
 =1/(z-1/2)+1/(z+1/2)+zeta'(z+1/2)/zeta(z+1/2).                (22)
```

Indeed the continuous term is the Laplace transform of `2cosh(h/2)dh`, while

```text
sum_(n>=2)Lambda(n)n^(-1/2)exp(-z log n)
 =-zeta'(z+1/2)/zeta(z+1/2).                                  (23)
```

After adding the Gamma logarithmic connection, `(22)` is the completed logarithmic source
`xi'/xi`. Thus continuation of the boundary measure is automatically divisor-sensitive; a
factorization that replaces it by its prime-number-theorem main term deletes precisely the pole
data that the RH argument must transport.

## 5. Positive CCM obligation

Every finite-aperture multiplier, Wiener--Hopf, Evans, or Gram implementation of the screw route
must jointly carry

```text
digamma logarithmic multiplier
  + finite prime cosine module
  + rank-two polar boundary block
  + critical Mellin defect of E(X)
  + Paley--Wiener compression at the matching aperture.        (24)
```

The polar block may not be absorbed into an aperture-independent `m_infinity`, and the prime main
term may not be studied without its polar cancellation. Any zero-free or characteristic-crossing
factorization must be performed on the corrected symbol `W_a`.

The same Laplace identity now gives the exact source incidence of the canonical diagonal Fock
coordinate.  Setting `z=x+y+1/2` in `(22)` yields

```text
1/(x+y)
 =-zeta'(1+x+y)/zeta(1+x+y)-1/(x+y+1)
  +integral_0^infinity exp(-(x+y+1/2)h)dR(h).             (25)
```

Thus the universal Cauchy leg required by the infinitesimal CCM contraction is already the signed
colligation of the resolved prime-power Gram, a shifted polar Gram, and this critical Mellin
defect.  The resulting RH-equivalent four-channel passivity law is recorded in
`../not_new_scientific_knowledge/ccm-diagonal-fock-polar-prime-mellin-incidence-law.md`.

## Novelty boundary

The Fourier transform `(3)` and partial summation `(12)` are elementary. The potentially new
content is the correction of the sign in the June 2026 source and the resulting identification
of `(13)` as the exact finite-aperture polar--prime boundary invariant. This remains an erratum
candidate until checked against the author or a revised source version; it is not promoted as new scientific
knowledge.

## Gates

- [x] distributional sign checked against Suzuki equations (2.5) and (2.11)
- [x] exact polar multiplier computed
- [x] rank-two parity signature computed
- [x] prime main-term cancellation proved
- [x] critical Mellin defect identity proved
- [x] exact autocorrelation Stieltjes carrier isolated
- [x] Laplace source identified with the rational-plus-Euler logarithmic derivative
- [x] necessary critical-defect carrier law stated positively
- [x] unconditional finite-dimensional core formalized in Lean and axiom-audited
- [x] real-cutoff Abel and von Mangoldt critical Mellin identities formalized in Lean
- [x] complete finite zero-frequency defect `(13)` formalized in Lean
- [x] infinite real-ray polar--prime Laplace identity and four-channel kernel colligation
  formalized in Lean
- [ ] independent source/author audit of the printed sign
- [ ] formalize the distributional/autocorrelation Stieltjes layers and full complex continuation
- [ ] control the full compressed symbol on `PW_a`
- [ ] RH
