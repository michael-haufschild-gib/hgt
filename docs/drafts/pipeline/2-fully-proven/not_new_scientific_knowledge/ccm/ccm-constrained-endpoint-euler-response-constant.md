# Exact gap-scale Euler response of the constrained CCM endpoint layer

- **ID:** `ccm-constrained-endpoint-euler-response-constant`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** Slepian--Pollak finite-Fourier theory, Fuchs fixed-mode concentration
  asymptotics, Slepian's full fixed-mode PSWF expansions, and
  `constrained-prolate-two-mode-ground-state.md`
- **Statement:** For the normalized vanishing-integral `h_0`--`h_4` CCM source, the prime-dilation
  response of its leading lower endpoint tail is
  `(4*pi/33)(-zeta'(2)/zeta(2))d_1+o(d_1)`. With the two signed prime atoms in the Weil kernel, the
  actual prime-form contribution is
  `-(8*pi/33)(-zeta'(2)/zeta(2))d_1+o(d_1)`.

## Setup

For `c>0`, let

```text
(Q_c f)(x)=integral_(-1)^1 sin(c(x-y))/(pi*(x-y)) f(y)dy             (1)
```

on `L2(-1,1)`. Let `psi_(m,c)` be a real normalized eigenfunction with simple eigenvalue
`nu_m(c)`, and choose the fixed-mode branch continuously. In the CCM normalization put

```text
c=2*pi*lambda^2,
e_(m,lambda)(x)=lambda^(-1/2) psi_(m,c)(x/lambda),
d_m(lambda)=1-nu_m(2*pi*lambda^2).                                  (2)
```

Thus `e_(m,lambda)` is normalized on `[-lambda,lambda]`. For the positive compressed-Fourier
sector used by CCM, write

```text
e_0=e_(0,lambda),   e_1=e_(4,lambda),
d_0=1-chi_0^2,      d_1=1-chi_4^2,
ell_j=integral_R e_j,
g_lambda=(ell_1 e_0-ell_0 e_1)/sqrt(ell_0^2+ell_1^2).               (3)
```

The source `g_lambda` has unit norm and zero integral.

## Exact endpoint-response identity

`[PROVED HERE]` For every simple prolate branch,

```text
d/dc log(nu_m(c))=2*|psi_(m,c)(1)|^2/c.                             (4)
```

Equivalently, in the scaled CCM variable,

```text
|e_(m,lambda)(lambda)|^2
 =-d_m'(lambda)/(4*(1-d_m(lambda))).                                (5)
```

### Proof

Let

```text
(F_c f)(x)=integral_(-1)^1 exp(i*c*x*y)f(y)dy.
```

Direct calculation gives

```text
Q_c=(c/(2*pi)) F_c^* F_c.                                          (6)
```

Hellmann--Feynman and differentiation of the kernel in `(1)` give

```text
nu_m'(c)
 =1/pi * integral integral
    psi_(m,c)(x)psi_(m,c)(y)cos(c(x-y))dxdy
 =1/pi * |integral psi_(m,c)(x)exp(i*c*x)dx|^2.                     (7)
```

The finite-Fourier eigenrelation says

```text
F_c psi_(m,c)=mu_m(c)psi_(m,c).
```

Evaluation at `x=1` and `(6)` give

```text
|integral psi_(m,c)(x)exp(i*c*x)dx|^2
 =|mu_m(c)|^2 |psi_(m,c)(1)|^2
 =(2*pi/c)nu_m(c)|psi_(m,c)(1)|^2.                                 (8)
```

Equations `(7)`--`(8)` prove `(4)`. Scaling the endpoint by `lambda^(-1/2)` and using
`dc/dlambda=4*pi*lambda` proves `(5)`.

## Fixed-mode endpoint asymptotic

The classical fixed-mode prolate expansion, in its differentiable Poincare form, gives for every
fixed `m`

```text
d_m(lambda)
 =A_m lambda^(2m+1) exp(-4*pi*lambda^2)
    *(1+O(lambda^(-2))),

d_m'(lambda)/d_m(lambda)
 =-8*pi*lambda+(2m+1)/lambda+O(lambda^(-3)),                        (9)
```

with `A_m>0`. The first line is the Fuchs asymptotic already used in the constrained-prolate cards;
the differentiated expansion is supplied by the classical full fixed-mode PSWF expansion, not by
formal differentiation of an isolated `~` statement.

Combining `(5)` and `(9)` proves

```text
|e_(m,lambda)(lambda)|^2/(lambda*d_m(lambda)) -> 2*pi.              (10)
```

## Endpoint constant for the constrained source

For `m=0,4`, `(9)` implies

```text
d_0/d_1=O(lambda^(-8)),
e_0(lambda)/e_1(lambda)=O(lambda^(-4)).                             (11)
```

The exact constrained-prolate theorem gives

```text
ell_0^2/(ell_0^2+ell_1^2)->8/11.                                   (12)
```

Equations `(3)`, `(10)`--`(12)` therefore yield

```text
|g_lambda(lambda)|^2/(lambda*d_1(lambda)) ->16*pi/11.               (13)
```

The leading lower exterior term in the Poisson endpoint expansion is

```text
a_lambda T_(L_lambda)(s),
a_lambda=g_lambda(lambda)/(pi*sqrt(lambda)),
L_lambda=2*pi*lambda^2,
T_L(s)=e^(-s/2)S(L e^s).                                           (14)
```

Hence

```text
|a_lambda|^2/d_1(lambda) ->16/(11*pi).                              (15)
```

## Exact all-prime response constant

Define the complete lower-exterior prime-dilation quadratic response of the leading endpoint layer
by

```text
R_lambda
 =sum_(n>=2) Lambda(n)n^(-1/2)
    integral_0^infinity
      [a_lambda T_(L_lambda)(s)]
      [a_lambda T_(L_lambda)(s+log n)]ds.                           (16)
```

The full exterior sawtooth incidence theorem proves absolute convergence and

```text
sum_(n>=2) Lambda(n)n^(-1/2)
  integral_0^infinity T_(L_lambda)(s)T_(L_lambda)(s+log n)ds
 ->pi^2/12 * (-zeta'(2)/zeta(2)).                                  (17)
```

Multiplying `(15)` and `(17)` gives the claimed exact limit:

```text
R_lambda/d_1(lambda)
 ->(4*pi/33)*(-zeta'(2)/zeta(2)).                                  (18)
```

Every quantity on the right is positive.

## Signed prime contribution to the exterior Weil form

In additive logarithmic coordinates, the prime part of the even screw kernel is

```text
K_prime(t)
 =-sum_(n>=2) Lambda(n)n^(-1/2)
    *(delta_(log n)(t)+delta_(-log n)(t)).                          (19)
```

Let the leading lower tail be supported on `x<=-log(lambda)` and write

```text
b_lambda^0(-log(lambda)-s)=a_lambda T_(L_lambda)(s),  s>=0.
```

The two atoms in `(19)` give equal correlations, so the prime part of the global Weil form is

```text
Q_prime(b_lambda^0,b_lambda^0)=-2 R_lambda.                         (20)
```

Therefore `(18)` yields the signed asymptotic

```text
Q_prime(b_lambda^0,b_lambda^0)/d_1(lambda)
 ->-(8*pi/33)*(-zeta'(2)/zeta(2)).                                 (21)
```

## Positive consequence for the CCM route

The leading exterior prime layer is now calibrated at the same exponential scale as the
constrained positive-sector gap:

```text
leading prime endpoint response = explicit positive constant*d_1+o(d_1),
actual prime Weil contribution  = explicit negative constant*d_1+o(d_1).             (22)
```

Thus the true-Weil comparison must preserve and combine three `d_1`-scale quantities rather than
merely bound an unspecified small tail:

```text
the signed prime contribution in (21)
  + the archimedean endpoint response
  + the subleading/interior prime-incidence response.                                (23)
```

A proof that the sum in `(23)` equals a positive constant times `d_1`, with a remainder
`o(d_1)`, would prove that the CCM seed has cofinally vanishing positive Weil Rayleigh quotient.
Together with a matching true-gap or floor argument, this feeds respectively the determinant or
direct cofinal-Weil branch. Equation `(21)` supplies the first exact signed arithmetic coefficient
in that comparison.

The theorem does **not** identify the full exterior Weil form with `(16)`. Since `g_lambda` is
supported on `[-lambda,lambda]`, its summation vector vanishes identically for `u>lambda`; the
complete exterior representative is the lower tail. The remaining obligations are the
archimedean term, the full lower-tail remainder after subtracting `(14)`, and the passage from the
model seed to the true Weil ground state.

That remainder must be kept intact in the zeta-multiplier graph domain. In particular, the Poisson
central correction by itself is proportional to `e^(-s/2)`. Its isolated prime correlations would
contain `sum Lambda(n)/n`, which diverges. The source is nevertheless in the graph domain because
the central correction cancels with the rest of the exact Fourier tail. Thus pointwise endpoint-jet
sizes do not license a termwise Weil-form expansion; the positive next theorem is a bilinear
estimate for

```text
exact lower tail - a_lambda T_(L_lambda)
```

as one source-defined graph-domain vector.

## Novelty and significance verdict

### Parent overlap

- Slepian--Pollak and Fuchs supply `(4)` in equivalent normalization and the fixed-mode asymptotic
  input `(9)`.
- `constrained-prolate-two-mode-ground-state.md` supplies the `8/11` coefficient.
- `ccm-cofinal-prime-sawtooth-incidence-law.md` supplies absolute summability and the full
  exterior Euler scalar.

The exact constants `16/(11*pi)` and `(18)` were not located verbatim in the checked parent sources.
However, `ccm-prolate-endpoint-jet-resummation-law.md` proves that the fixed endpoint expansion is
not cofinally ordered at frequencies comparable to `lambda`. The vector `b_lambda^0` is therefore
a formal first-component calibration, not a proved leading approximation to the exact CCM tail.

After vocabulary erasure, the result is a direct combination of a classical endpoint response, a
constrained two-mode coefficient, and periodic dilation averaging. Its unproved connection to the
actual radial tail prevents it from clearing the significance gate even if the displayed constant
is novel as a formula. It is classified as a bridge. A significant new result must instead compute
the weighted dilation correlations of the **uniform radial-prolate profile** or prove the
renormalized exact-tail remainder theorem.

## References

- D. Slepian, H. O. Pollak, *Prolate spheroidal wave functions, Fourier analysis and uncertainty I*,
  Bell System Technical Journal 40 (1961), 43--63.
- W. H. J. Fuchs, *On the eigenvalues of an integral equation arising in the theory of band-limited
  signals*, J. Math. Anal. Appl. 9 (1964), 317--330.
- D. Slepian, *Some Asymptotic Expansions for Prolate Spheroidal Wave Functions*, J. Math. Phys. 44
  (1965), 99--140.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

The formal tree has no sinc-kernel operator, parameter derivative, normalized prolate branch, or
Fuchs asymptotic. Formalizing Hellmann--Feynman in isolation would not certify `(18)`. No Lean file
is added.

## Gates

- [x] exact endpoint-response identity proved
- [x] fixed-mode endpoint scale derived
- [x] constrained endpoint coefficient derived
- [x] growing all-prime response constant derived
- [ ] independent proof of the differentiated fixed-mode normalization
- [ ] exact archimedean endpoint response
- [ ] subleading/interior incidence remainder `o(d_1)`
- [ ] true Weil Rayleigh-excess or cofinal-floor transfer
