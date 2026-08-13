# Absolute-Euler paired energy is one normalized screw-current dissipation

- **ID:** `absolute-euler-paired-normalized-screw-current-identification`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[VALUE RELATION]`, `[TOP-DOWN INTERFACE DISCHARGE]`
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT AN RH PROOF]`
- **Parents:**
  `absolute-euler-paired-cumulative-critical-error-current-law.md`,
  `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-screw-kernel-positivity-improving-breakdown.md`, and
  `formal/GaloisForLFunctions/RHTower/CCMCriticalMellinCompletedError.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiShiftPrimeExposure.lean`
- **Statement:** On the complete rational damped-sine core, the compensated digamma form and the
  cumulative critical prime current combine into one classically integrable current.  Its
  distributional derivative is exactly the full Suzuki--Weil screw kernel, including the
  negative prime-power atoms.  The paired boundary condition forces the autocorrelation current
  to vanish at contact, so no finite-part boundary hypothesis remains.

## 1. Paired boundary cancellation

Let

```text
y(x)=Im sum_j r_j exp(-w_j*x),
Re(w_j)>1/2,  r_j real,                                  (1)
```

and put

```text
C_y(h)=integral_0^infinity y(x+h)y(x) dx.                (2)
```

Because every coefficient `r_j` is real,

```text
y(0)=Im sum_j r_j=0.                                     (3)
```

Integration by parts therefore gives the exact contact laws

```text
C_y'(0)=integral_0^infinity y'(x)y(x) dx
       =-y(0)^2/2=0,                                    (4)

C_y''(0)=-integral_0^infinity y'(x)^2 dx.                (5)
```

In particular `C_y'(h)=O(h)` at the origin.  This is stronger than ordinary Cauchy-packet
summability: it is the boundary cancellation selected by the Schwarz-odd paired source itself.

## 2. Exact primitive of the Gamma tail

Define, for `h>0`,

```text
k_infinity(h)=exp(-h/2)/(1-exp(-2*h)),                   (6)

A_infinity(h)=integral_h^infinity k_infinity(t) dt.     (7)
```

The substitution `u=exp(-t/2)` gives the closed form

```text
A_infinity(h)
 =atanh(exp(-h/2))+atan(exp(-h/2)),                     (8)

A_infinity'(h)=-k_infinity(h).                          (9)
```

Let

```text
D_Gauss
 =-(log(pi)+EulerGamma)/2 * I
  +sum_(n>=0)(1/(2*(n+1))*I-R_(2*n+1/2))                (10)
```

be the compensated digamma form from the parent card.  With `C_0=C_y(0)`, geometric summation of
the resolvent kernels gives

```text
<y,D_Gauss y>
 =-(log(pi)+EulerGamma)/2*C_0
  -integral_0^infinity k_infinity(h)
      (C_y(h)-exp(-3*h/2)*C_0) dh.                      (11)
```

The bracket in `(11)` vanishes at contact.  Integrating against the tail primitive `(7)` is
therefore ordinary integration by parts, not a separation of divergent Gamma series:

```text
<y,D_Gauss y>
 =-integral_0^infinity A_infinity(h)C_y'(h) dh
  -kappa_infinity*C_0,                                  (12)
```

where

```text
kappa_infinity
 =(log(8*pi)+EulerGamma)/2+pi/4.                        (13)
```

Indeed Tonelli's theorem and the substitution `u=exp(-h/2)` give

```text
integral_0^infinity A_infinity(h)exp(-3*h/2) dh
 =log(2)+pi/6.                                          (14)
```

Equations `(12)--(14)` fix the real contact normalization exactly.

## 3. The normalized completed screw current

Recall

```text
E_crit(h)
 =4*sinh(h/2)
  -sum_(2<=m<=exp(h)) Lambda(m)*m^(-1/2).                (15)
```

Define the normalized one-sided source current

```text
J_Xi_screw(h)=E_crit(h)+A_infinity(h)-kappa_infinity.    (16)
```

The cumulative-current parent theorem states

```text
Q_pair(y)
 =8*(<y,D_Gauss y>
      -integral_0^infinity E_crit(h)C_y'(h) dh).         (17)
```

Since `integral_0^infinity C_y'(h) dh=-C_0`, equations `(12)` and `(16)` turn `(17)` into the
single exact identity

```text
Q_pair(y)
 =-8*integral_0^infinity J_Xi_screw(h)C_y'(h) dh.       (18)
```

The integral in `(18)` is classical.  Near zero, `(8)` gives
`J_Xi_screw(h)=-(1/2)log(h)+O(1)`, while `(4)--(5)` give `C_y'(h)=O(h)`.  At infinity the strict packet
damping `Re(w_j)>1/2` beats the elementary critical exponential bound used in the parent card.

## 4. Exact collision with the Suzuki--Weil screw kernel

In the sense of distributions on the positive ray,

```text
E_crit'
 =2*cosh(h/2) dh
  -sum_(m>=2) Lambda(m)*m^(-1/2) delta_(log m).          (19)
```

Using `(9)`, the regular part of `J_Xi_screw'` is

```text
2*cosh(h/2)-exp(-h/2)/(1-exp(-2*h))
 =exp(h/2)-exp(-5*h/2)/(1-exp(-2*h)).                   (20)
```

The right side of `(20)` is exactly the regular kernel `K_reg` computed from Suzuki's screw
function in `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-screw-kernel-positivity-improving-breakdown.md`.  Hence

```text
J_Xi_screw'
 =K_reg(h) dh
  -sum_(m>=2) Lambda(m)*m^(-1/2) delta_(log m)
 =K_Weil                                                     (21)
```

is the full distributional Weil kernel `-g''`.  The additive constant `(13)` is the canonical
normalization selected by the completed Xi logarithmic derivative; it disappears from `(21)` but
is load-bearing in the current identity `(18)`.

Thus the cumulative critical-error route and the screw-function route are not merely analogous.
They are the same source form after one exact primitive and the paired boundary cancellation.

## 5. Formal even-shift regularization

The same denominator occurring in `(6)` is exactly the source filter exposed by the formal `+2`
shift theorem.  Define

```text
K_shift(h)=(1-exp(-2*h))*K_Weil(h).                      (22)
```

Multiplying `(21)` by the smooth factor in `(22)` gives

```text
K_shift
 =[exp(h/2)-exp(-3*h/2)-exp(-5*h/2)] dh
  -sum_(m>=2) Lambda(m)*m^(-1/2)*(1-m^(-2))
      delta_(log m).                                    (23)
```

The regular density in `(23)` has finite limit `-1` at contact.  Thus one even shift removes both
the logarithmic distributional singularity and the infinite digamma denominator.

Let `s=1/2+w`, with `Re(w)>1/2`.  The one-sided Laplace transform of the regular density is

```text
1/(w-1/2)-1/(w+3/2)-1/(w+5/2)
 =-[1/(s+2)+1/(s+1)-1/(s-1)].                           (24)
```

The atomic transform is the negative filtered von Mangoldt series.  Consequently the formal
theorem `xi_logDeriv_shift_two_exposes_prime_source` is exactly the value identity

```text
Laplace(K_shift)(w)
 =logDeriv(xi)(s)-logDeriv(xi)(s+2).                    (25)
```

This is more than a similarity of factors: the rational archimedean shift defect in Lean is the
Laplace transform of the three-exponential density in `(23)`, and the coefficient
`Lambda(m)*(1-m^(-2))` is the atomic multiplier in the same distribution.

Equation `(25)` supplies a regular finite-shift source interface for later attacks.  It does not
by itself preserve positivity: multiplication of a convolution kernel by `1-exp(-2*h)` is not a
positive map on the autocorrelation cone.  Reconstructing `K_Weil` by the geometric inverse
requires the canonical contact normalization `(13)` and control of all exponentially reweighted
filtered forms.  The positive remaining opportunity is therefore a source-specific inversion or
telescoping theorem, not the already formalized scalar sign of the filtered series on real Euler
anchors.

### The contact channel is positively necessary

The failure of bare filtered positivity already occurs inside the permitted damped-sine core.
Extend `(23)` evenly to the line and let `Q_shift` be its convolution quadratic.  For `a>1/2`, put

```text
y_a(x)=exp(-a*x)*sin(a*x),  x>=0,                        (26)
```

extended by zero to the negative half-line.  The regular density in `(23)` extends continuously
to contact with value

```text
K_shift,reg(0)=1-1-1=-1.                                (27)
```

After `u=a*x`, `v=a*y`, local dominated convergence gives

```text
lim_(a->infinity) a^2*Q_shift(y_a)
 =-[(integral_0^infinity exp(-u)sin(u)du)^2]
 =-1/4.                                                  (28)
```

The prime atoms do not contribute to `(28)`: their first displacement is `log 2`, whereas the
packet lives at scale `1/a`, and every atomic autocorrelation is exponentially small in `a`.
The exponentially growing part of the regular density is likewise dominated by the packet decay
for all sufficiently large `a`.  Hence `Q_shift(y_a)<0` for all sufficiently large `a`; rational
such `a` give witnesses in the countable source core.

The positive theorem forced by `(28)` is:

> Every direct positivity-compatible use of the formal even shift must add a compensating
> channel alongside the regular filtered distribution.  In the present source coordinates, the
> canonical compensator is the contact/boundary normalization.

The current normalization `(13)--(18)` supplies exactly such a channel.  Deleting it while keeping
only the filtered von Mangoldt coefficients loses the local positive mechanism before any
large-prime estimate is reached.

## 6. What is discharged and what remains open

Equations `(3)--(25)` discharge four separate-looking inputs:

1. no independent domination estimate for `D_Gauss` is needed;
2. no principal-value or finite-part contact hypothesis is needed on the paired core;
3. no unidentified bridge from the cumulative critical error to the screw kernel remains.
4. no unidentified bridge from the formal even-shift source to a regularized screw kernel remains.

The live chain is now

```text
integral_0^infinity J_Xi_screw(h)C_y'(h) dh <= 0
  for every rational damped-sine packet y
 -> absolute-Euler paired passivity
 -> positivity on the Xi--Hurwitz orientation vector
 -> RH.                                                   (29)
```

The first line is still open.  Because the paired core is complete, generic positivity of the
full screw form would merely restate Weil's criterion.  A non-circular proof must exploit an
additional source-specific property of the explicit current `(16)` together with the finite
exponential boundary-zero class `(1)`.  Suzuki's unconditional construction of the restricted
self-adjoint screw operators supplies the correct analytic domain, but not their cofinal
nonnegativity.

The boundary cancellation does not remove the critical Radon--Nikodym recession from
`ccm-euler-gamma-radon-nikodym-frame-law.md`.  A paired Cauchy packet cancels only finitely many
inverse powers of `log p`; the critical correction grows exponentially in `log p`.  Its positive
content is instead the classical integrability and exact current normalization in `(18)`.

## 7. Corpus and literature boundary

- `CCMCriticalMellinCompletedError.lean` already identifies `E_crit` with the causal Volterra
  potential of the normalized Chebyshev error.
- `CCMPolarPrimeStieltjesAutocorrelation.lean` supplies the finite-aperture Stieltjes
  integration-by-parts provider used by the parent current card.
- `XiShiftPrimeExposure.lean` proves the exact even-shift rational/filtered-prime value relation
  identified with `(23)--(25)`.
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-screw-kernel-positivity-improving-breakdown.md` derives `(20)` from Masatoshi Suzuki,
  *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- Suzuki's framework turns the distributional Weil quadratic into restricted self-adjoint
  operators and continuous screw kernels; it does not assert their cofinal positivity without RH.

The new content here is an exact coordinate splice and boundary-domain discharge.  It is
conservatively classified as a bridge, not as new scientific knowledge.

## Lean decision

No Lean file is added under the active no-computation/no-build boundary.  A later formalization
should first prove `(3)--(5)`, then the finite Gauss partial-sum version of `(11)--(12)`, and only
afterwards pass through the already formalized Stieltjes current identity.

## Gates

- [x] paired source boundary zero and flat autocorrelation contact proved
- [x] Gamma tail primitive computed in closed form
- [x] canonical contact normalization computed
- [x] complete paired energy compressed to one classical current integral
- [x] distributional derivative identified with the full Suzuki--Weil screw kernel
- [x] even-shift filter identified with a contact-regular three-exponential screw distribution
- [x] formal filtered von Mangoldt shift theorem spliced to its exact Laplace transform
- [x] bare filtered positivity ruled out by an exact damped-sine scaling witness
- [x] bare filtered source proved to require a compensating channel; canonical contact supplied
- [x] separate Gamma and finite-part boundary hypotheses discharged
- [x] critical frame recession checked not to be removed by finite logarithmic cancellation
- [ ] construct a contact-augmented positivity-compatible inversion of the even-shift filter
- [ ] prove the normalized screw-current dissipation on the rational damped-sine core
- [ ] formalize the exact interface after the analytic sign mechanism is found
- [ ] prove RH
