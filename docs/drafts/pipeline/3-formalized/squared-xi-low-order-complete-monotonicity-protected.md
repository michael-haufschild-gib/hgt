# Squared-Xi low-order complete monotonicity is unconditionally protected

- **ID:** squared-xi-low-order-complete-monotonicity-protected
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4, fully unconditional) / RH-disproof route discriminator
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [SIGNIFICANT ROUTE KILL]`
  `[FORMALIZED IN LEAN, AXIOMS CLEAN, STRICTLY STRONGER THAN THE CARD]`
- **Sources:** `XiEndpointStrongHeightGap.lean`; `PrimeArchScaledHausdorffDivisorValueRelation.lean`; the genus-zero canonical product of centered Xi in the squared variable; the critical-strip theorem
- **Statement:** For `y>1/4`, the squared-variable logarithmic derivative of centered Xi has the complete-monotonicity signs through derivative order thirteen, unconditionally.  Hence the first possible squared-seam derivative witness against RH has order at least fourteen.
- **Formalized strengthening:** the same signs hold for every `y>0` and every order through
  **eighteen**, so the first possible squared-seam derivative witness has order at least nineteen.

## Theorem

Put

```text
g(y) = xi'(1/2+sqrt(y)) / (2*sqrt(y)*xi(1/2+sqrt(y)))
```

for `y>1/4`.  Then, for every integer `n` with `0<=n<=13`,

```text
(-1)^n g^(n)(y) > 0.                                      (1)
```

Equivalently, with `L(s)=xi'(s)/xi(s)` and
`F(w)=L(1/2+w)/w=2g(w^2)`, every alternating squared-coordinate derivative
of `F` through order thirteen has the RH-compatible strict sign on `w>1/2`.

In particular,

```text
w*L'(1/2+w)-L(1/2+w) < 0,                                (2)
```

so the first-gate inequality proposed in
`../../1-in-progress/absolute-euler-squared-seam-sign-violation.md` cannot
hold.

## Proof `[PROVED HERE]`

### 1. Uniform angle bound for every squared zero

Let `rho=sigma+i*gamma` be a nontrivial Xi zero and set

```text
delta = sigma-1/2,
t     = gamma^2-delta^2,
b     = 2*delta*gamma,
q     = b^2.
```

The critical strip gives `delta^2<=1/4`.  The already formalized endpoint
height theorem gives

```text
41/2 < gamma^2.                                           (3)
```

For `y>1/4`, put `A=y+t=y+gamma^2-delta^2`.  Then
`A>=gamma^2>0`, and hence

```text
x := q/A^2
   = 4*delta^2*gamma^2/A^2
   <= 1/gamma^2
   < 2/41.                                                (4)
```

The conjugate pair of squared zeros contributes a positive multiple of

```text
H(y) = A/(A^2+q) = Re(1/(A-i*b)).                         (5)
```

Critical-line zeros are the special case `b=0`.

### 2. Exact derivative signs through order six

For `k=n+1`, differentiation of (5) gives

```text
(-1)^n H^(n)(y)
  = n! * Re((A-i*b)^(-k)).                                (6)
```

After dividing by positive powers of `A` and `1+x`, the sign in (6) is the
sign of

```text
C_k(x) = Re((1-i*sqrt(x))^k).
```

For `1<=k<=7`, these polynomials are

```text
C_1 = 1,
C_2 = 1-x,
C_3 = 1-3x,
C_4 = 1-6x+x^2,
C_5 = 1-10x+5x^2,
C_6 = 1-15x+15x^2-x^3,
C_7 = 1-21x+35x^2-7x^3.                                  (7)
```

The first five are immediately positive for `0<=x<2/41` after discarding
their nonnegative final terms where appropriate.  For `C_6`,

```text
C_6(x) >= 1-15*(2/41)-(2/41)^3 > 0.                       (8)
```

For the last polynomial,

```text
C_7'(x) = -21+70x-21x^2 < -21+140/41 < 0
```

on `[0,2/41]`, while the exact endpoint value is

```text
C_7(2/41) = 4003/68921 > 0.                               (9)
```

Thus the height bound alone makes every orbit contribution in (6) have the
strict sign in (1) for `0<=n<=6`.

### 3. The formal reciprocal-square sector extends the protection

The current Lean corpus has a sharper input than the height estimate.  For
every Xi multiplicity copy, let

```text
lambda = xiZeroCopyReciprocalSquare = 1/(t-i*b).
```

`PrimeArchScaledHausdorffDivisorValueRelation.lean` proves pointwise that

```text
Re(lambda)>0,
(913/100)*|Im(lambda)| <= Re(lambda),                    (10)
```

and uses this sector to prove `Re(lambda^m)>=0` for every `1<=m<=14`.
For the shifted kernel in (5), put

```text
mu_y = 1/(t+y-i*b).
```

The imaginary-to-real ratios satisfy

```text
|Im(lambda)|/Re(lambda) = |b|/t,
|Im(mu_y)|/Re(mu_y)     = |b|/(t+y) <= |b|/t.            (11)
```

Thus `mu_y` lies in the same sector (10).  Equivalently,
`|arg(mu_y)|<=100/913`.  If `m<=14`, then

```text
|m*arg(mu_y)| <= 1400/913 < pi/2.                        (12)
```

The final rational inequality is already proved in the formal sector
argument.  Since `mu_y!=0`, equation (12) gives

```text
Re(mu_y^m)>0                                             (13)
```

for every `1<=m<=14`.  Combining (6) with `m=n+1` proves the per-orbit
strict derivative sign for every `0<=n<=13`.

### 4. Canonical-product assembly

The even entire function `w |-> xi(1/2+w)` is a genus-zero entire function
of order `1/2` in `y=w^2`.  Its logarithmic derivative is the absolutely and
locally normally convergent sum over squared zero orbits.  Therefore its
derivatives may be summed orbitwise on `y>1/4`.  Equations (10)--(13) make
every summand in (1) positive through order thirteen.  Xi has nontrivial
zeros, so the sum is strictly positive.  This proves (1).

Finally,

```text
d/dy [L(1/2+sqrt(y))/sqrt(y)]
  = [w*L'(1/2+w)-L(1/2+w)]/(2*w^3),
```

and (2) follows from the `n=1` case.  `QED`

## Sharpness of this discriminator

The height-only chamber proves positivity through derivative order six.  The
reciprocal-square sector `84 B^2 <= t^2` proves it through order thirteen: its
argument budget at the next power is `1500/913 > pi/2`.

That is not the true boundary.  The shift `A = y + t` is strictly larger than the
unshifted `t`, so **every** sector ratio the corpus proves for the unshifted
reciprocal-square atoms transfers to the shifted kernel at every `y>0`.  The
corner-exclusion sectors already formalized for reciprocal-square powers
fifteen through nineteen therefore protect derivative orders fourteen through
eighteen as well, at every positive `y`, and the first unprotected order is
**nineteen**, not fourteen.

## Consequence

Fixed orders `n=0,...,18` cannot disprove RH anywhere on `y>0`, hence nowhere on
the absolute Euler ray `w>1/2`.  In particular the compact witness window
`1/4<y<8` claimed for order fourteen is empty.  A surviving squared-seam attack
must either:

1. prove an order-nineteen-or-higher sign violation from the completed source;
2. use a source-controlled order/base-point coupling that outruns the corner
   exclusions;
3. leave the one-point complete-monotonicity test for a different exact
   RH-false witness.

## Gates

- [x] Existing formal height gap used instead of zero computation.
- [x] Every squared zero orbit placed in the exact chamber `x<2/41`.
- [x] Exact derivative polynomials through order seven proved positive.
- [x] Existing reciprocal-square sector transported to every shifted kernel.
- [x] Derivative protection extended through order thirteen.
- [x] Canonical-product assembly completed on paper.
- [x] Independent audit of the squared-variable product normalization and differentiation:
  both are now machine-checked in Lean.  The normalization is the paired reflection identity
  `xiRelativeResolventTrace_eq_reciprocalSquareResolvent` composed with the completed Hadamard
  factorization, and the differentiation is termwise with an explicit uniform reciprocal-square
  majorant on the whole positive base ray.
- [x] Lean formalization, unconditional and end to end
  (`RHTower.SquaredXiCompleteMonotonicity`), axioms `[propext, Classical.choice, Quot.sound]`.
- [x] 2 -> 3 formalized.
- [ ] 3 -> 4 publication-ready.

## Lean status

`formal/GaloisForLFunctions/RHTower/SquaredXiCompleteMonotonicity.lean`, axioms
`[propext, Classical.choice, Quot.sound]` throughout.  The Lean theorem is **strictly stronger than
this card in two independent directions**: the base ray is the whole of `y > 0` rather than
`y > 1/4`, and the protected derivative range reaches order eighteen rather than thirteen.

- `xiSquaredNode` — the squared centered spectral coordinate `alpha_q^2 = (v - u) - 2 i a b` in the
  zero coordinates `u = (Re rho - 1/2)^2`, `v = (Im rho)^2`; `xiSquaredNode_re`,
  `xiSquaredNode_im`, `xiSquaredNode_re_pos` (open critical strip plus the endpoint height gap).
- `xiShiftedReciprocalSquare_eq_inv` / `xiShiftedReciprocalSquare_eq_coordinate` — the corpus's
  Möbius-translated atom `lambda/(1 + y lambda)` is exactly the shifted resolvent kernel
  `(y + alpha_q^2)^{-1} = ((y + v - u) - (2 a b) i)^{-1}`.
- `eightyFour_mul_xiSquaredNode_im_sq_lt` — the shifted eighty-four sector `84 B^2 < A^2`, from
  `u < 1/4` and the off-line quartet gap `85 < v`; `re_xiShiftedReciprocalSquare_pow_pos` turns it
  into atomwise positivity of all fourteen powers through the tangent-`1/9` budget
  `14/9 < pi/2`.
- `re_xiShiftedReciprocalSquare_pow_pos_of_sector`, `xiCenteredSectorRatio_of_window_empty` —
  a strict unshifted sector ratio survives every positive shift, and an empty sector-failure
  window supplies that ratio.  Composed with the existing corner exclusions this gives
  `re_xiShiftedReciprocalSquare_pow_{fifteen,...,nineteen}_pos` and hence
  `re_xiShiftedReciprocalSquare_pow_pos_of_le_nineteen`.
- `xiShiftedReciprocalMoment_im_eq_zero` — the field is real: conjugation of the divisor acts on
  the squared nodes by complex conjugation (`xiSquaredNode_copyConj`).
- `hasDerivAt_xiShiftedReciprocalSquare_pow`, `hasDerivAt_xiShiftedReciprocalMoment`,
  `hasDerivAt_re_xiShiftedReciprocalMoment` — termwise differentiation of the moment tower on
  `(0, infinity)`, with the uniform majorant `(n+1) * ||lambda_q||^{n+2}`.
- `squaredXiRadialField`, `iteratedDeriv_squaredXiRadialField` — the closed form
  `g^(n)(y) = (-1)^n n!/2 * sum_q (y + alpha_q^2)^{-(n+1)}`.
- `xiShiftedReciprocalMoment_zero_eq`, `squaredXiRadialField_eq` — the exact identification with
  the card's `g`: `squaredXiRadialField y = xi'(1/2 + sqrt y)/(2 sqrt y xi(1/2 + sqrt y))`.
- **`alternating_iteratedDeriv_squaredXiRadialField_pos`** — `(-1)^n g^(n)(y) > 0` for every
  `y > 0` and every `n <= 18`; `alternating_iteratedDeriv_squaredXiRadialField_pos_of_le_thirteen`
  is this card's statement (1), and
  `alternating_iteratedDeriv_squaredXiRadialField_pos_orderFourteen` is `g^(14)(y) > 0`.
- `xiRealLogDeriv`, `hasDerivAt_xiRealLogDeriv`, `squaredXiRadialField_sq_eq`,
  **`xiRealLogDeriv_radial_gap_neg`** — statement (2), `w L'(1/2+w) - L(1/2+w) < 0` for `w > 0`.

## Log

- 2026-07-31 — Formalized unconditionally.  The whole card is one identity plus one sector: the
  reflection-paired Hadamard trace makes `2 g(y)` the tsum of `(y + alpha_q^2)^{-1}`, whose atoms
  are `(A - B i)^{-1}` with `A = y + v - u` and `B = 2 a b`.  Since the shift only enlarges `A`,
  every sector ratio proved at `y = 0` in the corpus transfers verbatim, so the protected range is
  not thirteen but eighteen, and the compact window `1/4 < y < 8` of the order-fourteen card
  disappears entirely.  The `1/4` of the card is likewise unnecessary: `xi(1/2 + w) != 0` for every
  real `w` by the source-pure zero-free band, so the field is defined and the sign holds on all of
  `y > 0`.  Termwise differentiation needed no new analytic input beyond
  `hasDerivAt_tsum_of_isPreconnected` and the corpus majorant `||mu_y|| <= ||lambda||`.
