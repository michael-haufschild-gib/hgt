# Squared-Xi radial jets have a sign-aligned reverse-Bessel prime source

- **ID:** `squared-xi-radial-jet-reverse-bessel-source-alignment`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / completed-source reduction
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [SOURCE ALIGNMENT FORMALIZED]`
- **Sources:** `XiCollapseDirichletLeg.lean`; `CCMShiftedXiCancellation.lean`;
  `CCMSharpPrimeWindowContinuation.lean`
- **Statement:** Every alternating squared-coordinate jet of the real absolute-Euler Xi
  logarithmic derivative is a reverse-Bessel weighted completed jet.  In the split source, all
  von Mangoldt jet terms have the same negative sign.  The pole and Euler terms admit an exact
  cancellation-preserving regrouping through the pole-filled zeta function.

## Radial-jet coefficients

For `0<=j<=n`, set

```text
b_(n,j) = (2*n-j)! / (2^(n-j)*(n-j)!*j!).                 (1)
```

Equivalently, with coefficients outside `0<=j<=n` set to zero,

```text
b_(0,0)=1,
b_(n+1,j)=(2*n+1-j)*b_(n,j)+b_(n,j-1).                  (2)
```

In particular every `b_(n,j)` is a positive integer.  Write

```text
B_n(x)=sum_(j=0)^n b_(n,j)*x^j.                          (3)
```

This is the positive-coefficient reverse-Bessel polynomial in the normalization forced by the
squared-coordinate derivative.

## Exact radial-jet theorem `[PROVED HERE]`

Let

```text
s=1/2+w,              w>1/2,
L(s)=xi'(s)/xi(s),
F(w)=L(1/2+w)/w,
D=(1/(2*w))*d/dw.
```

Then, for every `n>=0`,

```text
D^n F(w)
 = 2^(-n)*w^(-2*n-1)
   *sum_(j=0)^n (-1)^(n-j)*b_(n,j)*w^j*L^(j)(s).        (4)
```

Consequently the positive rescaling of the RH-necessary alternating sign is

```text
Q_n(w)
 :=(-1)^n*2^n*w^(2*n+1)*D^n F(w)
 = sum_(j=0)^n (-1)^j*b_(n,j)*w^j*L^(j)(s).             (5)
```

### Proof

The case `n=0` is immediate.  Suppose `(4)` holds at `n`.  Applying
`D=(2*w)^(-1)d/dw` to a summand gives

```text
D[w^(j-2*n-1)*L^(j)(s)]
 = (1/2)*(j-2*n-1)*w^(j-2*n-3)*L^(j)(s)
   +(1/2)*w^(j-2*n-2)*L^(j+1)(s).                       (6)
```

After shifting the second index, the coefficient of the `j`th jet is `(2)` with the sign
`(-1)^(n+1-j)`.  This proves `(4)` by induction.  Multiplying by the positive radial scale gives
`(5)`.  Expanding `(2)` verifies `(1)` by the factorial identities.  `QED`

For

```text
g(y)=xi'(1/2+sqrt(y))/(2*sqrt(y)*xi(1/2+sqrt(y))),
```

one has `g^(n)(w^2)=(1/2)D^nF(w)`.  Thus, for `w>0`,

```text
(-1)^n*g^(n)(w^2)<0  iff  Q_n(w)<0.                     (7)
```

## Von Mangoldt sign alignment `[PROVED HERE]`

On `s>1`, the formalized Xi jet split is

```text
L^(j)(s)=R_j(s)+G_j(s)+(-1)^(j+1)*E_j(s),               (8)
```

where `R_j` is the rational jet, `G_j` is the half-argument digamma jet, and

```text
E_j(s)=sum_(m>=1) Lambda(m)*(log m)^j*m^(-s)>0           (9)
```

for every `j`.  Substitution in `(5)` gives

```text
Q_n(w)=A_n(w)-P_n(w),                                   (10)

A_n(w)=sum_(j=0)^n (-1)^j*b_(n,j)*w^j*(R_j(s)+G_j(s)),

P_n(w)=sum_(j=0)^n b_(n,j)*w^j*E_j(s)
      =sum_(m>=1) Lambda(m)*m^(-s)*B_n(w*log m)>0.       (11)
```

The prime sign is independent of both `j` and the parity of `n`: the outer alternating sign in
`Q_n` exactly cancels the alternating von Mangoldt jet sign.  Hence the Euler source always pushes
toward an RH-disproof witness; the completed rational--Gamma source supplies the opposing term.

## Cancellation-preserving form `[PROVED HERE]`

The separate quantities `A_n` and `P_n` are a bad comparison near `s=1`.  The pole-filled function

```text
Zreg(s)=(s-1)*zeta(s),
```

already exists in the formal corpus as `regularizedRiemannZeta`, including the value `Zreg(1)=1`
and differentiability at the filled point.  The corpus proves, away from `s=1`,

```text
(log Zreg)'(s)=1/(s-1)+zeta'(s)/zeta(s).                 (12)
```

Therefore

```text
L(s)=1/s-log(pi)/2+(1/2)*digamma(s/2)+(log Zreg)'(s),   (13)
```

and `(5)` may be applied directly to the four terms in `(13)`.  This is an exact regrouping of
the polar and Euler jets before any inequality is taken.  It remains analytic through `s=1`, so
it is the correct compact-window coordinate.

## Order-fourteen reduction

The prior protected-sector theorems leave only

```text
n=14,                  1/2<w<sqrt(8).                   (14)
```

At this order the required certificate is

```text
Q_14(w)<0.                                                 (15)
```

Equations `(5)` and `(13)` reduce `(15)` to a finite order-fourteen jet inequality for
`log Zreg`, the elementary `1/s` term, and the half-argument digamma term.  No zero location and
no numerical evaluation enter this reduction.

`[OPEN CORE]` Prove `(15)` at one exact `w` in `(14)`, or prove a growing-order analogue, using
an exact integral or alternating expansion for the regularized-zeta logarithmic jet.  A termwise
comparison of `1/(s-1)` with the von Mangoldt series is not admissible because it destroys `(12)`.

## Lean certificate

The source-alignment portion is formalized in

`formal/GaloisForLFunctions/RHTower/SquaredXiRadialJetSourceAlignment.lean`.

The module defines the positive recursive magnitudes, the alternating completed jet polynomial,
and its rational--Gamma and prime pieces.  It proves unconditionally on `Re(1/2+w)>1`:

```text
squaredXiAlternatingJetPolynomial
  = squaredXiAlternatingRationalGammaJetPolynomial
    - squaredXiPrimeJetPolynomial.
```

The formal prime polynomial has no alternating coefficient.  The module is wired into the
`RHTower` umbrella.  Its exact target build and touched-file check pass; the axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.  The repository-wide lint still reports
unrelated concurrent modules absent from their umbrellas, but no error for this module.

The exact coefficient theory of equation (1) is now formalized unconditionally in the same module:

- `squaredRadialJetWeightClosedForm n j = (2n−j)! / (2^{n−j} (n−j)! j!)` (in `ℚ`);
- `squaredRadialJetWeight_eq_closedForm (n j) (hj : j ≤ n) :`
  `(squaredRadialJetWeight n j : ℚ) = squaredRadialJetWeightClosedForm n j` — the recurrence-defined
  magnitudes equal the reverse-Bessel closed form on the triangular range, proved by induction on
  `n` (the `n = m + k + 1` substitution eliminates every truncated subtraction so the recurrence
  step is a pure `field_simp; ring` factorial identity);
- `squaredRadialJetWeight_pos (n j) (hj : j ≤ n) : 0 < squaredRadialJetWeight n j` — every magnitude
  is a positive integer (equation (1)'s positivity), read off from the closed form;
- `squaredRadialJetWeight_eq_zero_of_lt (n j) (h : n < j) : squaredRadialJetWeight n j = 0` — the
  triangular support.

`#print axioms` on all three: `propext`, `Classical.choice`, `Quot.sound` only.  Still open in Lean:
the analytic radial-derivative identity (4)/(5), which requires the differentiability/analyticity of
`xiLogDeriv` on `Re(s) > 1` and the iterated-derivative shift; and the `[OPEN CORE]` `Q_14(w) < 0`.

## Gates

- [x] Exact radial-jet coefficients and recurrence proved (closed form + positivity now formalized:
  `RHTower.squaredRadialJetWeight_eq_closedForm`, `squaredRadialJetWeight_pos`).
- [x] Alternating sign normalization connected to the squared-Xi derivative.
- [x] All von Mangoldt jets sign-aligned into one positive reverse-Bessel polynomial.
- [x] Pole/Euler cancellation preserved by the existing pole-filled zeta object.
- [ ] Independent audit of the reverse-Bessel normalization.
- [x] Formalize the recursive weights and source split `(10)`.
- [ ] Formalize the analytic radial-derivative identity `(4)` and its positive rescaling `(5)`.
- [ ] Prove a strict negative completed source jet.
- [ ] Wire the negative jet to `not RiemannHypothesis` in Lean.

## Log

- 2026-07-24 -- Formalized the exact reverse-Bessel closed form (1) and positivity of the radial-jet
  magnitudes in `RHTower.squaredRadialJetWeight_eq_closedForm` / `_pos` (plus the triangular support
  `_eq_zero_of_lt`), connecting the recurrence-defined `squaredRadialJetWeight` to its closed form.
  Axioms clean; module builds. Remaining Lean gaps: the analytic identity (4)/(5) (needs
  `xiLogDeriv` analyticity on `Re(s)>1`) and the `[OPEN CORE]` `Q_14(w)<0`.
