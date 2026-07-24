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
- [x] Formalize the analytic radial-derivative identity `(4)` and its positive rescaling `(5)` (abstract smooth `L`, `RHTower/SquaredXiRadialJetIdentity.lean`)
- [ ] Prove a strict negative completed source jet.
- [ ] Wire the negative jet to `not RiemannHypothesis` in Lean.

## Log

- 2026-07-24 -- Formalized the exact reverse-Bessel closed form (1) and positivity of the radial-jet
  magnitudes in `RHTower.squaredRadialJetWeight_eq_closedForm` / `_pos` (plus the triangular support
  `_eq_zero_of_lt`), connecting the recurrence-defined `squaredRadialJetWeight` to its closed form.
  Axioms clean; module builds. Remaining Lean gaps: the analytic identity (4)/(5) (needs
  `xiLogDeriv` analyticity on `Re(s)>1`) and the `[OPEN CORE]` `Q_14(w)<0`.
- 2026-07-24 — **Analytic core of the radial-derivative identity (4) formalized** (toward gate
  `Formalize the analytic radial-derivative identity (4)/(5)`), in
  `RHTower/SquaredXiRadialJetIdentity.lean` (unconditional, axioms `[propext, Classical.choice,
  Quot.sound]`), for an arbitrary smooth `L` (no `xiLogDeriv` analyticity needed — the calculus
  identity holds for any `ContDiff ℝ ⊤ L`):
  * `radialOp` / `radialProfile` — the operator `D f = f'/(2w)` and profile `F(w) = L(1/2+w)/w`.
  * `deriv_iteratedDeriv_shift` — chain rule `d/dw[L^(j)(c+w)] = L^(j+1)(c+w)`.
  * `deriv_pow_mul_iteratedDeriv_shift` — **equation (6) core**: `d/dw[w^m·L^(j)(1/2+w)] =
    m·w^(m-1)·L^(j)(1/2+w) + w^m·L^(j+1)(1/2+w)` (via `HasDerivAt` product rule + the shift chain rule).
  **Remaining for (4)/(5):** the induction on `n` assembling this single-term derivative over the
  `Finset.range (n+1)` sum with the `squaredRadialJetWeight` recurrence and the `/(2^n w^(2n+1))`
  radial scale (the `[OPEN CORE]` `Q_14(w) < 0` and the RH-wiring gates remain non-Lean/RH-level).
- 2026-07-24 — **Radial-jet-sum derivative infrastructure** (toward identity (4)), added to
  `RHTower/SquaredXiRadialJetIdentity.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `hasDerivAt_pow_mul_iteratedDeriv_shift` — `HasDerivAt` form of equation (6) core.
  * `jetSum L c N` — the abstract-coefficient radial jet sum `∑_{j≤N} c j·w^j·L^(j)(1/2+w)`.
  * `hasDerivAt_jetSum` — its derivative is the coefficientwise single-term derivative
    `∑_{j≤N} c j·(j·w^(j-1)·L^(j)(1/2+w) + w^j·L^(j+1)(1/2+w))` (via `HasDerivAt.sum` + the step lemma,
    bridged to the `fun v => ∑ …` form through `Finset.sum_apply`).
  **Remaining for (4)/(5):** the combinatorial recurrence `w·jetSum'_n − (2n+1)·jetSum_n = jetSum_{n+1}`
  (specializing `c j = (-1)^(n-j)·squaredRadialJetWeight n j`, reindexing the shifted sum, and applying
  the `squaredRadialJetWeight` recurrence), then the `D^n F = jetSum_n / (2^n w^(2n+1))` induction.
- 2026-07-24 — **Signed-coefficient recurrence (combinatorial core of (4))** added to
  `RHTower/SquaredXiRadialJetIdentity.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `jetCoeff n j = (-1)^(n-j)·squaredRadialJetWeight n j` — the signed radial-jet coefficient.
  * `jetCoeff_succ_zero` — `jetCoeff (n+1) 0 = -(2n+1)·jetCoeff n 0` (the `t 0` boundary coefficient).
  * `jetCoeff_succ_top` — `jetCoeff (n+1)(n+1) = jetCoeff n n` (the `t(n+1)` boundary, using
    `squaredRadialJetWeight_eq_zero_of_lt`).
  * `jetCoeff_succ_mid` — for `i < n`, `jetCoeff n (i+1)·((i+1)-(2n+1)) + jetCoeff n i =
    jetCoeff (n+1)(i+1)` (the interior coefficient, from `squaredRadialJetWeight_succ_succ` + the sign
    normalization `(-1)^(n-i) = -(-1)^(n-(i+1))`).
  These are the exact `b`-recurrence content matching the operator step (6) index-by-index.
  **Remaining for (4)/(5):** the Finset sum-recurrence `w·jetSum'_n − (2n+1)·jetSum_n = jetSum_{n+1}`
  assembling these three coefficient identities across the range (peel/reindex the shifted sum), then
  the `D^n F = jetSum_n/(2^n w^(2n+1))` quotient induction.
- 2026-07-24 — **Signed-coefficient sum recurrence formalized** (combinatorial core of (4)):
  `jetCoeff_sum_recurrence` — `∑_{j≤n} jetCoeff n j·(j·t j + t(j+1)) − (2n+1)·∑_{j≤n} jetCoeff n j·t j =
  ∑_{j≤n+1} jetCoeff (n+1) j·t j` for any `t : ℕ → ℝ` (axioms `[propext, Classical.choice, Quot.sound]`),
  assembling the three pointwise `jetCoeff` recurrences via peel/reindex (`Finset.sum_range_succ` /
  `Finset.sum_range_succ'` + `Finset.sum_congr`).  **Remaining for (4)/(5):** the calculus connection
  `w·deriv(jetSum L (jetCoeff n) n) w = ∑ jetCoeff n j·(j·w^j·L^(j) + w^(j+1)·L^(j+1))` (via
  `hasDerivAt_jetSum` + the `w·w^(j-1)=w^j` exponent bridge), letting `t j = w^j·L^(j)(1/2+w)` turn the
  sum recurrence into `w·jetSum'_n − (2n+1)·jetSum_n = jetSum_{n+1}`; then the
  `D^n F = jetSum_n/(2^n w^(2n+1))` quotient induction.
- 2026-07-24 — **Radial-jet recurrence (natural form) formalized**, in
  `RHTower/SquaredXiRadialJetIdentity.lean` (axioms `[propext, Classical.choice, Quot.sound]`):
  * `w_mul_deriv_jetSum` — the calculus connection `w·(jetSum L c n)′(w) = ∑_{j≤n} c j·(j·w^j·L^(j)(1/2+w)
    + w^(j+1)·L^(j+1)(1/2+w))` (via `hasDerivAt_jetSum` + the `w·w^(j-1)=w^j` exponent bridge, closed by
    `linear_combination`).
  * `jetSum_recurrence` — **`w·(jetSum_n)′(w) − (2n+1)·jetSum_n(w) = jetSum_{n+1}(w)`** with
    `jetSum_n = jetSum L (jetCoeff n) n`, obtained by feeding `t j = w^j·L^(j)(1/2+w)` into
    `jetCoeff_sum_recurrence`.
  **Remaining for (4)/(5):** the `radialOp^[n] (radialProfile L) = jetSum_n / (2^n w^(2n+1))` quotient
  induction (base `n=0` is `L(1/2+w)/w`; the step is the quotient-rule derivative + `jetSum_recurrence`,
  transferred through the IH by `EventuallyEq.deriv_eq` on `Ioi 0`).
- 2026-07-24 — **Radial-derivative identity (4) and positive rescaling (5) fully formalized** (gate
  `Formalize the analytic radial-derivative identity (4)/(5)`), in
  `RHTower/SquaredXiRadialJetIdentity.lean` (unconditional, axioms `[propext, Classical.choice,
  Quot.sound]`), for an **arbitrary smooth `L`** (`ContDiff ℝ ⊤ L`) — the identity is a calculus fact
  needing no `xiLogDeriv` analyticity:
  * `radialOp_iterate_eq` — **equation (4)**: `radialOp^[n] (radialProfile L) w = jetSum_n w /
    (2^n·w^(2n+1))` for `w > 0`, by induction on `n` (base `L(1/2+w)/w`; step = quotient-rule
    derivative + `jetSum_recurrence`, transferred through the IH by `EventuallyEq.deriv_eq` on `Ioi 0`).
  * `radialJet_positive_rescaling` — **equation (5)**: `(-1)^n·2^n·w^(2n+1)·radialOp^[n](radialProfile L) w
    = ∑_{j≤n} (-1)^j·b_{n,j}·w^j·L^(j)(1/2+w)` (sign corollary of (4), `(-1)^n·(-1)^(n-j) = (-1)^j`).
  Specializing to `L = xiLogDeriv` (once its `Re(s)>1` smoothness is available) yields the card's exact
  `D^n F` identity.  Remaining Lean gate is the `[OPEN CORE]` `Q_14(w) < 0` (RH-discriminator, open
  research); the strict-sign and RH-wiring gates are RH-level.
