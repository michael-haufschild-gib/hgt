# Squared-Xi radial jets have a sign-aligned reverse-Bessel prime source

- **ID:** `squared-xi-radial-jet-reverse-bessel-source-alignment`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4, fully unconditional) / completed-source reduction
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [FORMALIZED END TO END]`
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

## Order-fourteen reduction `[REFUTED]`

The reduction formerly left the single target

```text
n=14,                  1/2<w<sqrt(8),                   (14)
Q_14(w)<0.                                              (15)
```

`(15)` is **false**.  The sector-power positivity of the shifted reciprocal square is free in the
shift parameter, so it protects every order through eighteen at every positive radius, with no
far-right cutoff.  Transported through `(7)` this gives, unconditionally,

```text
Q_n(w)>0   for all n<=18 and all w>0.                   (16)
```

In particular the order-fourteen window `(14)` is empty and no exact `w` can satisfy `(15)`.

`[OPEN CORE]` The witness frontier is therefore `n>=19`: prove `Q_n(w)<0` for some order
`n>=19` and some `w>0`, or prove a growing-order analogue, using an exact integral or alternating
expansion for the regularized-zeta logarithmic jet.  A termwise comparison of `1/(s-1)` with the
von Mangoldt series is not admissible because it destroys `(12)`.

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
`RHTower` umbrella.  Direct source checks and exact target builds pass; the axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

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

`#print axioms` on all three: `propext`, `Classical.choice`, `Quot.sound` only.  The analytic
radial-derivative identity, genuine-Xi specialization, order-fourteen refutation, and every-order
RH discriminator are discharged by the modules below.  The former `Q_14(w) < 0` target is not an
open Lean obligation: it is false, and `completedSourceJet_orderFourteen_pos` proves its negation.

### `GaloisForLFunctions/RHTower/SquaredXiRadialJetXiSpecialization.lean`

The abstract radial-jet identity specialized to the genuine completed Xi, and the squared-coordinate
bridge `(7)`.

- `xi_ofReal_ne_zero`, **`contDiff_xiRayLogDeriv`** — `xi` is entire and has no zero on the real
  axis, so `xi'/xi` is holomorphic on an open neighbourhood of `ℝ` and its real trace is smooth at
  every order on all of `ℝ`.  This is exactly the hypothesis the abstract identity needed, and it
  removes the card's "once `xiLogDeriv` smoothness is available" caveat.
- `xiRayLogDeriv_shift`, `radialProfile_xiRayLogDeriv` — the radial profile of `xi'/xi` is twice the
  squared-coordinate field at `w^2`.
- `radialOp_iterate_congr_of_pos`, `radialOp_iterate_const_mul`,
  **`hasDerivAt_iteratedDeriv_squaredXiRadialField`**, **`radialOp_iterate_comp_sq`** — the radial
  operator `D = (2w)^{-1} d/dw` is the pullback of `d/dy` under `y = w^2`, so its `n`-th iterate on
  a squared-coordinate composite is the `n`-th `y`-derivative at `w^2`.
- **`radialOp_iterate_radialProfile_xi`** — **equation `(4)` for the completed Xi**:
  `D^n F w = 2 g^(n)(w^2)`.
- `completedSourceJet` — the card's `Q_n w = sum_j (-1)^j b_{n,j} w^j L^(j)(1/2+w)`.
- **`completedSourceJet_eq`** — **equations `(5)` and `(7)` for the completed Xi**:
  `Q_n w = (-1)^n 2^{n+1} w^{2n+1} g^(n)(w^2)`, so `Q_n w < 0` and `(-1)^n g^(n)(w^2) < 0` are the
  same statement.
- **`completedSourceJet_pos`**, **`completedSourceJet_orderFourteen_pos`**,
  `not_completedSourceJet_neg_of_le_eighteen` — **equation `(16)`**: `Q_n w > 0` for every `n <= 18`
  and every `w > 0`, unconditionally.  The order-fourteen witness window is empty.

### `GaloisForLFunctions/RHTower/SquaredXiSourceJetRHWiring.lean`

The discriminator: a strictly negative completed source jet disproves RH.

- **`xiSquaredNode_im_eq_zero_of_riemannHypothesis`** — under RH every centered spectral point is
  real, so the squared node is real.  Unconditionally its real part is already positive, so under
  RH the node is a *positive real*.
- **`re_xiShiftedReciprocalSquare_pow_pos_of_riemannHypothesis`** — hence every shifted reciprocal
  power is a positive real, at **every** order: the sector restriction that caps the unconditional
  argument at order nineteen disappears.
- **`re_xiShiftedReciprocalMoment_pos_of_riemannHypothesis`**,
  **`alternating_iteratedDeriv_squaredXiRadialField_pos_of_riemannHypothesis`** — the
  squared-coordinate field is completely monotone at every order under RH.
- **`completedSourceJet_pos_of_riemannHypothesis`** — `Q_n w > 0` for every `n` and every `w > 0`
  under RH.
- **`not_riemannHypothesis_of_completedSourceJet_neg`** — the contrapositive: one strictly negative
  completed source jet at one positive radius disproves the Riemann hypothesis.  Combined with
  `(16)`, any such witness must have order `n >= 19`.

### `GaloisForLFunctions/RHTower/SquaredXiRadialJetSourceCompletion.lean`

The end-to-end interfaces missing from the earlier certificate are now unconditional:

- `completedSourceJet_eq_re_alternatingJetPolynomial` identifies the actual real `Q_n` with the
  real part of the complex sign-aligned source polynomial;
- `completedSourceJet_eq_rationalGamma_sub_prime` transports the exact complex split to the actual
  completed source jet;
- `re_LSeries_logMul_vonMangoldt_real`, `squaredXiPrimeJetPolynomial_re_eq`, and
  `reverseBesselVonMangoldtSource_pos` prove equation `(11)` and its strict positivity for the full
  von Mangoldt series, not merely for a finite aperture;
- `regularizedZetaRayLogDeriv_eq`, `contDiffAt_regularizedZetaRayLogDeriv_one`, and
  `completedSourceJet_eq_archimedean_add_regularized` prove equations `(12)`--`(13)` while keeping
  the pole/Euler cancellation smooth through `s = 1`;
- `completedSourceJet_eq_archimedean_add_discrepancy` gives the exact
  Chebyshev--Stieltjes cancellation-preserving form.

All five original card leaves plus the completion leaf pass under `lake env lean`; the completion
module's final `lake build` passes.  Seventeen load-bearing capstones report exactly
`[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] Exact radial-jet coefficients and recurrence proved (closed form + positivity now formalized:
  `RHTower.squaredRadialJetWeight_eq_closedForm`, `squaredRadialJetWeight_pos`).
- [x] Alternating sign normalization connected to the squared-Xi derivative.
- [x] All von Mangoldt jets sign-aligned into one positive reverse-Bessel polynomial.
- [x] Pole/Euler cancellation preserved by the existing pole-filled zeta object.
- [x] Independent audit of the reverse-Bessel normalization: recurrence, factorial closed form,
  triangular support, adjacent-ratio identity, and positive integer range agree.
- [x] Formalize the recursive weights and source split `(10)`.
- [x] Formalize the analytic radial-derivative identity `(4)` and its positive rescaling `(5)` (abstract smooth `L`, `RHTower/SquaredXiRadialJetIdentity.lean`)
- [x] Formalize the specialization of `(4)`/`(5)` to `L = xi'/xi` and the squared-coordinate
  bridge `(7)` (`RHTower/SquaredXiRadialJetXiSpecialization.lean`).
- [x] Strict negative completed source jet at order fourteen: **refuted**, `(16)`
  (`RHTower.completedSourceJet_orderFourteen_pos`); the witness frontier is `n >= 19`.
- [x] Dispose of the strict-negative search correctly: existence at `n >= 19` remains an explicit
  open research problem and is not asserted by this theorem card; the proved discriminator is
  formalized without assuming such a witness.
- [x] Wire the negative jet to `not RiemannHypothesis` in Lean
  (`RHTower.not_riemannHypothesis_of_completedSourceJet_neg`).

## Log

- 2026-08-01 — Promoted to Stage 3. Added
  `RHTower/SquaredXiRadialJetSourceCompletion.lean`, closing complex-to-real source transport,
  strict positivity of the full reverse-Bessel von Mangoldt source, pole-filled-zeta smoothness at
  one, and the exact Chebyshev discrepancy. Six direct sources, final completion-module build, and
  seventeen-capstone axiom audit pass; only standard foundations occur.

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
- 2026-07-31 — **Order-fourteen target refuted; specialization to the genuine Xi completed.**  The
  abstract identity `(4)`/`(5)` needed a globally smooth profile, and the completed Xi supplies one:
  `xi` is entire with no real zero, so `xi'/xi` is holomorphic on an open neighbourhood of the real
  axis and its real trace is smooth at every order.  With that, `D` is recognized as the exact
  pullback of `d/dy` under `y = w^2`, which turns `(5)` into the card's `(7)`:
  `Q_n w = (-1)^n 2^{n+1} w^{2n+1} g^(n)(w^2)`.  The squared-Xi complete-monotonicity theorem then
  gives `Q_n w > 0` for every `n <= 18` and every `w > 0`, unconditionally, so the reduction's
  order-fourteen certificate `Q_14(w) < 0` is false and the window `(14)` is empty.  The witness
  frontier moves to `n >= 19`; the RH-wiring gate is unchanged.
- 2026-07-31 — **RH wiring closed.**  Under RH the centered spectral points are real, so the squared
  node is a positive real and every shifted reciprocal power is a positive real at every order —
  the sector bound that caps the unconditional argument at order nineteen is not needed.  Hence the
  squared-coordinate field is completely monotone at all orders under RH, `Q_n w > 0` for every `n`
  and `w > 0`, and contrapositively one strictly negative completed source jet disproves RH.  With
  `(16)` this locates the discriminator exactly: a witness exists only at order `n >= 19`, and the
  card's remaining gate is that single open inequality.
