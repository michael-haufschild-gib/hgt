# Observer ramification and horizon-exponent no-go

- **ID:** `observer-ramification-horizon-exponent-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / COUNTERMODEL / POSITIVE SURVIVOR (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [PHYSICS TRANSFER]`
  `[NO RH CLAIM] [FORMALIZED IN LEAN]`
- **Role:** proves decoder blow-up exponent depends on observer vanishing order and can occur with
  zero law change; separates observer singularity from non-Morita law horizon.

## Theorem 1: observer-ramification exponent

Suppose near `t=0`

\[
 e(t)=a|t|^m(1+o(1)),
 \qquad
 K(t)=b|t|^{-\beta}(1+o(1)),
 \tag{1}
\]

with `a,b,beta>0` and `m>0`. Then

\[
 K(t)\asymp e(t)^{-\beta/m},
 \qquad
 \lim_{t\to0}
 \frac{\log K(t)}{-\log e(t)}=\frac{\beta}{m}.
 \tag{2}
\]

If another reporter obeys

\[
 e'(t)=c\,e(t)^r(1+o(1)),
 \qquad c,r>0,
 \tag{3}
\]

its observed exponent is `beta/(mr)`.

### Proof

Taking logarithms in `(1)` gives

\[
 \log e(t)=\log a+m\log|t|+o(1),
 \qquad
 \log K(t)=\log b-\beta\log|t|+o(1).
\]

Divide and let `t->0` to obtain `(2)`. Equation `(3)` multiplies leading vanishing order by `r`,
giving stated exponent. QED.

Thus raw exponent is not intrinsic until normalized by reporter ramification order.

## Theorem 2: exact sinc square-root horizon inside fixed theory

Let `T>0` and

\[
 q_T(\delta)=\operatorname{sinc}(T\delta)
 =\frac{\sin(T\delta)}{T\delta},
 \qquad q_T(0)=1.
 \tag{4}
\]

For `|T delta|<=1`,

\[
 \frac{19}{120}(T\delta)^2
 \le1-q_T(\delta)
 \le\frac16(T\delta)^2.
 \tag{5}
\]

Writing `y=1-q_T(delta)` gives

\[
 \frac{\sqrt{6y}}{T}
 \le|\delta|
 \le\frac1T\sqrt{\frac{120y}{19}}.
 \tag{6}
\]

The inverse has exponent `1/2` and loses sign of `delta` although all dynamics lives inside one
fixed matrix/operator algebra; no non-Morita event and no Tor conormal occur.

### Proof

For `|x|<=1`, alternating Taylor series with decreasing terms gives

\[
 \frac{x^2}{6}-\frac{x^4}{120}
 \le1-\frac{\sin x}{x}
 \le\frac{x^2}{6}.
\]

Since `x^4<=x^2`, lower side is at least `(19/120)x^2`. Set `x=T delta` and invert positive
inequalities to obtain `(5)`--`(6)`. QED.

More generally fixed-theory reporter `q_r(t)=exp(-|t|^(2r))` has inverse exponent `1/(2r)` near
zero. Rational exponents alone cannot classify law-horizon singularities.

## Positive survivor: three-part observed-horizon diagnostic

For corpus applications, define **controlled observed law horizon** by evidence in three independent
slots:

1. nonzero relative law/execution complex;
2. nonzero derived conormal/Tor after specialization;
3. observer decoder exponent normalized by reporter ramification order.

This is sufficient diagnostic by definition, not theorem that every possible law change must have
observer or Tor witness. Slot 3 alone is ordinary inverse geometry. Quadratic discriminant model
has all three and exact normalized exponent; sinc recurrence has only slot 3.

## Physics consequences

- Modular flow `rho^(it) A rho^(-it)` in finite matrix algebra is inner fixed-law dynamics, not
  law-time.
- DSSYK wormhole length/Krylov growth may be physical geometric observable while remaining fixed
  model law; unbounded growth is not by itself non-Morita execution.
- Region-dependent or approximate recovery data require quantitative observer profile, but exact
  admission-algebra change must be shown before calling it law birth.

## Hostile audit

1. Theorem is elementary asymptotic analysis; novelty is anti-theatre separation in corpus.
2. Same exponent across arithmetic and physics is no evidence of same law singularity without
   matching relative complex and Tor class.
3. Choice of reporter can arbitrarily rescale exponent by `(3)`.
4. Fixed theory can still have physical spacetime dynamics; conclusion concerns mathematical law
   change only.

## Literature boundary

Modular-time/QNEC constraints: arXiv:2503.21385. DSSYK wormhole/Krylov length:
arXiv:2606.20220. Region-adapted holographic algebras: arXiv:2607.08684.

## Lean-return note

Formalized; see `observer-ramification-horizon-exponent-no-go-formalized.md`.  The note below was written before that work and is kept for the record: it is no longer a restriction.

> No Lean work authorized. If later requested, Taylor inequalities and exponent limit are elementary
> analysis targets independent of RH.

## Log

- 2026-08-08 — hostile physics transfer falsified exponent-only law-horizon identification.

## Formalized companion

`observer-ramification-horizon-exponent-no-go-formalized.md` (same directory).
