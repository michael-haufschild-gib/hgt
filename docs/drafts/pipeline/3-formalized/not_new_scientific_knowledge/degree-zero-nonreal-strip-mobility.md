# An integral multiplicative FE polynomial with only nonreal off-line zeros

- **ID:** degree-zero-nonreal-strip-mobility
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / sharp constraint-class counterexample
- **Date:** 2026-07-10
- **Scientific status:** `[BRIDGE]`, not new scientific knowledge.  The construction strengthens
  the project boundary by simultaneously imposing a zero-free real axis and excluding
  critical-line zeros, but it is an elementary reciprocal-polynomial specialization and does not
  survive the parent-theory novelty gate.
- **Lean:** `formal/GaloisForLFunctions/RHTower/DegreeZeroNonrealOffline.lean`.

## Statement

Define

\[
D(s)=1+40\,16^{-2s}+256\,16^{-4s}.
\]

Then:

1. `D` is an entire Dirichlet polynomial with integer-valued multiplicative coefficient function
   supported on \(\{1,256,65536\}\).
2. It satisfies the exact functional equation
   \[
   D(s)=16^{\,2-4s}D(1-s).
   \]
3. It is strictly positive on the real axis.
4. Every zero is nonreal, lies off \(\operatorname{Re}s=1/2\), and the zero set meets both open
   half-strips \(0<\operatorname{Re}s<1/2\) and \(1/2<\operatorname{Re}s<1\).
5. In particular, `D` has a simple nonreal zero strictly inside the open critical strip and off
   the critical line.

Consequently exact FE symmetry, integrality, multiplicativity, finite entire Dirichlet-series
realization, and absence of real zeros still do not force critical-line support.

## Reciprocal polynomial

Put \(w=16^{-s}\) and

\[
P(w)=1+40w^2+256w^4.
\]

Equivalently, with \(u=4w\),

\[
P(w)=R(u),\qquad R(u)=u^4+\frac52u^2+1.
\]

The polynomial `R` is reciprocal:

\[
R(u)=u^4R(u^{-1}).
\]

Since \(16^{2-4s}=256w^4=u^4\) and
\(4\,16^{-(1-s)}=u^{-1}\), reciprocity gives the displayed functional equation.

## Integral multiplicative coefficients

Let `a` be the arithmetic function

\[
a(1)=1,\qquad a(256)=40,\qquad a(65536)=256,
\]

and `a(n)=0` otherwise.  All three support points are powers of the single prime `2`:

\[
1=2^0,\qquad 256=2^8,\qquad 65536=2^{16}.
\]

If \(\gcd(m,n)=1\) and \(mn\) belongs to this support, at most one of `m,n` is nontrivial.
Therefore \(a(mn)=a(m)a(n)\).  The finite L-series of `a` is exactly `D`.

## Zero classification

Set \(t=16^{-2s}\).  Then

\[
D(s)=1+40t+256t^2.
\]

Its two `t`-roots are

\[
t_-=-A,\qquad t_+=-B,\qquad
A=\frac1{32},\qquad B=\frac18.
\]

Both roots are negative real and distinct, so every zero of `D` is nonreal and simple.  They also
satisfy

\[
AB=\frac1{256}.
\]

For a solution of \(16^{-2s}=-A\), the real part is

\[
\beta_A=-\frac{\log A}{2\log16}.
\]

The exact values satisfy

\[
\frac1{256}<A=\frac1{32}<\frac1{16}
\]

and hence \(1/2<\beta_A<1\).  Similarly \(1/16<B<1\), so the solutions attached to \(-B\) have real part
strictly between `0` and `1/2`.  The product relation `AB=1/256` gives
\(\beta_A+\beta_B=1\), exactly matching the functional equation.

Since \(\log A=-5\log2\) and \(\log16=4\log2\), an explicit right-half-strip zero is

\[
\rho=\frac58-i\,\frac{\pi}{8\log2}.
\]

Indeed,

\[
-2\rho\log16=-5\log2+i\pi=\log A+i\pi,
\qquad
16^{-2\rho}=-A,
\]

and hence \(D(\rho)=1-40A+256A^2=0\).  The derivative with respect to `t` at \(-A\) is

\[
40-512A=24\ne0,
\]

while the derivative of \(16^{-2s}\) never vanishes, so \(\rho\) is simple.

No zero lies on the critical line: there \(|t|=1/16\), whereas the two possible root moduli are
\(A<1/16\) and \(B>1/16\).

## Zero-free real axis

For real \(\sigma\), \(16^{-2\sigma}>0\), and therefore

\[
D(\sigma)=1+40\,16^{-2\sigma}+256\,16^{-4\sigma}>0.
\]

Thus the counterexample cannot be dismissed by adjoining the known zero-free real interval of the
Riemann zeta function; it has no real zeros anywhere.

## Significance and attack

- The earlier `dzo` witness had real zeros at `1/3` and `2/3`.  A proposed carrier could
  therefore evade it by adding the unconditional fact that zeta has no real zero in the open strip.
  This theorem closes that escape.
- The witness is still a single-prime column and therefore vertically periodic.  It does not refute
  a constraint that uses the genuinely infinite, aperiodic all-prime Euler source.
- The construction is a scaled reciprocal quartic.  Its algebra is classical in spirit, so the
  exact theorem is a routine degree-zero L-function example rather than new scientific knowledge.
  Its research value is as a sharp falsifier for insufficient RH constraint classes.

## Lean certificate

The formal module proves:

- `dzoQuartic_fe` — the exact functional equation;
- `dzoQuarticCoeff_multiplicative`, `dzoQuarticCoeff_integral`, and
  `LSeries_dzoQuarticCoeff` — the integral multiplicative Dirichlet realization;
- `dzoQuartic_ρ_eq_zero`, `ρdzoQuartic_mem_right_strip`, and
  `ρdzoQuartic_not_real` — the explicit nonreal right-half-strip zero;
- `dzoQuartic_order_one` — simplicity of that zero;
- `dzoQuartic_ofReal_re_pos` and `dzoQuartic_ofReal_ne_zero` — positivity and
  zero-freeness on the full real axis;
- `dzoQuartic_mem_class` — direct membership in `IntegralMultiplicativeFEClass` with
  conductor `256`.

The exact module build passes.  The listed public theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1: reciprocal quartic, arithmetic support, and target zero identified
- [x] 1 → 2: FE, multiplicativity, zero classification, strip location, simplicity, and real-axis
  zero-freeness proved on paper
- [x] independent algebra audit via the Lean certificates
- [x] 2 → 3: exact function, coefficient stream, FE, simple nonreal strip zero, real-axis
  positivity, and degree-zero class membership formalized
- [x] parent-theory gate: downgraded to `[BRIDGE]`; no scientific-novelty promotion
