# Deninger tensor-square mate identification of actual Gamma boundary

- **ID:** `deninger-gamma-tensor-square-mate-identification`
- **Route:** L / Deninger finite failure-nerve mate
- **Status:** fully proved on paper; RH not proved
- **Input:** actual ordered `(2,3)` Gamma/co-Poisson Calderon--Witt witness;
  bilateral Deninger half-density character

## Theorem

For (n>1) and (s\in\mathbb C), let

\[
 \lambda_n(s)=n^{1/2-s}
\]

be the associated-grade Deninger half-density character.  Its tensor-square
radial source-inverse/analytic-dagger mate curvature is

\[
 K_n(s)=\|\lambda_n(s)\|^{-2}-\|\lambda_n(s)\|^2.
 \tag{1}
\]

Then

\[
 K_n(s)=2\sinh\bigl((2\Re s-1)\log n\bigr).
 \tag{2}
\]

Let (q) be an actual Xi-divisor copy, write

\[
 f_q=2\left(\Re\rho_q-\frac12\right),
\]

and let (b_\Gamma(q)) be the actual Gamma/co-Poisson reflection-odd
boundary coefficient at the canonical ordered `(2,3)` Calderon--Witt
witness.  If (A_{23}) is its undeformed exterior amplitude, then

\[
 \boxed{
 b_\Gamma(q)=\left(-\frac{A_{23}}2\right)K_6(\rho_q),
 \qquad -\frac{A_{23}}2>0.
 }
 \tag{3}
\]

Thus actual Gamma admission coefficient is, before bounded normalization,
exactly a strictly positive calibration of the tensor-square radial mate
curvature of the Deninger associated-grade character at composite degree
(6=2\cdot3).

## Proof

The half-density norm law gives

\[
 \|\lambda_n(s)\|=n^{1/2-\Re s}.
\]

Put (d=2\Re s-1).  Then

\[
 \|\lambda_n(s)\|^{-2}=n^d,
 \qquad
 \|\lambda_n(s)\|^2=n^{-d}.
\]

Since (n^{\pm d}=\exp(\pm d\log n)),

\[
 K_n(s)=e^{d\log n}-e^{-d\log n}
       =2\sinh(d\log n),
\]

which proves `(2)`.

For the actual ordered `(2,3)` Gamma witness, the already proved explicit
formula is

\[
 b_\Gamma(q)=A_{23}\sinh(f_qR_{23}),
\]

where (A_{23}<0) and (R_{23}) is the sum of the two depth-zero modular
rates.  Each depth-zero rate is minus the prime logarithm, hence

\[
 R_{23}=-\log2-\log3=-\log6.
\]

Therefore

\[
\begin{aligned}
 b_\Gamma(q)
 &=A_{23}\sinh(-f_q\log6)\\
 &=-A_{23}\sinh(f_q\log6)\\
 &=\left(-\frac{A_{23}}2\right)K_6(\rho_q),
\end{aligned}
\]

using (f_q=2\Re\rho_q-1) and `(2)`.  Since (A_{23}<0), the calibration
constant is strictly positive.

No Xi zero location, RH, source-null-homotopy, or conormal-dependent metric
is assumed.

## What is new and what is not

Not new:

- half-density character and its critical-line norm criterion;
- radial mate curvature
  (|\lambda\|^{-2}-\|\lambda\|^2=2\sinh(2\log|\lambda|^{-1})), already
  present in Burnol/Sonin full-history work;
- hyperbolic-sine formula for actual Gamma boundary.

New theorem is exact equality `(3)` between these independently constructed
objects, including forced composite degree (6), sign, and positive
calibration.  Corpus search found no previous Deninger/Burnol mate theorem
identified with the actual Calderon--Witt Gamma admission witness.

This is a finite associated-grade comparison, not the missing cofinal source
producer.  It closes a precise part of
`FINITE_EPG_FAILURE_NERVE_MATE_COMPARISON`: on the radial associated grade,
the concrete Gamma reporter already reads the tensor-square source
inverse/dagger mate curvature at its canonical witness.

## Frontier left

Still missing:

1. lift `(3)` from radial character to the full filtered finite
   prime/depth reporter, retaining zero-rate Euler gauge and terminal pole;
2. prove compatibility over prime cutoff, exponent depth, and Gamma aperture;
3. pass strict, nonannihilatingly through Xi Cartier base change;
4. derive a source Bianchi/null-homotopy identity for the resulting positive
   quadratic Green curvature.

Any construction which inserts (s=\rho_q) before the filtered source mate
or defines its metric by requiring `(3)` is rejected as circular.

## Formalization target

Lean should prove unconditionally:

- formula `(2)` from existing `bilateralHalfDensityCharacter` norm law;
- (R_{23}=-\log6);
- exact comparison `(3)`;
- strict positivity of calibration constant;
- zero-set compatibility as a corollary, not as an assumption.

