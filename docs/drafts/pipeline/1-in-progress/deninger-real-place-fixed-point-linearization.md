# Real-place fixed-point linearization

- **ID:** `deninger-real-place-fixed-point-linearization`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE WITH CONDITIONAL PAPER THEOREM
- **Label:** `DAC_REAL_PLACE_FIXED_POINT_LINEARIZATION`
- **Parent:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Statement:** the real signature boundary is a stationary arithmetic
  packet with normal flow exponent \(-2\), producing Deninger's exact
  archimedean density.

## Fixed-point formula

Deninger's foliated Lefschetz formula assigns to a stationary point \(x\)
a term of the form
\[
 \epsilon_x\,
 \frac{\operatorname{Tr}(\phi_x^t|E_x)}
      {|1-e^{\kappa_xt}|}.                                           \tag{1}
\]
For completed Riemann zeta on positive time, the required
archimedean distribution is the regular function
\[
 T_\infty(t)=\frac1{1-e^{-2t}},\qquad t>0.                           \tag{2}
\]

## Conditional theorem

`[PROVED HERE] [DAC_REAL_PLACE_FIXED_POINT_FORMULA]`

If the real-place packet has:

\[
 \epsilon_\infty=+1,\qquad
 \operatorname{Tr}(\phi_\infty^t|E_\infty)=1,\qquad
 \kappa_\infty=-2,                                                   \tag{3}
\]
then its contribution `(1)` is exactly `(2)`.  Since \(t>0\),
\(0<e^{-2t}<1\), so the absolute value in `(1)` is
\(1-e^{-2t}\).

No Gamma factor is used in this implication.

## Source conjecture

`[CONJECTURE] [DAC_REAL_PLACE_FIXED_POINT_LINEARIZATION]`

The archimedean signature boundary in
`DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT` has a geometric
realization satisfying `(3)`.  More precisely:

1. the real signature orientation defines one stationary packet;
2. its coefficient fiber is the rank-one orientation
   \(\mathbb R(-1)\);
3. its transverse normal is the quadratic real norm line;
4. the flow acts on that normal by \(e^{-2t}\);
5. the MW signature orientation gives \(\epsilon_\infty=+1\);
6. this fixed packet is compatible with the Kähler leaf orientation and
   global residue/signature reciprocity.

The proposed source of exponent \(2\) is quadratic real norm/signature
geometry: complex conjugate directions pair through
\(N_{\mathbb C/\mathbb R}(z)=z\bar z\).  This must be proved inside the
real Betti/MW boundary model, not inferred from poles of
\(\Gamma(s/2)\).

## Construction program

1. Construct the real Betti/MW signature boundary as a flow-equivariant
   closed stratum.
2. Identify its formal normal line from the quadratic norm correspondence.
3. Compute the differential of the flow and prove exponent \(-2\).
4. Match its orientation with the global arithmetic trace.
5. Apply `DAC_REAL_PLACE_FIXED_POINT_FORMULA`, then compare `(2)` with
   the independently formalized archimedean explicit-formula
   distribution.

## Falsifiers

- Exponent \(-1\) gives the wrong Gamma factor.
- Reading exponent \(-2\) from the target Gamma poles is circular unless
  the source normal-line computation is independently proved.
- A signature class without a stationary geometric packet does not
  justify a fixed-point term.
- Wrong orientation changes the sign of the archimedean density.

## Current status

- Conditional fixed-point calculation: paper-proved.
- Target density and its arbitrary-test explicit-formula identity:
  already formalized independently.
- Source real packet, quadratic normal line, exponent, and orientation:
  open.

**Verdict:** `ACTIVE SOURCE CONJECTURE; ARCHIMEDEAN TRACE REDUCED TO ONE
NORMAL-DERIVATIVE COMPUTATION`.

## Log

- 2026-07-26 — Isolated the exact source data yielding
  \((1-e^{-2t})^{-1}\).
