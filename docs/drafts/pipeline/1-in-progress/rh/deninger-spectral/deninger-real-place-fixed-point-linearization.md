# Real-place fixed-point linearization

- **ID:** `deninger-real-place-fixed-point-linearization`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE WITH CONDITIONAL PAPER THEOREM
- **Label:** `DAC_REAL_PLACE_FIXED_POINT_LINEARIZATION`
- **Parent:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Statement:** the real signature boundary is a stationary arithmetic
  packet with normal flow exponent \(-2\), producing Deninger's exact
  archimedean density.

## Primary-source correction

Deninger's real normal law is explicit, not an exponent that remains to
be guessed.  In the real orbifold coordinate
\(\mathbb R_{\ge0}\cong\mathbb R/\mu_2\), his transverse flow is
\[
 r\longmapsto e^{-2t}r,
\]
so \(\kappa_\infty=-2\).  The 2018 rational-Witt dynamical space has no
fixed points; this stationary real component belongs to the conjectural
arithmetic compactification.

`DAC_REAL_ORBIFOLD_REES_DUAL_CONORMAL_JET_TOWER` now proves that the
full even Taylor-jet product has weights \(e^{-2kt}\) and exact
positive-time character \((1-e^{-2t})^{-1}\).  Thus the remaining
source problem is global stationary-component construction and
orientation/trace gluing, not the local exponent or geometric series.

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
4. the flow acts on that normal by \(e^{-2t}\), as in Deninger's real
   Rees orbifold;
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
2. Identify its formal normal line with Deninger's real Rees orbifold.
3. Insert the proved full dual-conormal even-jet tower; do not truncate
   to the order-zero coefficient fiber.
4. Match its orientation with the global arithmetic trace.
5. Apply `DAC_REAL_PLACE_FIXED_POINT_FORMULA`, then compare `(2)` with
   the independently formalized archimedean explicit-formula
   distribution.

## Falsifiers

- Exponent \(-1\) contradicts Deninger's real Rees flow.
- Reading exponent \(-2\) from target Gamma poles remains circular;
  here it is instead primary source data.
- A signature class without a stationary geometric packet does not
  justify a fixed-point term.
- Wrong orientation changes the sign of the archimedean density.

## Current status

- Conditional fixed-point calculation: paper-proved.
- Target density and its arbitrary-test explicit-formula identity:
  already formalized independently.
- Local orbifold normal, exponent, full jet character, and arbitrary
  positive-time test identity: proved.
- Global compactified real packet, stationary leaf coefficient,
  orientation, and \(t=0\) renormalization: open.

**Verdict:** `ACTIVE SOURCE CONJECTURE; ARCHIMEDEAN TRACE REDUCED TO ONE
GLOBAL COMPACTIFICATION/ORIENTATION COMPARISON`.

## Log

- 2026-07-26 — Isolated the exact source data yielding
  \((1-e^{-2t})^{-1}\).
- 2026-07-27 — Replaced the open exponent guess by Deninger's explicit
  real Rees orbifold flow and the proved full dual-conormal even-jet
  character.
