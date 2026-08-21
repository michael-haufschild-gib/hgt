# Matched CCM oriented characteristic cocycle

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadMatchedOrientedCharacteristicCocycle`.
This is a route theorem, not an RH proof.

## New knowledge

A mass-matched prime--polar cell is not exhausted by its previously formalized even cosine
rebate.  It is the real shadow of an exact complex characteristic cocycle.  For

\[
A=\exp(\log(n)/2),\qquad \theta=2\pi r\xi,
\]

Lean proves pointwise

\[
A e^{r/2}(1-e^{i\theta})+A e^{-r/2}(1-e^{-i\theta})
=A\cosh(r/2)(2-2\cos\theta)-i\,2A\sinh(r/2)\sin\theta.
\]

After radial integration and arithmetic phase transport:

- real channel is exactly the matched cosine profile plus the Suzuki sine-current coupling;
- symbol is Hermitian under `xi ↦ -xi`;
- symbol vanishes at spectral center;
- finite matched prime--polar blocks are exactly integrals of the real part of one aggregate
  Hermitian symbol;
- odd radial channel has first jet

\[
\int_0^{\rho_n}4\pi r A\sinh(r/2)\,dr,
\]

  nonnegative for every `n` and strictly positive for every literal Suzuki prime-power wall.

## Route consequence

Scalar or even compression provably deletes a nonzero arithmetic orientation coordinate.  This
explains, in one invariant statement, why several corpus routes die after same-depth scalarization,
even-quadratic compression, or chirality erasure.  A viable Robin--Gamma--holonomy occurrence
theorem must retain a complex two-channel carrier, and the prime-log sewing should be
operator-valued rather than scalar.

This does not assume that such sewing is sufficient.  It supplies a falsifiable discriminator for
the next conjecture loop: seek an exact occurrence of this oriented symbol in the actual
division-free source trace and compare its two-channel Gram form with the aperture-dressed Suzuki
negative-light Gram.  If the imaginary channel disappears, that proposed occurrence map is ruled
out before any global estimate.

## Lean audit

- direct leaf check: passed;
- exact module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
