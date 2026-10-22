# Completed prime--Gamma complex Hankel parity transfer

- **ID:** `completed-prime-gamma-complex-hankel-parity-transfer`
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE]`
- **Scientific status:** `[PROVED INTERFACE] [OPEN CORE]`

## Target

Retain the full complex Taylor coefficients of the moving completed prime--Gamma moment germ before
taking real parts.  For

\[
  \widehat c_k(\sigma)=
  \frac{G_\sigma^{(2k)}(0)}{(2k)!},
  \qquad
  \widehat\Delta_n(\sigma)=
  \det[\widehat c_{i+j}(\sigma)]_{0\le i,j<n},
\]

the first formal target is

\[
  \widehat\Delta_n(1-\sigma)=\widehat\Delta_n(\sigma),
  \qquad
  \widehat\Delta_n(1/2)=
  \bigl(\det(\texttt{primeArchSourceMomentHankelMatrix }n):\mathbb C\bigr).
\]

On the zero-free domain of `xi`, the coefficient should also equal the explicit completed-source
jet

\[
  \widehat c_k(\sigma)=
  \frac{(-1)^k}{(2k+1)!}
  \left(\frac{\xi'}{\xi}\right)^{(2k+1)}(\sigma).
\]

This formula makes `widehatDelta_n` holomorphic on every zero-free component and Schwarz-real on
the real axis.

## Top-down simplification

The existing far-right route asks that every real determinant stay nonzero between its positive
far-right anchor and the center.  That is stronger than necessary.  A real analytic function can
cross from positive to negative only through a zero of odd order.  The intended chain is therefore

```text
far-right positivity of widehatDelta_n                                  [PAPER]
  + every real zero of widehatDelta_n on [1/2,R_n] has even order       [OPEN CORE]
  + widehatDelta_n(1/2) != 0                                            [OPEN CORE]
  -> widehatDelta_n(1/2) > 0 for every n
  -> positivity of every central prime--Gamma Hankel determinant        [Lean]
  -> RH.                                                                 [Lean]
```

The exact reflection makes a zero at the fixed point `1/2` even automatically once the complex
determinant is proved holomorphic there.  This fixed-point parity is now formalized.  Thus the
source problem is reduced from zero exclusion to noncentral odd-order exclusion plus central
nonvanishing.

The later polynomial-test refinement in
`completed-prime-gamma-polynomial-even-factorization-to-rh.md` is sharper as an RH route.  It
transports the countable quadratic tests rather than strict leading determinants.  Its even-factor
sign theorem permits a zero at `1/2`, so the separate central-nonvanishing input disappears.  The
determinant route remains a valid stronger alternative, but it is no longer the minimal consumer.

## Gates

- [x] define the complex moving moments, matrices, and determinants
- [x] prove exact reflection
- [x] prove the central complex-to-real determinant identity
- [x] prove the explicit logarithmic-derivative jet formula at the center
- [x] prove holomorphy of the explicit logarithmic-derivative determinant off the Xi divisor
- [x] prove its Schwarz reality on the real axis
- [x] prove even analytic order at the reflection center whenever the germ has finite order
- [x] formalize finite even-factor sign transport on a real compact interval
- [ ] produce a source-side exclusion of noncentral odd-order determinant zeros
