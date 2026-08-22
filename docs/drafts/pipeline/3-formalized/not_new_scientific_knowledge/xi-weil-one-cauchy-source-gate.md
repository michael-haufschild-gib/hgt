# Xi Weil one-Cauchy source gate

- **ID:** `xi-weil-one-cauchy-source-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** RH is equivalent both to upper-half-strip positivity of every single regular Xi
  Cauchy diagonal and to nonnegativity of the corresponding continued prime--archimedean source
  divided difference.

## Goal

Work backward from the regular two-pole Cauchy criterion and determine the smallest source-visible
packet family that still forces RH. The answer is rank one: no off-diagonal minor, full Cauchy-core
density, or confluent real diagonal is required.

## Theorem

Write

\[
T(z)=\texttt{continuedPrimeArchSourceRelativeTrace}(z).
\]

On the centered upper half-strip `0 < Im z < 1/2`, away from the zeta poles of the source,
critical-line conjugation gives

\[
T(\bar z)=\overline{T(z)}.
\]

Consequently the one-Cauchy divided-difference diagonal is

\[
\operatorname{Re}
\frac{T(\bar z)-T(z)}{z-\bar z}
=-rac{\operatorname{Im}T(z)}{\operatorname{Im}z}.
\]

Since `Im z > 0`, nonnegativity of this scalar is exactly the continued-source anti-Herglotz sign.
The already formalized local-pole argument converts that sign into RH. Conversely, RH makes every
square-summable Weil diagonal nonnegative. Therefore

\[
\mathrm{RH}
\iff
\forall z,\quad
\operatorname{Re}\langle k_z,k_z\rangle_{\Xi,\mathrm{Weil}}\ge0
\]

for regular `z` in the centered upper half-strip, and equivalently

\[
\mathrm{RH}
\iff
\forall z,\quad
\operatorname{Re}
\frac{T(\bar z)-T(z)}{z-\bar z}\ge0.
\]

The second formulation contains only values of the fixed continued prime--Gamma source and its
explicit pole-free domain conditions; it contains no Xi-zero enumeration or spectral test family.

## Positive carrier law

A successful source construction need only establish rank-one upper-half-strip passivity. The
moving two-pole family remains useful for approximating the explicit off-real sign vector, but its
off-diagonal positivity is stronger than necessary for proving RH.

The remaining positive theorem is therefore the scalar source inequality

\[
\operatorname{Im}T(z)\le0,
\qquad 0<\operatorname{Im}z<\frac12,
\]

equivalently left-half-strip accretivity of the completed prime--Gamma flux. Any prime, theta,
Sonin, or determinant mechanism that supplies this scalar sign closes RH immediately.

The finite Euler connection is now audited exactly in
`../../2-fully-proven/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/finite-euler-connection-cauchy-phase-chambers.md`.
Its one-prime diagonal is a difference of two positive disk Poisson kernels and has an explicit
positive/negative phase threshold; every finite nonempty prime packet visits both chambers.
Consequently a semilocal proof of this gate cannot stop at positivity of individual Euler or
all-pass factors.  It must prove phase-locked domination by the completed prime--Gamma remainder.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/XiWeilOneCauchyGate.lean`

Main declarations:

- `xiRelativeResolventTrace_conj`
- `continuedPrimeArchSourceRelativeTrace_conj_of_domain`
- `continuedPrimeArchSourceRelativeTrace_conj_of_upperHalfStrip`
- `ContinuedPrimeArchUpperCauchyDiagonalNonnegative`
- `continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz`
- `XiWeilUpperOneCauchyNonnegative`
- `xiWeilUpperOneCauchyNonnegative_iff_riemannHypothesis`
- `continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis`

Verification:

- `lake build GaloisForLFunctions.RHTower.XiWeilOneCauchyGate` passes.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1 in-progress: rank-one diagonal isolated from the rank-two criterion
- [x] 1 → 2 fully-proven: conjugation and scalar divided-difference identity proved
- [x] 2 → 3 formalized: exact source and target equivalences proved in Lean
- [ ] 3 → 4 publication-ready: integrate with a proof of the scalar prime--Gamma sign
