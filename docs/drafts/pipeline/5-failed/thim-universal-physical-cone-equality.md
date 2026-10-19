# Universal finite-horizon equality of physical cone constants

- **ID:** thim-universal-physical-cone-equality
- **Stage:** 5-failed
- **Type:** REFUTED (Lean)
- **Source:** [Finite-horizon cone gap and centering](../3-formalized/thim-finite-horizon-positive-cone-gap.md)
- **Failed statement:** `K_N = K_N^+` for every `N >= 2`, where these are the
  literal signed and nonnegative optimal constants for the original physical
  pronic energies.

## Refutation

`fermiPhysicalInverseConstant_three_strict_cone_gap` proves `K_3^+ < K_3`.
The proof uses the actual horizon-three Gram forms, exact rational pronic
comparisons, attainment of the nonnegative maximum with both remaining
coefficients positive, and a strictly improving signed centering shift.
It uses no numerical calculation or unproved analytic estimate.

## Strongest positive survivor

For `N >= 2`, shifting the original coefficients by `t*(e_2-e_1)` changes
both physical energies by the same quadratic `-2*t*A+t^2*T`, with `T>0`
and `A` the original weighted odd trace. Thus `P-Q` is invariant. Whenever
`P>Q`, the ratio is uniquely maximized along this orbit at `t=A/T`; the exact
gain is `(P-Q)*A^2/(T*Q*(Q-A^2/T))`. A nonnegative signed extremizer with
ratio above one must have zero coefficients at every admitted odd divisor.
The nonnegative horizon-three optimum is attained with positive coefficients
at both 2 and 3, exposing the strict separation from the signed optimum.

- **Paper status:** dependency-closed proof on the linked formalized card.
- **Lean status:** exact centering, gain, support restriction, interior
  maximizer, and strict gap are proved in
  `FermiOddTraceCenteringAndExtremalRestriction.lean` and
  `FermiFiniteHorizonPositiveConeGap.lean`, with the two intervening pronic/Gram
  leaves listed on that card.
- **Certificate:** four named source/olean checks, all 48 public axiom audits
  using only standard Lean axioms, imports, index, and generated-file lint
  passed on 2026-10-19.
- **Counting:** supporting extension of C1; no additional qualified count.

The shared `4/pi^2` leading asymptotic survives. Equality at a finite horizon
does not follow from that asymptotic; the new exact invariant explains how
signed coefficients improve the finite-horizon optimum.
