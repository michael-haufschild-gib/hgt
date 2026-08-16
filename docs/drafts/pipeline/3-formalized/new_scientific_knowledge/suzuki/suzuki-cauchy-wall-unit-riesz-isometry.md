# Suzuki Cauchy-wall / unit-Riesz isometry

## Status

Formalized in Lean 4.  Route map remains read-only.  This closes the missing *compensation-object
identification* inside `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`; it does not close the remaining
cofinal estimate.

## Corpus-first frontier audit

Exact searches with `scripts/formal_tools.py research` covered Suzuki wall fields, reflected-wall
Gram completion, Cauchy-height Fourier kernels, unit-Riesz coherent increments, completed
prime/polar barycenters, and rational counterterms.  Closest prior modules were:

- `SuzukiWallFieldLightConeKernelCompletion`: finite light Gram with diagonal
  `ArithmeticFunction.vonMangoldt n / Real.sqrt n`, but no polar recentering or Cauchy-height
  realization;
- `CCMUnitRieszCompletedCoherentBarycenter`: completed prime-minus-polar barycenter and exact
  bulk/boundary energy, but no Suzuki wall-field identification;
- `SuzukiCoherentCausalDepthFusion`: an extra-damped summable carrier, not the raw completed
  prime/polar wall geometry.

No internal theorem identified normalized literal Suzuki wall phases with the unit-Riesz coherent
frame or evaluated the polar continuum in that same height carrier.

## Theorem

For logarithmic coordinate `x`, define the normalized wall phase

\[
  \chi_x(t)=\exp(ixt/2).
\]

With Cauchy probability measure `dt / (pi * (1+t^2))`, its Gram kernel is

\[
  \langle \chi_x,\chi_y\rangle_C=e^{-|x-y|/2}.
\]

Consequently, anchoring at `a` gives exactly the CCM unit-exponential coherent-increment Gram:

\[
  \langle\chi_x-\chi_a,\chi_y-\chi_a\rangle_C
  =\langle u_x-u_a,u_y-u_a\rangle,
  \qquad u_x(s)=1_{s>x}e^{-(s-x)/2}.
\]

The full positive polar continuum in the same carrier has the closed form

\[
  \int_0^\infty e^{-p}(1-\chi_{-p}(t))\,dp
  ={it/2\over 1+it/2}.
\]

Thus the finite completed source symbol

\[
  \sum_{2\le k\le N}{\Lambda(k)\over\sqrt N}
    \left(1-\chi_{-(\log N-\log k)}(t)\right)
  -\sqrt N\,{it/2\over1+it/2}
\]

vanishes at `t=0` before any scalar trace or cofinal limit.  The literal prime-power Suzuki wall
phase is also proved equal to its wall field divided by the strictly positive bare amplitude.

## Novelty audit

The Fourier transform of the Cauchy density is classical and is not claimed as new.  New content
is the exact source-specific weld: literal Suzuki wall phases, CCM unit-Riesz coherent increments,
and the completed polar continuum occupy one common spectral carrier with an explicit rational
counterterm.  This replaces the previously nonsummable raw wall diagonal by a completed,
zero-height-recentered object without deleting Gamma/polar data.

## Hostile audit

- No cofinal boundedness, sign, Ward domination, or RH conclusion is claimed.
- Zero-height cancellation alone gives no control away from zero height.
- Result identifies correct compensation geometry; it does not prove compensation is quantitatively
  sufficient against all-prime light mass.
- No prime number theorem, zero-free region, or unproved source estimate is assumed.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.SuzukiCauchyWallUnitRieszIsometry`
- **Wall/coherent capstone:**
  `suzukiCauchyAnchoredWallGram_eq_unitExponentialCoherentIncrementGram`
- **Polar capstone:** `integral_suzukiCauchyWallPolarCounterterm`
- **Completed source zero mode:** `suzukiUnitRieszCompletedCauchyWallSymbol_zero`
- **Literal wall normalization:**
  `suzukiCauchyWallPhase_log_primePower_eq_normalizedWall`

## Log

- 2026-08-16 — exact corpus-first collision search completed.
- 2026-08-16 — paper theorem and unconditional Lean proof completed; umbrella wired.
