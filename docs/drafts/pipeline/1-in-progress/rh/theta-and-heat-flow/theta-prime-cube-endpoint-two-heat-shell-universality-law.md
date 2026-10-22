# Theta prime-cube endpoint two-heat-shell universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure joined:

- `thetaPositiveFactorPairs_prime_cube`, which classifies the `p³` product fibre as four ordered
  divisor atoms `(1,p³)`, `(p,p²)`, `(p²,p)`, `(p³,1)` after undoing the zero-based indices; and
- `tendsto_thetaProductFiberCenteredCorrectedPhaseSeamCurrent_atTop_endpointGibbsSum`, which sends
  the escaping common-tail centre to a Gibbs sum over those same ordered atoms.

The existing prime-cube radial law closes logarithmic even moments into outer and inner radii.
No corpus theorem closes the fixed-point endpoint current itself into its corresponding two
Gaussian heat shells.

## Universal law

For a prime `p`, define

`H(p) =
  16 exp(-π(1+p⁶)) (2π(1+p⁶)-1)
  + 16 exp(-π(p²+p⁴)) (2π(p²+p⁴)-1)`.

Then the corrected product-fibre seam at the reflection fixed point satisfies

`thetaProductFiberCenteredCorrectedPhaseSeamCurrent (p³) c 0 → H(p)`

as `c → +∞`, and `H(p) > 0`.

Thus four ordered prime-cube divisor atoms collapse into exactly two unoriented heat shells:
the outer shell `{1,p³}` and inner shell `{p,p²}`. The collapse retains both shell scales and
forgets only their order.

## Dependency-closed paper proof

1. The prime-cube factor-pair classification gives exactly
   `(1,p³)`, `(p,p²)`, `(p²,p)`, `(p³,1)`.
2. Substitute these four atoms into the fixed-point Gibbs sum. An ordered atom `(a,b)` contributes
   `4 exp(-πa²) (8πb²-2) exp(-πb²)`.
3. Pair `(1,p³)` with `(p³,1)`. The common exponential is `exp(-π(1+p⁶))`; adding coefficients
   gives `16(2π(1+p⁶)-1)`.
4. Pair `(p,p²)` with `(p²,p)`. The common exponential is `exp(-π(p²+p⁴))`; adding coefficients
   gives `16(2π(p²+p⁴)-1)`.
5. Substitute the resulting identity into the centre-escape convergence theorem.
6. Since `p³ > 0`, the existing positive-Gibbs theorem for every positive fibre gives `H(p) > 0`.

No numerical evaluation, asymptotic approximation, or RH premise enters.

## Formal targets

- `thetaPrimeCubeEndpointTwoHeatShellCurrent`
- `thetaPrimeCube_endpointGibbsSum_eq_twoHeatShellCurrent`
- `thetaPrimeCube_endpointTwoHeatShellUniversality`

## Novelty audit

Post-proof searches found adjacent literature on theta-product reductions, theta heat equations,
and Gaussian statistics for divisor functions, but no statement identifying the four ordered
prime-cube endpoint atoms of this theta product fibre with the exact two-shell current above.

The exact centre-escape/two-heat-shell formula remains **[NOVELTY UNVERIFIED]**:

- https://doi.org/10.6028/jres.117.017
- https://dlmf.nist.gov/20.2
- https://arxiv.org/abs/1301.0214

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/RHTower/ThetaPrimeCubeEndpointTwoHeatShellUniversalityLaw.lean`

with declarations:

- `thetaPrimeCubeEndpointTwoHeatShellCurrent`
- `thetaPrimeCube_endpointGibbsSum_eq_twoHeatShellCurrent`
- `thetaPrimeCube_endpointTwoHeatShellUniversality`

Exact-file verification passed:

`lake env lean GaloisForLFunctions/RHTower/ThetaPrimeCubeEndpointTwoHeatShellUniversalityLaw.lean`

Wired into `GaloisForLFunctions/RHTower.lean` immediately after its two source-law imports.
