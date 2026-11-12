# Power combs have an Abel limit at the zero-width boundary

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A82; retain a canonical literal-comb limit when boundary zeros prevent ordinary convergence.
- **Statement:** For `0<a<1/2`, absolute integrability of the logarithmic
  Abel integrand for every `ε>0` is equivalent to `a+zetaZeroWidth≤1/2`.
  Whenever these equivalent conditions hold, the mean
  `ε ∫₀∞ exp(-εu) powerCombTail a ⌊exp u⌋ du` tends to
  `(powerTailZeroPairing a).re` as `ε↓0`.

## Connection

`PowerTailCombGrowth` supplies arbitrarily small positive growth exponents
at the closed width boundary. The exact comb decomposition transfers this
to the contact prefix. Its Mellin transform is therefore holomorphic on
`Re s>1-2a`, even without an exact boundary power bound.

Continue the actual contact symbol using the entire zeta residue unit.
At the real boundary its residue is
`-ζ′/ζ(1-a)-ζ(1-a)`. The Laplace identity for the logarithmic staircase
turns this residue into the Abel mean of the normalized contacts. The
already convergent archimedean, reference, and remainder terms then give
the reflected zero pairing.

## Lean chain — written, unverified

- `StrictPowerGrowthHasAnOpenMellinHalfPlane`, `ContactSymbolsContinueAcrossZeros`,
  `PowerContactSymbolAtTheClosedWidth`: strict contact growth and continuation.
- `PowerContactRealBoundaryResidue`, `PowerContactAbelMean`: actual real
  residue and continuously normalized Abel mean.
- `LogarithmicPowerNormalization`: the floor estimate makes the change
  of normalization bounded and vanishing.
- `LogarithmicAbelMeans`: integrability under subpolynomial growth,
  preservation of ordinary limits, and finite linear identities.
- `PowerContactDiscreteAbelMean`: the literal integer-normalized contact mean.
- `PowerCombsHaveTheirAbelLimitAtTheBoundary`: integrability of the literal
  comb and its Abel limit `powerTailZeroPairing a` in complex notation.

The complete chain is written; verification pending. No new contribution counted.

## Converse — written, unverified

The exact comb identity transfers absolute integrability to the normalized
contacts. Since `1-2a>0`, continuous normalization decreases their absolute
integrand. A weaker positive damping absorbs the logarithmic-time factor
in the derivative, giving holomorphy throughout `Re s>1-2a`.
The unconditional outer zero bound supplies a coarse linear contact bound
for the initial Dirichlet identity. Any zero with `Re ρ>1-a` then forces
the nonzero interior residue `-mζ(ρ+a)`, contradicting holomorphy.

Unverified Lean chain: `IntegrableLogarithmicStaircasesHaveHolomorphicMellinTransforms`,
`LogarithmicAbelIntegrability`, `PowerContactAbelIntegrability`, and
`HolomorphicContactSymbolsExcludeInteriorZeros`, followed by
`PowerCombAbelIntegrabilityDetectsTheZeroWidth`. The last states the exact
equivalence and the forced Abel limit. No new contribution counted.

This does not establish ordinary convergence at an unattained endpoint.
A direct dominated-convergence argument there would need a uniform
summable spectral tail for the discrete contact prefix; none has been supplied.
