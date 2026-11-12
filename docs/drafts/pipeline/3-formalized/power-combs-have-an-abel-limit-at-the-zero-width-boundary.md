# Power combs have an Abel limit at the zero-width boundary

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** A82; retain a canonical literal-comb limit at an attained boundary.
- **Statement:** For `0<a<1/2`,
  `LogarithmicAbelIntegrable (powerCombTail a) ↔ a+zetaZeroWidth≤1/2`.
  Under these equivalent conditions,
  `ε ∫₀∞ exp(-εu) powerCombTail a ⌊exp u⌋ du → powerTailZeroPairing a`
  as `ε↓0`, with the real integrand embedded in ℂ.

The criterion requires absolute integrability at every positive damping.
It includes boundary zeros, which obstruct ordinary convergence. Thus
Abel averaging retains the canonical zero pairing throughout the closed
zero-width range. Ordinary convergence at an unattained endpoint remains
unproved.

The [critical endpoint](critical-power-comb-abel-integrability-detects-rh.md)
is also formalized: at `a=1/2`, the same absolute-integrability condition
is equivalent to RH, and the mean tends to the finite part `E−2B′(0)`.

## Proof

The actual zero width supplies arbitrarily small positive growth bounds
for the normalized contacts. Their literal Mellin transform is holomorphic
on `Re s>1−2a`; the entire zeta residue unit continues the actual Dirichlet
symbol there. At the real boundary its residue is
`−ζ′/ζ(1−a)−ζ(1−a)`. The logarithmic staircase identity and the bounded,
vanishing floor-normalization error turn this residue into the discrete
contact Abel mean. The convergent elementary comb terms reconstruct the
reflected zero pairing.

Conversely, absolute comb integrability transfers to the contacts.
Continuous power normalization decreases the absolute integrand, and a
weaker damping absorbs the time factor in its derivative. This gives
holomorphy throughout `Re s>1−2a` without a pointwise growth assumption.
Any zero with `Reρ>1−a` produces the nonzero residue `−mζ(ρ+a)` inside
that half-plane: `Re(ρ+a)>1` prevents multiplier cancellation. Hence
no such zero exists, giving the exact width bound.

## Lean

- `PowerCombAbelIntegrabilityDetectsTheZeroWidth`:
  `logarithmicAbelIntegrable_powerCombTail_iff` and
  `tendsto_logarithmicAbelMean_powerCombTail_of_abelIntegrable`.
- `PowerCombsHaveTheirAbelLimitAtTheBoundary`: sufficient direction and
  the actual discrete Abel limit.
- `PowerContactAbelIntegrability`, `HolomorphicContactSymbolsExcludeInteriorZeros`:
  literal contact holomorphy and the interior-pole obstruction.

All supporting modules have their required oleans. Final single-file
`lake --old env lean` check passed; AGZ umbrella wired.
