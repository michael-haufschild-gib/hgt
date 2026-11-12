# Convergent power combs exclude boundary zeros

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** A82; endpoint of the power-comb convergence interval.
- **Statement:** For `0<a<1/2`, convergence of `powerCombTail a` excludes
  every ζ zero on `Re ρ=1-a`. Thus an attained positive zero width makes
  the corresponding boundary power comb diverge. Every convergent power
  comb has its reflected zero-pairing limit, including a possible
  unattained endpoint.

## Proof

The exact comb decomposition turns convergence into an asymptotic for
summatory weighted contacts. Abel–Mellin summation then gives zero
residue at every nonreal boundary frequency. The contact Dirichlet series
has the factor `ζ(s+2a)(-ζ′/ζ(s+a)-ζ(s+a))`. At `s=ρ-a`, with
`Re ρ=1-a`, its logarithmic-derivative pole survives because
`ζ(ρ+a)` is nonzero on the line `Re=1`.

## Lean

- The exact contact asymptotic is checked in Lean:
  `powerCombTailConverges_iff_normalizedPowerContacts_converges`.
- Vanishing nonreal boundary residues: checked using
  `SelbergClass.DegreeOne.tendsto_abelIntegral_off` and the existing
  step-profile Mellin identity, including the comb-specific bridge.
- Literal Dirichlet product: checked in `PowerContactDirichletSeries`.
- Cleared analytic continuation: checked in `PowerContactMellinContinuation`.
- Final boundary-zero exclusion and its corollaries are checked in
  `ConvergentPowerCombsExcludeBoundaryZeros`: divergence at an attained
  positive width and the exact open convergence interval when attained.

Lean chain: `PowerCombConvergencePaysContactAsymptotics`,
`PowerAsymptoticsHaveNoNonrealBoundaryResidues`,
`ConvergentPowerCombsHaveNoNonrealBoundaryResidues`,
`PowerContactDirichletSeries`, `PowerContactMellinContinuation`,
`ConvergentPowerCombsExcludeBoundaryZeros`.

The convergence radius remains `1/2-zetaZeroWidth`. If the positive right
zero width is attained, the positive subcritical convergence interval is
exactly open at that radius. Ordinary convergence at an unattained
endpoint remains open.

## Real boundary coefficient

The resonant Abel theorem gives residue `(1-2a)L` for a normalized contact
limit `L`. The same contact symbol has real-boundary residue
`-ζ′/ζ(1-a)-ζ(1-a)`, since `ζ(s+2a)` has residue one.
The unconditional reference integral cancels the remaining ζ term;
the archimedean value then gives the existing reflected zero pairing.
Thus every convergent comb has the same reflected zero-pairing limit,
without a strict gap from the actual zero width.

Lean extension: `PowerAsymptoticsDetermineRealBoundaryResidues`,
`PowerContactLimitsAreForced`, and
`EveryConvergentPowerCombHasItsZeroSideLimit` are checked and wired into
their umbrellas. Final declarations:
`tendsto_powerCombTail_zeroPairing_of_converges` and
`powerCombTailConverges_iff_tendsto_zeroPairing`.
