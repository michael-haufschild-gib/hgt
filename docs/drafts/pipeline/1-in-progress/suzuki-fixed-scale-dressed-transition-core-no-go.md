# Suzuki fixed-scale dressed transition-core no-go

Status: conjecture frozen; paper proof under hostile audit; Lean target not yet accepted.

## Exact RH proof chain

`SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`
→ eventually lower-semibounded rectangular Ward defect
→ `riemannHypothesis_of_suzukiRectangularWardDefect_eventually_bddBelow`
→ RH.

Corpus has isolated a positive reporter-secant transition core
`suzukiNaturalApertureTransitionCoreCauchyEnergy`.  It grows at least linearly on apertures
`8n`.  Fixed source scale `h > 0` makes complete aperture-dressed wall mass uniformly bounded,
independently of observer aperture and height.  Dressed marked halfgap and scalar holonomy Schur
budgets are fixed nonnegative scalar multiples of that same mass.

## Frozen conjecture S-WARD-BOUND-DRESSING-NOGO

For fixed positive source scale and fixed marked/Schur coordinates, allow arbitrary positive
observer aperture at every cutoff.  Even if the whole aperture-dressed light, marked halfgap, and
scalar holonomy budget is inserted with the favorable subtraction sign, the rectangular Ward
defect formed against the positive transition core tends to minus infinity on `8n`.

This kills the entire fixed-scale scalar aperture-dressed completion class as a producer of the
remaining semibounded Ward defect.  It is not a bound optimization: it separates incompatible
scaling classes (linear transition core versus uniformly bounded dressed completion, with the Xi
target at most square-root size).

## Corpus provenance and hostile checks

- `SuzukiCauchyReporterSecantTransitionCoreEscape`: transition core has a linear lower bound and
  escapes after every favorable cross-scale term is deleted.
- `SuzukiNaturalApertureWardScalingNoGo`: rectangular Xi curvature has an unconditional
  square-root envelope; raw natural Cauchy energy has wrong scaling.
- `SuzukiApertureDressedWallLightCompletion`: complete pre-split dressed wall mass is uniformly
  bounded independently of observer aperture and height.
- `SuzukiApertureDressedMarkedHalfGapUniformBound`: fixed marked halfgap budget is uniformly
  bounded.
- `SuzukiApertureDressedSchurTaxUniformBound`: fixed scalar holonomy Schur tax is uniformly
  bounded.
- `SuzukiApertureDressedSharpRecoverySchurNoGo`: coefficientwise sharp recovery already forces
  nonsummable tax; this blocks an unbounded scalar-gain evasion.
- `SuzukiWardPositiveChannelRankEscape`: fixed finite positive-channel absolute completion is
  already impossible.

Hostile sign test: subtracting the dressed budget from the transition core is the most favorable
possible sign.  If the defect still tends to minus infinity, adding any of these nonnegative debts
only worsens it.

## Literature residue (audited 2026-08-30)

Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v2, constructs finite
interval Friedrichs/self-adjoint operators but explicitly leaves the `a → ∞` strong-resolvent and
characteristic-function limits conjectural.  Its large-aperture discussion contains no
fixed-scale dressed Ward renormalizer or bounded-correction theorem.  Matsumoto--Suzuki screw
papers give RH equivalences, not this cofinal scaling obstruction.  Search of primary arXiv
records found no theorem resolving the frozen claim.

## Positive survivor if proved

Any viable Suzuki wall assembly must introduce at least one genuinely cofinal mechanism:

- signed atomic--continuous relative renormalization (the existing exact RH-equivalent survivor),
- cutoff-growing/non-scalar cross-channel transport tied to restricted-Weil response, or
- growing channel rank with a nontrivial collective cancellation.

Fixed source scale plus fixed scalar marked and Schur coordinates cannot suffice.
