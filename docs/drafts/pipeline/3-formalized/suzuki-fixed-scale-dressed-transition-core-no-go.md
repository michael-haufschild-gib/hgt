# Suzuki fixed-scale dressed transition-core no-go

Status: fully formalized route kill; paper proof, hostile sign audit, targeted build, and axiom audit passed 2026-08-30.

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

## Closed proof

Let `c N` be any correction uniformly bounded above by `B`.  Corpus theorem
`suzukiNaturalApertureCauchyEnergy_le_transitionCore` gives

`target(8N) - (transitionCore(8N) - c N) ≤ target(8N) - naturalCauchyEnergy(8N) + B`.

The right side tends to `-∞` by
`tendsto_suzukiRectangularWardDefect_naturalCauchyEnergy_eight_mul_atBot`; hence so does the corrected
transition-core defect.  The complete fixed-scale dressed budget is uniformly bounded above by
the sum of the already formalized wall-light, marked-halfgap, and scalar-holonomy Schur ceilings.
Instantiating `c` with that budget proves the frozen conjecture, and the `-∞` limit contradicts
every eventual lower bound.

## Lean certificate

Module:
`GaloisForLFunctions.RHTower.SuzukiFixedScaleDressedTransitionCoreNoGo`.

- `suzukiFixedScaleDressedWardBudget_le`: aperture-independent ceiling for the complete fixed-scale
  scalar dressing.
- `tendsto_suzukiRectangularWardDefect_transitionCore_sub_bounded_atBot`: abstract bounded-correction
  no-go.
- `tendsto_suzukiRectangularWardDefect_transitionCore_sub_fixedScaleDressed_atBot`: concrete dressed
  defect tends to `-∞` for every positive moving aperture sequence.
- `not_exists_eventually_bddBelow_suzukiRectangularWardDefect_transitionCore_sub_fixedScaleDressed`:
  no eventual Ward lower bound survives.
- `no_fixedScaleDressed_transitionCore_WardProducer`: closed, parameter-free class kill.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.SuzukiFixedScaleDressedTransitionCoreNoGo` passed; all five
certificates depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Module is wired into
`GaloisForLFunctions.RHTower`.  Global lint recognizes it as reachable; global lint remains red
only because unrelated concurrently present modules are not wired into their umbrellas.

## Positive survivor

Any viable Suzuki wall assembly must introduce at least one genuinely cofinal mechanism:

- signed atomic--continuous relative renormalization (the existing exact RH-equivalent survivor),
- cutoff-growing/non-scalar cross-channel transport tied to restricted-Weil response, or
- growing channel rank with a nontrivial collective cancellation.

Fixed source scale plus fixed scalar marked and Schur coordinates cannot suffice.
