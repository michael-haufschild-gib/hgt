# Suzuki marked-secant midpoint Lorentz completion — formalization certificate

## Status

`[FORMALIZED] [UNCONDITIONAL] [SOURCE-PURE] [NO RH PREMISE]`

## Paper source

`./suzuki-marked-secant-midpoint-lorentz-completion.md`

## Lean source

`formal/GaloisForLFunctions/RHTower/SuzukiMarkedSecantMidpointLorentzCompletion.lean`

## Formal theorem surface

- `suzukiProjectiveAffineSecantTensor_midpoint_halfGap`: exact marked numerator
  `Q=U*V-d^2*x*y+m*F`.
- `suzukiProjectiveAffineSecantDenominator_midpoint_halfGap`: exact denominator
  `P=V^2-d^2*y^2`.
- `suzukiProjectiveAffineSecantTensor_eq_symmetric_add_alternating`: complete symmetric/Pluecker
  split retaining affine mark.
- `suzukiMarkedSecantSymmetricForm_self_eq`: Lorentz diagonal
  `(r-m*s)^2-d^2*s^2`.
- `suzukiMarkedSecant_rootedCompletion_nonneg_iff`: sharp all-coordinate completion iff
  `d^2<=kappa`.
- `suzukiMarkedSecant_minimalRootedCompletion_eq_square`: critical completion is one square.
- `suzukiMarkedSecantSymmetricForm_has_positive_and_negative_directions`: explicit `(1,1)` inertia
  witnesses for distinct shifts.
- `suzukiMarkedSecant_dyadic_rootedCompletion_nonneg_iff`: Suzuki pair `(-2L,-L)` has exact debt
  `L^2/4`.
- `suzukiGlobalLocalCompoundNumerator_marked_midpoint_halfGap`: canonical full-jump numerator
  splits into midpoint determinant, rooted debt, and centered Pluecker flux.
- `suzukiMarkedSecantMidpoint_affineGauge_shear` and
  `suzukiMarkedSecantMidpoint_flux_affineGauge_invariant`: affine gauge is midpoint shear while
  flux stays fixed.
- `suzukiTwoResolvent_midpoint_forcing`: physical product resolvent satisfies centered
  second-order equation with exact `d^2` source term.
- `suzukiRelativeVolterraPhaseObservation_midpoint_forcing` and
  `suzukiTwoResolvent_relativeVolterraPhase_midpoint_debt`: same debt appears literally as
  `-d^2*phaseNeumann(v)` in actual relative causal phase.
- `suzukiMarkedXiCompoundNumerator_midpoint_halfGap` and denominator companion: direct connector
  to canonical marked Xi compound target.

## Scientific advance

Prior frontier asked for unspecified positive Gram factorization of signed compound Bezoutian.
Formal theorem fixes local inertia, exact completion amount, and physical source coordinate:

```text
amount = (beta-alpha)^2/4,
source = midpoint product-resolvent Neumann phase,
flux   = centered Pluecker channel,
dyadic amount = L^2/4.
```

This kills direct balanced-boundary producer because corpus proves all supported two-boundary
balanced Grams vanish on `(+1/2,-1/2)` while marked rank-one affine intercept survives.  Correct
source architecture must retain raw rooted Gamma--Bianchi coordinate before compression.

## Remaining open core

`SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM`: from explicit prime--Gamma source and pointed Ward identity,
prove signed global Xi term supplies exact halfgap-squared rooted Bianchi Gram plus positive
archimedean remainder, with already forced common-prime Julia/Bianchi mixed block.  This factors
canonical compound Bezoutian, giving jump Pick positivity and RH through existing connector.

RH is not claimed proved.

## Verification

- Direct Lean check: passed with
  `lake env lean GaloisForLFunctions/RHTower/SuzukiMarkedSecantMidpointLorentzCompletion.lean`.
- Final targeted SOTA build: passed with
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` (9193 jobs).
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or RH premise.
- Forbidden-token scan: clean.
- Repository lint reaches this module but remains red on four unrelated concurrent unreachable
  modules: `MobiusAdditiveTriangleSourceUniversalityLaw`,
  `MobiusLaplaceAdditiveTrianglePolylog`, `MobiusLaplacePolylogSharpCoefficientLaw`, and
  `SuzukiGlobalLocalScalarPickUniversalityLaw`.
