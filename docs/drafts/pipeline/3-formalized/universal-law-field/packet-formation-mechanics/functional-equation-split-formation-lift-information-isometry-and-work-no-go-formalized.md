# Functional-equation split-formation lift — Lean formalization certificate

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveFunctionalEquationPacketLift.lean`
- **Stage:** 3-formalized
- **Date:** 2026-08-11

## Certified declarations

1. `splitFormation` defines common-kernel observer/history formation as `μ ⊗ₘ κ`.
2. `splitFormation_recovers_observer` proves exact recovery by first projection.
3. `klDiv_splitFormation` proves unconditional extended-KL equality for finite measures and a
   common Markov kernel, including infinite divergence values.
4. `formationLiftKernel` constructs the stochastic action: recover observer, apply measurable
   action, discard old history, regenerate from common kernel.
5. `formationLiftKernel_naturality` proves the lifted action sends `E_K(μ)` to `E_K(A_*μ)`.
6. `formationLiftKernel_comp_on_formation` proves strict action composition on formed laws.
7. `formationLiftKernel_involution_on_formation` proves an involutive observer action remains an
   involution on the image of formation.
8. `formationLiftKernel_klDiv_isometry` proves information neutrality for every measurable
   embedding.
9. `formationJeffreys_splitFormation` and `formationJeffreys_lift_isometry` prove exact symmetric
   information-work conservation.
10. `involutiveFormationLift_informationNeutral` packages KL isometry, Jeffreys isometry, and
    involution into the functional-equation capstone with no embedding hypothesis supplied by the
    caller.
11. `reflectionSheetWeight_swap` proves reflection negates the tilt and toggles the formation
    sheet.
12. `reflectionSheetWeight_sameSheet_zero_iff` proves same-sheet closure at zero tilt exactly when
    the base weight is reflection invariant.

## Exact scope

Lean certifies the route-independent formation mechanism requested by the card. It does not encode
an RH hypothesis, zero, or route-specific endpoint. It proves that information neutrality is an
isometry law and therefore preserves Jeffreys separation rather than annihilating it.

Existing corpus modules already certify positivity/evenness and Fourier--Laplace identities of the
theta source and the common Hasse geometric recovery mass function. This module does not rebuild
their analytic measure instances. The paper card's Hellinger midpoint/Radon--Nikodym construction,
literal theta normalization, and strict-convex reflected-work formula remain outside this module's
declared formal scope.

## Audit

- Direct module check: `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFunctionalEquationPacketLift.lean`
- Final module build: `lake build GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift`
- Umbrella import: `GaloisForLFunctions.HTGeometry.UniversalLawField`
- Formal lint and axiom audit: passed at certificate creation.
