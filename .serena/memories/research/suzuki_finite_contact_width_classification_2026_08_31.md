# Suzuki finite-contact width classification — 2026-08-31

Qualifying result: killed every fixed nonlinear Suzuki transition-core contact order m≥2 as an endpoint-preserving repair through transition-core growth plus CCM-abscissa continuation.

Formal module:
- formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean
- wired into formal/GaloisForLFunctions/RHTower.lean

Definitions:
- P_m(N)=E_N^m/C_N^(m-1), totalized at C_N=0.
- alpha_m=(m-1)/(2m).

Main chain:
P_m eventually bounded -> |G_N|=O(exp(alpha_m log N)) -> Q(log N) same rate -> global Q(t)=O(exp(alpha_m t)) -> XiZeroHalfPlaneBound alpha_m.

Main capstones:
- suzukiTransitionCore_finiteContact_widthClassification
- suzukiFiniteContact_algebraicEndpointNoGo
- xiZeroHalfPlaneBound_suzukiFiniteContactWidth_of_finiteContactResidualEventuallyBounded

Sharpness/no-go:
For any m≥2 and proposed uniform K, R=K+1, C=R^(2m), E=R^(2(m-1)), G=R^(m-1) gives C>0, E≥0, G^2=E, E^m/C^(m-1)=1, but G>K. Thus finite-contact algebraic inequalities alone cannot generate endpoint-uniform Green control. Any survivor needs a new cancellation invariant before CCM continuation.

Order one:
SuzukiTransitionCoreFiniteContactResidualEventuallyBounded 1 is proved equivalent to existing aligned-energy eventual boundedness, hence RH. m=2 definitionally recovers quadratic residual and alpha_2=1/4.

Audit:
- lake env lean final module: passed.
- targeted lake build: 13735/13735.
- capstone axioms: only propext, Classical.choice, Quot.sound.
- formal lint: no issue in this module; only unrelated unwired concurrent modules failed reachability.
- no computations used.
- frontier map not edited by this work.

Cards:
- docs/drafts/pipeline/3-formalized/suzuki-finite-contact-width-classification.md
- docs/drafts/pipeline/5-failed/suzuki-higher-finite-contact-endpoint-preservation.md
