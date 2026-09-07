# EDQ: exact stationary endpoint now has strict source sign

Goal remains active: RH is NOT proved or falsified. Full chain: literal Euler deletion → retained arithmetic remainder or joint signature → independent source comparison through exceptional head → exclusion of every off-line zero → RH. Previous FSD turn was verified progress, not a blocker.

## New audited leaf

`formal/GaloisForLFunctions/RHTower/ArithmeticStationaryEndpointOrientation.lean`: 318 lines, 19 new theorems, no definitions, namespace `RHTower.DeletionMixedRefinement`. Imports only the already audited ArithmeticStationaryFourierDilation leaf.

At gamma=-omega*a, a>0, omega>0, beta>2, the actual anchored phase is phi(x)=omega*(x-a)-omega*a*(log x-log a). Existing reciprocalLogWeight W=x^(1-beta)/(omega*(x-a)) and reciprocalLogDissipation D=-W' are singular at a. For x>a the new source estimates are:
- 0<=phi(x)<=omega*(x-a).
- 0<=1-cos(phi)<=omega²*(x-a)²/2.
- 0<=W*(1-cos(phi))<=omega*x^(1-beta)*(x-a)/2.
- 0<=D*(1-cos(phi))<=beta*omega*x^(1-beta)/2.

The last majorant is integrable for beta>2; the boundary product tends to zero at a and at infinity (at infinity bound by omega*x^(2-beta)/2). Thus the exact integration-by-parts identity holds even at zero initial phase speed:
`integral_endpoint_logSine_eq_budget`: integral x^(-beta)*sin(phi) = integral D*(1-cos(phi)).
`integral_endpoint_logSine_pos`: this is strictly positive. Strictness uses nonzero phase motion at b=a+1, a sine-nonzero nearby point, and an open positive-measure part of the continuous positive budget. No numerical proof or source-sign hypothesis.

## Literal consequences

- `integral_anchoredLogSine_pos_of_den_nonneg`: same strict sign for beta>2 with omega*a+gamma>=0.
- `scaledBernoulliFourierAtom_neg_im_neg_of_le`: for Re(s)>0, positive N and integer k>0, Im A(s,N,-k)<0 when t<=2*pi*k*N. Equality is now proved, not an omitted stationary exception.
- `stationaryFourierBudget_eq_first_atom_at_threshold`: at t=2*pi*N the finite stationary budget is exactly Im A(s,N,-1), hence negative.
- `normalizedWeightedRemainder_im_neg_of_le_frequency`: full literal normalized remainder has Im g_s(N)<0 for 0<sigma<=1, t>=1, N>=1, t<=2*pi*N.
- `exists_positive_first_harmonic_strict_interior_at_closed_right_zero`: every zero with 1/2<=sigma<1 and t>=1 forces some positive first harmonic at N>=1 satisfying 2*pi*N<t strictly.

The remaining uncontrolled index head is now N<t/(2*pi), not N<=t/(2*pi). Do NOT remove the boundary atom from the complex FSD reconstruction: that transform still includes it and the new proof determines its negative imaginary sign. No source comparison excluding off-line zeros inside the head is supplied. Full R outside the proved strip/height domain remains open; its frozen statement is unchanged.

## Audit and cleanup

Foreground scratch passed via `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_stationary_endpoint.lean`. Final `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryEndpointOrientation` compiled exactly one leaf in 4.2s. All dependency messages were cached replays. Umbrella wired, not built. New-only axiom scratch audited exactly 19 theorems; only propext, Classical.choice, Quot.sound.

Global formal lint was run once and FAILED only on concurrently added unwired modules `GaloisForLFunctions.RHTower.DivisorHyperbolaSharpBlocks` and `GaloisForLFunctions.RHTower.HarmonicGeometricBounds`. No lint error for this leaf. Did not build/edit/re-audit those other modules or repeat unchanged lint. Search index refreshed once (32726 files,399472 declarations at refresh). Own Lean handles terminal. Own /tmp/edq_stationary_endpoint.lean and _axioms.lean removed. Logs /tmp/edq_stationary_endpoint_{build,axioms,lint,index}.log retained.

## Docs

Certificate: `docs/drafts/pipeline/3-formalized/edq-stationary-endpoint-orientation.md` (moved from 1-in-progress). Frontier EDQ paragraphs and row reflect the closed cutoff and strictly interior positive witness; no route/history changes elsewhere. STATUS high-level exceptional-head constraint updated to strict interior. R and cotangent active cards updated. Prior SFB/FSD certificates link this refinement without changing their original theorem statements or repeating their audits. New card records unresolved global lint and unresolved RH separately.

Continue with the actual source comparison inside the strict stationary head, retaining the known-negative boundary and both infinite sectors. Avoid rebuilding old saddle geometry, inverse transforms, or known nonstationary signs.