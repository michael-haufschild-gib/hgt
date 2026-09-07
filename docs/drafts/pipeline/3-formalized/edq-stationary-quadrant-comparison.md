# EDQ: stationary tail quadrant and interior phase comparison

- **Stage:** 3-formalized
- **RH chain:** literal Euler deletion → retained arithmetic source → signed comparison through the strict stationary head → exclusion of every off-line zero → RH
- **RH status:** open. Tail orientation and a phase-band source sign must not be identified with a zero-location selector.

## Corpus origin and proved target SQC

`ArithmeticStationaryEndpointOrientation` gives a strictly positive anchored sine integral at zero initial phase speed. `ArithmeticStationaryFourierDilation` retains the full first-harmonic source and its complex phase. Existing stationary-phase norm estimates lose this signed information. Corpus searches for stationary splits, logarithmic cosine phases, and positive cosine integrals find no literal logarithmic-clock cosine counterpart; generic convex-cosine and repeated integration-by-parts mechanisms occur elsewhere in the corpus.

Let a,omega>0, beta>2, y=x-a, and psi(x)=omega*(x-a)-omega*a*(log x-log a). Retain the existing W=x^(1-beta)/(omega*y) and D=-W'. Define

`H=x^(1-beta)*(beta*y+a)/(omega^2*y^3) = D/psi'`,

`K=x^(-beta)*[(beta-1)*(beta*y^2+a*y)+x*(2*beta*y+3*a)]/(omega^2*y^4) = -H'`.

Lean proves the exact cosine identity and sign:

`C=integral_(a..infinity) x^(-beta)*cos(psi(x)) dx`

` = integral_(a..infinity) K(x)*(1-cos(psi(x))) dx > 0`.

Together with the already positive sine integral S, the complex tail integral of x^(-beta)*exp(-i*psi(x)) has C>0 and imaginary part -S<0.

## Dependency-closed paper proof

The reciprocal logarithmic inequality gives `0<=psi(x)<=omega*y^2/x` for x>a. Therefore `|sin psi|<=omega*y^2/x` and `1-cos psi<=omega^2*y^4/(2*x^2)`. All singular factors are compensated:

- `|W*sin psi|<=x^(-beta)*y`, which tends to zero at a and infinity;
- `|D*sin psi|<=(beta+1)*x^(-beta)`, integrable;
- `0<=H*(1-cos psi)<=(beta+1)*x^(-beta)*y/2`, with zero endpoint limits;
- `0<=K*(1-cos psi)<=(beta^2+2*beta+2)*x^(-beta)/2`, integrable.

Integration by parts first gives C=integral D*sin psi, then the displayed positive identity. K>0 on x>a, and the existing nonzero-sine witness makes its cosine defect positive on an open set. All operations concern the full actual products, not the singular factors individually.

For an interior saddle b>a, put t=omega*b and theta=-omega*(b-a)+t*log(b/a). The exact phase split is phi_a(x)=theta-psi_b(x), hence

`integral_(a..infinity) x^(-beta)*sin(phi_a(x)) dx`

` = integral_(a..b) x^(-beta)*sin(phi_a(x)) dx + sin(theta)*C_b-cos(theta)*S_b`.

On a<=x<=b, 0<=phi_a(x)<=theta. Thus when pi/2<=theta<=pi the finite head is nonnegative and the rotated tail is strictly positive. This supplies a concrete positive interior phase band for the literal source, without any zero premise. Its meaning for RH remains a separate source-comparison question; intended critical zeros also require positive interior contributions.

## Plan

- [x] Verify the compensated cosine identity and strict sign in Lean scratch.
- [x] Prove the exact stationary split and interior phase-band sign on the literal Fourier source.
- [x] Targeted leaf audit, new-only axioms, umbrella wiring without build, lint run, cleanup.
- [ ] Global lint after concurrent modules are wired; failures are recorded below.
- [ ] Supply the independent comparison excluding all off-line zeros and finish RH.

No numerical result, added axiom, or unproved sign premise is used. No novelty claim is made.


## Formal scope

`formal/GaloisForLFunctions/RHTower/ArithmeticStationaryQuadrantComparison.lean`, namespace `RHTower.DeletionMixedRefinement`: 536 lines, 37 declarations (35 theorems and two definitions).

- `endpoint_phase_le_quadratic`, `endpoint_cos_defect_le_quartic`: exact compensation orders at the stationary endpoint.
- `hasDerivAt_stationaryCosWeight`, `stationaryCosWeight_mul_phase_deriv`: the second reciprocal weight and its derivative are identified with the actual first dissipation and clock.
- `endpoint_dissipation_sine_bound`, `stationaryCos_boundary_bound`, `stationaryCos_budget_bound`: all product estimates needed for absolute integrability and endpoint limits.
- `integral_endpoint_logCos_eq_positive_budget`, `integral_endpoint_logCos_pos`: exact positive cosine identity for a,omega>0 and beta>2.
- `integral_stationary_complex_tail_quadrant`: the actual complex integral has positive real part and negative imaginary part.
- `integral_stationary_logSine_split`: exact original-source decomposition into finite head and both rotated quadrature components.
- `integral_stationary_logSine_pos_phase_band`: strict sign when the saddle phase belongs to `[pi/2,pi]`.
- `scaledBernoulliFourierAtom_neg_im_pos_of_phase_band`: the literal source consequence, for sigma>0, N>=1, integer k>0, t>2*pi*k*N, and `theta=-2*pi*k*(t/(2*pi*k)-N)+t*log((t/(2*pi*k))/N)` in that phase band. No zero premise is used.

This is an actual signed source law. It does not assert that the whole stationary sector has this sign at every parameter, provide the opposing-sector magnitude comparison, or distinguish critical from off-line zeros. Full R outside its proved strip/height range and the decisive RH comparison remain open.

## Verification

Foreground `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_stationary_quadrant.lean` passed. The final command `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryQuadrantComparison` compiled exactly this one leaf in 5.2 seconds. All dependency messages were cached replays. Umbrella is wired and was not built.

A separate `/tmp` scratch audited exactly these 37 new declarations. They use only `propext`, `Classical.choice`, and `Quot.sound`; no old declaration was included. Global `python3 scripts/formal_tools.py lint` reported two unrelated unreachable modules added concurrently: `GaloisForLFunctions.RHTower.MobiusDivisorPrimePairEnergy` and `GaloisForLFunctions.HTGeometry.AlternatingPairJetIntegral`. There was no lint error for this leaf. Those unrelated files were not edited, built, or re-audited, and unchanged lint was not repeated.

The corpus search index was refreshed once. Owned Lean handles completed and own scratch sources were removed. Logs remain at `/tmp/edq_stationary_quadrant_{build,axioms,lint,index}.log`. No numerical experiment, computational certificate, added axiom, or unproved sign input enters these results. RH remains unproved and unfalsified.
