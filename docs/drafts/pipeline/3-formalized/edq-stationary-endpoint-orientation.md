# EDQ: signed orientation at the stationary endpoint

- **Stage:** 3-formalized
- **RH chain:** literal Euler deletion → retained arithmetic first-harmonic profile → source comparison through the exceptional head → exclusion of every off-line zero → RH
- **RH status:** open. This target resolves the exact stationary boundary, not the interior head.

## Corpus evidence and proved target SEO

`ArithmeticUnitFourierOrientation` proves strict positivity of the anchored sine integral when `omega*a+gamma>0`. That theorem covers the Bernoulli negative-frequency sign for `t<2*pi*k*N`; the endpoint is handled here. `ArithmeticStationaryFourierDilation` reconstructs the retained finite first-harmonic profile exactly. General weighted stationary-phase norm estimates are available in `VanDerCorputWeightedSecondGeneral`, but do not retain the signed source needed here.

Consider the endpoint case `gamma=-omega*a`, with `a>0`, `omega>0`, and `beta>2`. Put

`phi(x)=omega*(x-a)-omega*a*log(x/a)`,

`W(x)=x^(1-beta)/(omega*(x-a))`,

`D(x)=x^(-beta)*[(beta-1)*omega*(x-a)+omega*x]/[omega*(x-a)]^2`.

Lean proves the exact positive identity

`integral_(a..infinity) x^(-beta)*sin(phi(x)) dx`

` = integral_(a..infinity) D(x)*(1-cos(phi(x))) dx > 0`.

## Dependency-closed paper proof

For x>a, logarithmic concavity gives `0<=phi(x)<=omega*(x-a)`. Therefore `0<=1-cos(phi(x))<=(omega*(x-a))^2/2`. The derivative of W is -D, and D is strictly positive. The singular factor is compensated in both products:

- `0<=W(x)*(1-cos(phi(x)))<=omega*x^(1-beta)*(x-a)/2`;
- `0<=D(x)*(1-cos(phi(x)))<=beta*omega*x^(1-beta)/2`.

The first bound tends to zero at a and is bounded by `omega*x^(2-beta)/2` at infinity, also tending to zero. The second is integrable because beta>2. Integration by parts on the open half-line now has zero boundary terms and gives the exact identity. Strict positivity follows because the clock derivative is positive at every x>a, hence its sine cannot vanish on the whole open interval; continuity supplies a positive-measure positive part of the integrand.

For the actual source beta=sigma+2, every sigma>0 satisfies this domain. The literal negative-frequency atom is therefore strictly negative also at `t=2*pi*k*N`. Combining with the already audited finite stationary budget proves the normalized-remainder sign for `t<=2*pi*N`, `0<sigma<=1`, and `t>=1`. Any positive first-harmonic witness forced by a closed-right strip zero in that height range lies strictly inside `2*pi*N<t`. The complete complex stationary transform retains its boundary atom; the new theorem determines that atom's negative imaginary sign rather than removing it from the transform.

## Plan and scope

- [x] Check endpoint inequalities and exact integrable positive identity in Lean scratch.
- [x] Derive the actual Fourier endpoint sign and sharpen the source cutoff/witness.
- [x] Targeted leaf build, new-only axiom audit, umbrella wiring without build, lint run, cleanup.
- [ ] Global lint after concurrently added modules are wired; current failures are recorded below.
- [ ] Supply the independent interior-head comparison and finish RH.

No numerical result, new axiom, or assumed source sign is used. The argument uses existing corpus integration-by-parts and sine-positivity mechanisms; no novelty claim is made.


## Formal scope

`formal/GaloisForLFunctions/RHTower/ArithmeticStationaryEndpointOrientation.lean`, namespace `RHTower.DeletionMixedRefinement`: 318 lines, 19 theorems, no new definitions.

- `endpoint_boundary_bounds`, `endpoint_budget_bounds`: explicit bounds for the actual compensated products.
- `integrable_endpoint_budget`, `tendsto_endpoint_boundary_at_anchor`, `tendsto_endpoint_boundary_atTop`: all integrability and endpoint obligations, without extending the singular weight as a continuous factor.
- `integral_endpoint_logSine_eq_budget`, `integral_endpoint_logSine_pos`: the exact identity and strict positive orientation for a,omega>0 and beta>2.
- `scaledBernoulliFourierAtom_neg_im_neg_of_le`: the actual negative-frequency atom is strictly negative when `t<=2*pi*k*N`, for sigma>0, N>=1, and integer k>0.
- `normalizedWeightedRemainder_im_neg_of_le_frequency`: the normalized remainder is strictly negative for `0<sigma<=1`, `t>=1`, and `t<=2*pi*N`.
- `exists_positive_first_harmonic_strict_interior_at_closed_right_zero`: every zero with `1/2<=sigma<1` and `t>=1` has some positive first-harmonic value at a positive integer N satisfying `2*pi*N<t`.

The last conclusion is a necessary zero condition and includes critical zeros. It supplies no bound excluding off-line zeros in the remaining interior head.

## Verification

Foreground `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_stationary_endpoint.lean` passed. The final audit used `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryEndpointOrientation`; exactly this one leaf compiled, in 4.2 seconds. Dependency messages were cached replays. The umbrella import is wired and no umbrella was built.

A separate `/tmp` scratch audited exactly these 19 new theorems. All use only `propext`, `Classical.choice`, and `Quot.sound`; no previous declaration was included. Global `python3 scripts/formal_tools.py lint` reported two unrelated unreachable modules added concurrently: `GaloisForLFunctions.RHTower.DivisorHyperbolaSharpBlocks` and `GaloisForLFunctions.RHTower.HarmonicGeometricBounds`. It reported no error for this leaf. The unrelated modules were not built, edited, or re-audited.

The corpus search index was refreshed once. Owned Lean handles completed and own scratch sources were removed. Build, axiom, lint, and index logs remain at `/tmp/edq_stationary_endpoint_*.log`. RH remains unproved and unfalsified.

The [stationary-quadrant comparison](edq-stationary-quadrant-comparison.md) supplies the strictly positive cosine companion, the exact phase rotation at an interior saddle, and a positive phase band for literal negative-frequency atoms. Its full split retains both quadrature components and the pre-saddle head; it does not close the RH comparison.
