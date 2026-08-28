# PW-B endpoint winding defeats infinite dark kernel

- **ID:** HC31
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / POSITIVE SURVIVOR
- **Route:** PW-B
- **Date:** 2026-08-28
- **Statement:** Literal finite-energy endpoint winding has strictly positive response and rank-one energy on corpus's explicit infinite-support PW-dark kernel at every positive backreaction scale.

## Goal

Close concrete infinite-support counterexample left by countable three-moment recoil reporters. Use
exact geometric-tail dark vector already constructed in corpus, not replacement model.

## Result

For existing infinite-support dark weight

`w_n = (1/2)^n + 2 delta_(n=0) - 4 delta_(n=1)`

and physical endpoint base

`q = exp(-1/(4 epsilon))`, `epsilon>0`,

Lean proves convergent exact response

`sum_(n>=0) w_n q^(n+1) = q(1-q)(3-2q)/(1-q/2) > 0`.

The double series obtained by pairing existing infinite rank-one dark matrix with two endpoint
winding legs converges, factors as square of scalar response, and is strictly positive. Hence kernel
that is nonzero, positive-semidefinite on every finite principal section, infinitely supported, and
identically dark to full countable three-moment recoil reporter is visible to literal physical endpoint
winding at every positive backreaction scale.

## Proof certificate

Split weighted response into geometric tail plus two low-grade corrections. Tail has ratio `q/2` and
sum `q/(1-q/2)`; adding corrections `2q-4q^2` factors into stated positive rational function. HC29
supplies `0<q<1`. Absolute summability permits corpus product-`tsum` factorization of rank-one matrix
energy into response squared.

Lean module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekInfiniteDarkEndpointWindingSeparation.lean`.

Main declarations:

- `schwarzschildParikhWilczekInfiniteGradeDarkWeight_endpointPower_hasSum`
- `schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse_eq`
- `schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse_pos`
- `schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy_eq_sq`
- `schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy_pos`
- `schwarzschildParikhWilczekEndpointWinding_defeats_infiniteGradeDarkMatrix`

Verification: direct `lake env lean` passed; target-only `lake build
GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekInfiniteDarkEndpointWindingSeparation`
passed (11614 jobs). Six audited endpoints depend only on `[propext, Classical.choice, Quot.sound]`.
Formal lint reports no error in module; repository-wide failure remains limited to pre-existing
unreachable modules outside HC31.

## Corpus and literature novelty audit

Mandatory corpus searches covered PW oriented recoil, endpoint winding, countable grade matrices,
infinite-support completion, geometric generating functions, and `l1` uniqueness. Corpus supplied
exact infinite three-moment dark kernel and HC29 endpoint powers, but no evaluation pairing them.

Primary-source searches checked Parikh--Wilczek, [*Hawking Radiation as
Tunneling*](https://arxiv.org/abs/hep-th/9907001); Zhang--Cai--You--Zhan, [*Hidden Messenger
Revealed in Hawking Radiation*](https://arxiv.org/abs/0903.0893); Corda, [*Precise model of Hawking
radiation from the tunnelling mechanism*](https://arxiv.org/abs/1411.1213); Chen--Huang,
[*Revisiting the tunneling spectrum and information recovery of a general charged and rotating black
hole*](https://arxiv.org/abs/1501.03687); and Gangopadhyay, [*Minimal length effects in black hole
thermodynamics from tunneling formalism*](https://arxiv.org/abs/1405.4229). Literature includes
nonthermal energy-conserving spectra, sequential correlations, level dependence, and other summable
infinite corrections. Searches found no theorem separating a three-moment infinite dark kernel by
the finite-mass endpoint winding, nor corresponding countable PSD energy law. Novelty claim is
bounded to this source-specific separation theorem as of 2026-08-28.

## Gates

- [x] 0 -> 1: source-exact target, explicit corpus counterexample, summable-series attack
- [x] 1 -> 2: dependency-closed generating-function and energy proof
- [x] 2 -> 3: unconditional Lean theorem, target build, axiom audit
- [ ] 3 -> 4: standalone publication draft

## New insight

- **Known obstruction removed:** physical endpoint winding sees corpus's strongest explicit
  admissible infinite-support PW-dark kernel.
- **Orientation:** response is strictly positive for every positive backreaction scale, whereas HC29
  finite polynomial-dark response is strictly negative.
- **Sharp remaining boundary:** remaining scalar darkness requires a different summable sequence
  whose analytic generating function vanishes on physical endpoint bases; classification of all such
  sequences is next burden.

## Remaining burden

Classify all absolutely summable grade sequences from their endpoint response on `q in (0,1)`, then
couple resulting faithful grade channel to source-derived oriented recoil before Xi-divisor
specialization.

## Log

- 2026-08-28 — conjectured from explicit countable PW dark vector and HC29 endpoint Laplace law
- 2026-08-28 — first attempt reduced to `HasSum` normalization and denominator bookkeeping
- 2026-08-28 — exact positive response and countable square-energy law formalized and audited
