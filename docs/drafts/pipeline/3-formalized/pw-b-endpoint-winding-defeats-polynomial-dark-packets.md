# PW-B endpoint winding defeats polynomial dark packets

- **ID:** HC29
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / POSITIVE SURVIVOR
- **Route:** PW-B
- **Date:** 2026-08-28
- **Statement:** Literal finite-mass Parikh--Wilczek endpoint winding has strictly negative response and strictly positive rank-one energy on every finite-polynomial grade-dark packet.

## Goal

Test an actual source-derived nonpolynomial PW observable against the complete family of
finite-polynomial dark packets, rather than postulating a generic nonlinear channel.

## Result

At positive backreaction parameter `epsilon`, set

`q = exp(-1/(4 epsilon))`.

Then `0<q<1`, and the exact finite-energy endpoint amplitude of winding grade `k` is `q^(k+1)`.
For the polynomial-dark packet of reporter degree `d`, whose order is `N=2d+1` and whose weights
are `w_k=(-1)^(N-k) choose(N,k)`, Lean proves

`sum_{k=0}^N w_k q^(k+1) = q(q-1)^N < 0`.

The rank-one PSD dark-matrix energy against two endpoint winding profiles is exactly the square of
that response and is therefore strictly positive. This holds for every `d` and every
`epsilon>0`.

Thus literal nonperturbative finite-mass endpoint winding detects every known finite-polynomial PW
dark packet. This is a source-exact escape from the terminal finite-polynomial grade algebra.

## Proof certificate

The existing physical endpoint law gives action `A_k=(k+1)/4` and amplitude
`exp(-A_k/epsilon)`, which is exactly `q^(k+1)`. The binomial theorem evaluates the dark response
as `q(q-1)^N`. Since `N=2d+1` is odd and `0<q<1`, its sign is strictly negative. Expanding the
rank-one matrix outer product factors the double sum as the square of the same response.

Lean module:
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekEndpointWindingPolynomialDarkSeparation.lean`.

Main declarations:

- `schwarzschildParikhWilczekWindingTerm_energyEndpoint_eq_laplaceBase_pow`
- `schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse_eq`
- `schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse_neg`
- `schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy_eq_sq`
- `schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy_pos`
- `schwarzschildParikhWilczekEndpointWinding_defeats_everyPolynomialDarkPacket`

Verification: direct `lake env lean` passed; target-only `lake build
GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekEndpointWindingPolynomialDarkSeparation`
passed (11613 jobs); six audited endpoints report only `[propext, Classical.choice, Quot.sound]`.

## Literature and corpus novelty audit

Mandatory corpus searches covered finite-mass PW entropy/tunnelling composition, nonlinear
cross-shell coupling, endpoint actions, finite-polynomial darkness, and alternating-binomial
exponential response. Corpus supplied both ingredients—the literal endpoint winding and the sharp
polynomial dark family—but no theorem paired them or proved all-degree strict separation.

Primary-source searches checked Parikh--Wilczek, *Hawking Radiation as Tunneling*
(arXiv:hep-th/9907001); Zhang--Cai--You--Zhan, *Hidden Messenger Revealed in Hawking Radiation*
(arXiv:0903.0893); and Corda, *Precise model of Hawking radiation from the tunnelling mechanism*
(arXiv:1411.1213). They treat energy-conserving nonthermal emission, sequential correlations, and
level-dependent emission probabilities; searches found no alternating-binomial all-degree dark
packet separation or associated PSD energy theorem. Novelty claim is bounded to corpus plus these
searches as of 2026-08-28.

## Gates

- [x] 0 -> 1: corpus-derived source-exact exponential response conjecture
- [x] 1 -> 2: dependency-closed binomial proof
- [x] 2 -> 3: unconditional Lean theorem, target build, axiom audit
- [ ] 3 -> 4: standalone publication draft

## Positive survivor

- **Exact new insight:** known polynomial-dark PW packets are not dark to the physical finite-energy
  endpoint winding; response even has a fixed negative orientation.
- **Sharp boundary:** every finite polynomial reporter is defeated by some packet, but one literal
  exponential grade profile detects every packet in that family.
- **Status:** dependency-closed and formalized.

## Remaining burden

Couple endpoint winding response to the oriented recoil/holonomy channel before Xi-divisor
specialization. Prove a global source law whose vanishing or sign forces wall placement, while
retaining the strict grade faithfulness established here.

## Log

- 2026-08-28 — conjectured from literal endpoint amplitude and finite-polynomial no-go
- 2026-08-28 — exact response and strict sign proved for every degree and positive backreaction
- 2026-08-28 — formalized, wired, target-built, and axiom-audited
