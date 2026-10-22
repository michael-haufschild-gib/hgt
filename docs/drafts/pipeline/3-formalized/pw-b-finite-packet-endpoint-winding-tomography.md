# PW-B finite-packet endpoint-winding tomography

- **ID:** HC30
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** PW-B
- **Date:** 2026-08-28
- **Statement:** For a packet supported on grades `0,...,N-1`, its responses to the literal Parikh--Wilczek endpoint winding at the `N` physical scales `epsilon_j = 1/(4(j+1))` determine every packet coefficient.

## Goal

Upgrade HC29 from separation of one explicit polynomial-dark family to faithful tomography of every
finite-support grade packet. Observable and sampling scales remain literal finite-energy
Parikh--Wilczek data; no generic nonlinear reporter or RH hypothesis enters.

## Result

For arbitrary `N` and coefficients `c : Fin N -> R`, define the positive source scales

`epsilon_j = 1/(4(j+1))`.

Existing exact endpoint law gives grade-`k` amplitude

`exp(-(j+1))^(k+1)`.

Lean proves

`(forall j, response(c,j)=0) iff c=0`.

Thus `N` explicit positive backreaction samples suffice to recover every coefficient of an
arbitrary `N`-grade packet. Result includes `N=0` uniformly and eliminates every nonzero
finite-support dark packet for this physical endpoint channel.

## Proof certificate

Set `q_j=exp(-(j+1))`. Factoring nonzero row multiplier `q_j` reduces sampled response matrix to
ordinary Vandermonde matrix with entries `q_j^k`. Real exponential injectivity makes nodes `q_j`
pairwise distinct. `Matrix.det_vandermonde_ne_zero_iff` gives nonzero determinant, and
`Matrix.eq_zero_of_mulVec_eq_zero` forces coefficient vector to vanish.

Lean module:
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekFinitePacketEndpointTomography.lean`.

Main declarations:

- `schwarzschildParikhWilczekEndpointTomographyScale_pos`
- `schwarzschildParikhWilczekEndpointWindingLaplaceBase_sample`
- `schwarzschildParikhWilczekFinitePacketEndpointResponse_eq`
- `schwarzschildParikhWilczekEndpointTomographyNode_fin_injective`
- `schwarzschildParikhWilczekFinitePacketEndpointResponse_eq_zero_iff`

Verification: direct `lake env lean` passed; target-only `lake build
GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekFinitePacketEndpointTomography` passed
(11614 jobs). Five audited declarations depend only on `[propext, Classical.choice, Quot.sound]`.
Formal lint reports no error in this module; repository-wide failure remains limited to pre-existing
unreachable modules outside HC30.

## Corpus and literature novelty audit

Mandatory corpus searches covered PW endpoint winding, finite-packet tomography, physical
backreaction sampling, exponential-polynomial observability, and Vandermonde kernels. Corpus
supplied HC29 endpoint powers and general determinant infrastructure but no application recovering
arbitrary PW grade packets from finitely many physical scales.

Primary-source searches checked Parikh--Wilczek, [*Hawking Radiation as
Tunneling*](https://arxiv.org/abs/hep-th/9907001); Zhang--Cai--You--Zhan, [*Hidden Messenger
Revealed in Hawking Radiation*](https://arxiv.org/abs/0903.0893); Corda, [*Precise model of Hawking
radiation from the tunnelling mechanism*](https://arxiv.org/abs/1411.1213); and Chen--Huang,
[*Revisiting the tunneling spectrum and information recovery of a general charged and rotating black
hole*](https://arxiv.org/abs/1501.03687). They study energy-conserving nonthermal emission,
sequential correlations, entropy conservation, and level-dependent probabilities. Searches found no
finite-sample Vandermonde theorem reconstructing arbitrary PW grade amplitudes. Novelty claim is
bounded to this source-specific identifiability theorem, not to Vandermonde algebra, as of
2026-08-28.

## Gates

- [x] 0 -> 1: source-pure statement, corpus gap, Vandermonde attack
- [x] 1 -> 2: dependency-closed finite-sample proof
- [x] 2 -> 3: unconditional Lean theorem, target build, axiom audit
- [ ] 3 -> 4: standalone publication draft

## New insight

- **Finite-support closure:** HC29's one-family separation extends to every finite grade packet.
- **Finite observability:** continuum access is unnecessary; packet length many explicit physical
  scales suffice.
- **Sharp remaining boundary:** any remaining darkness must be an infinite-support/completion
  phenomenon or arise when the grade channel is coupled to recoil orientation.

## Remaining burden

Move to source-first infinite packet/completion control and couple recovered grade data to oriented
recoil before Xi-divisor specialization. A finite polynomial or finite-support counterexample can no
longer carry that burden.

## Log

- 2026-08-28 — conjectured from HC29 endpoint powers plus corpus Vandermonde infrastructure
- 2026-08-28 — first Lean attempt exposed matrix-orientation mismatch; corrected to row-sample Vandermonde
- 2026-08-28 — formalized, wired, target-built, axiom-audited, and novelty-audited
