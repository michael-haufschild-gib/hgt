# Coherent compensation by several actual collars

- **ID:** signed-prime-polar-multiple-collars
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Parent:** `1-in-progress/signed-prime-polar-transport-2026-10-17.md`
- **Count:** uncounted; requires a distinct full transport theorem.

## Question

Can several signed collar sources exploit source geometry unavailable to the
single-collar optimizer, while retaining every cross term in the gauge cost?

For g_i the backward average on [A_i,A_i+d_i], s_i=g_i', k_i=s_i-g_i/2,
and Δ=A_i-A_j, test the exact kernel identities

B_ij=∫g_i g_j=(d_i d_j)⁻¹∫_[A_i,A_i+d_i]∫_[A_j,A_j+d_j]h(y-z)dzdy,
S_ij=∫s_i s_j=[h(Δ)-h(Δ-d_j)-h(Δ+d_i)+h(Δ+d_i-d_j)]/(d_i d_j),
G_ij=∫k_i k_j=S_ij+B_ij/4.

The last identity should follow from integrating (g_i g_j)' over the line.
Then arbitrary real coefficients retain the full quadratic forms B,S,G.
Derive an actual source support budget for the mixture and transfer its gauge
bound through the signed prime–polar packet, before optimizing coefficients.
The source Gram inequality must discharge singular directions; no invertibility
or positive-definiteness hypothesis may be added to main endpoints.

## Gates

- [x] Initial search `/tmp/spp7-next-search.json`: partial=false/errors=[], snapshot
  coverage; retrieved discrete Gram and smooth gauge precedents, plus current
  unverified single-collar work. Field text search found no mixed collar gauge
  kernel. This is not an external novelty claim.
- [ ] Inspect precise mixed-source dependencies and refine the substantive target.
- [ ] Dependency-closed paper proof, including singular coefficient geometry.
- [ ] Formalize exact kernels and a full source-only transport endpoint.
- [ ] Direct leaf and axiom audits; wiring, lint/index, ledger.

A polarization identity alone does not count. Seek a useful coherent mixture
certificate and a proved comparison with one-collar trials. No grid blindness,
source differentiability premise, cutoff-uniform assertion, or RH work.
