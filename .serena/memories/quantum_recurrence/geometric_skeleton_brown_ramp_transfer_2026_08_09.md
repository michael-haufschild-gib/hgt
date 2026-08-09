# Geometric-skeleton Brown ramp transfer, 2026-08-09

New paper-proved bridge:
- `docs/drafts/pipeline/2-fully-proven/geometric-skeleton-brown-ramp-transfer-law.md`

Exact theorem: if static evolution has simulator cost (S(u,gamma)le vu+A), and at geometric times (T_j/T_{j-1}le q) it obeys (C_{epsilon_+}(psi_{T_j})>cvT_j-K), with (q(1-c)<1), then every (tin[T_0,T_N]) obeys
(C_{epsilon_-}(psi_t)>[1-q(1-c)]vt-(K+A)).
Proof is backward autonomous circuit composition from the next skeleton endpoint. Matching simulator composition gives the upper ramp.

A Brown interval of exponential duration needs only (O(n)) geometric endpoint events, not a linear mesh of (O(2^n)) times. If each bounded reporter failure is (Be^{-kappa r}), union over the skeleton needs only (r=O(log n+log(1/delta))). The former (r=O(n)) complete ramp mesh is retired.

Exact remaining core: for one fixed ordinary static local Hamiltonian after one common return excision, prove simultaneous robust Bellman escape/hardness at those prescribed geometric times and align the last endpoint with the start of the continuous near-maximal plateau. The transfer is a BRIDGE, not claimed novelty or Brown closure. Lean deferred during corpus refactor; no Lean process started.