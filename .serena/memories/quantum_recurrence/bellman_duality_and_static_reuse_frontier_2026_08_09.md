# Brown–Susskind static-local frontier, 2026-08-09

New paper-proved cards:
- `docs/drafts/pipeline/2-fully-proven/exact-penalty-robust-circuit-bellman-duality.md`
- `docs/drafts/pipeline/2-fully-proven/instant-exact-complexity-calibration-singularity-law.md`

Exact duality: for finite inverse-closed isometric gate set G,
V_{λ,ε}(x)=min_w (|w|+λ(d(x,W_wχ)-ε)_+) is λ-Lipschitz, obeys exact Bellman obstacle recursion, is maximal among Bellman subsolutions, and equals C_ε(x) at finite λ once λ exceeds the lower-layer clearance threshold. Therefore bare existence of a robust Bellman calibration is circular; Brown progress requires an external formula not evaluating reachable sets, distances to circuit layers, or complexity.

Conditioning survivor: if d(x(t),χ)≤v|t| and exact complexity is c_t, any λ-Lipschitz certificate reaching c_t satisfies λ≥c_t/(v|t|). Combined with the rational two-local instant exact-complexity theorem, λ≥(2^n-1)/(16|t| ||H_n||). Exact transcendence cannot seed a robust fixed-resolution Brown ramp.

New SOTA boundary: Zlokapa–Allen–Harrow arXiv:2607.19852 uses a static bounded-degree local base gadget only at unit time; linear late-time lower bound refreshes disjoint blocks in time, equivalently grows static system size with t. It does not prove repeated-reuse growth for one fixed-size time-independent H.

Live open core: construct and prove quenched Brown-rate growth of an explicit reuse-sensitive endpoint Bellman subsolution for the ordinary fixed-shell q-local ensemble, after one common return excision. Lifted history does not descend; exact transcendence is ill-conditioned; local observables saturate polynomially; unstructured orbit geometry is defeated by the small complete orbit net.
