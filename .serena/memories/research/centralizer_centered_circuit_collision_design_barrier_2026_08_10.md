# Centralizer-centered circuit collision and design barrier (2026-08-10)

New paper-proof card:
`docs/drafts/pipeline/2-fully-proven/centralizer-centered-circuit-collision-and-design-barrier-law.md`.

Parents:
- `all-replica-static-centralizer-planar-separation-law.md`
- `gate-walk-green-bellman-tropicalization-law.md`

Proved:
1. Abstract exact identity for self-adjoint L with zero-mode projector P and universal fixed subspace N⊂ker L:
   <e^{-itL}x,M>-<Px,M>=<δ_t,(I-P)M>=<δ_t,(I-Π_N)M>.
2. For padded length-s circuit dictionary (N=M^s), one random-circuit replica moment absorbs complete union:
   1_{max fidelity≥a} ≤ N a^{-r} A_{s,r}.
3. Exact static/completed decomposition:
   A_{s,r}(H,t)-bar A_{s,r}(H)
   = <(e^{-itL_{H,r}}-P_{H,r})x_r, M_{s,r}>.
   Exact projective r-design target moment makes physical collision equal completed baseline for every H,t.
4. Flat occupied spectral seed has completed target moment ≤r!D^{-r}.
   Hence shortcut probability ≤N a^{-r}(r!D^{-r}+Δ_{s,r}(t)), with Δ the signed annealed centralizer-centered directional defect.
5. Support-rank design barrier:
   for target moment supported on ≤N pure states,
   ||(I-Π)M||_HS² = Tr(M²)-1/h ≥1/min(N,h)-1/h,
   h=binom(D+r-1,r).
6. Exact incompatibility:
   if N a^{-r} r!D^{-r}<1 (completed moment is useful), then
   N<a^rD^r/r!≤h and ||(I-Π)M||_HS>sqrt((1-a^r)/N).
   Thus universal design/norm transfer is forced to square-root N^{-1/2}, while one shortcut detection needs a^r/N.
7. Heavy conjecture loop:
   - target randomization exact: proved;
   - approximate design/norm closure: falsified sharply;
   - quenched centered norm: falsified by parent unitary-complement theorem;
   - signed directional defect survives.

Exact remaining core:
Prove the signed directional estimate for Δ_{s,r}(t) at r=Theta(D), s=Theta(D/log M), Brown skeleton times, after common return/carrier excision. No absolute norm, design distance, or positive channel can replace it.

Honest boundary:
- no Brown ramp yet;
- flat spectral seed used for r!D^{-r};
- state rank barrier needs representation-specific replacement for restricted Choi-unitary target orbit;
- novelty is only candidate composition; projection, designs, purity/rank, Steinhaus are standard;
- Lean deferred because user said corpus is being refactored. No Lean process started by this task.
