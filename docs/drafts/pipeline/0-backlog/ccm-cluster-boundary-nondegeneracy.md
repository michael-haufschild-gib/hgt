# Boundary nondegeneracy of top Takagi edge profiles (CCM clustered residue)

- **ID:** ccm-cluster-boundary-nondegeneracy
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** goal-loop rows 951, 955, 962 · MUST-1218/1225/1226 (CCM parity lane)
- **Statement:** For nodes `ζ_j = δ − iτ_j` (common `δ > 0`, distinct real `τ_j`) and masses `M_j > 0`, every maximiser `W*` of `|Σ_j M_j W(ζ_j)²|` over the unit sphere of `H²(Re ζ > 0)` has `lim_{x→∞} x W*(x) ≠ 0`. Equivalently, `Σ_j M_j W*(ζ_j) ≠ 0`; in the time domain, `w*(0) ≠ 0`.

## Goal
Row 962 [P] shows the following. At large height (`t_j = T + τ_j`, `T → ∞`, fixed shape), the CCM parity balance along the aperture line satisfies `T·F(θ(a)) = −(2/N) Im(e^{ic}A₀) + O(1/T)`, an exact sinusoid in the common phase `c = −2Ta`, with `A₀ ∝ (Σ_k x_k)(…)`. Nondegeneracy at one point of the relative-phase orbit (which contains `0`) therefore gives odd ground states cofinally for every cluster shape at large height. That would close the residue of row 955 except a compact low-height family.

## Gates
- [ ] 0 → 1
- [ ] 1 → 2
- [ ] 2 → 3

## Approach
- **Known [P]:** `m = 2`, equal masses, zero relative phase. The swap+conjugation symmetry forces `v₂ = v̄₁` at the top. Then `Σx = 0` would need `Re h ≥ g` and `Im h = 0` for `G = [[g,h],[h̄,g]]`, which contradicts `|h| < g`.
- **Variational constraints if `w*(0) = 0`:** truncating `[0, ε)` costs only `O(ε³)` norm. The `O(ε²)` truncation term vanishes because `Σ M_j v_j = 0`. Hence `φ(ε) = e^{2εδ}|Σ M_j e^{−2iετ_j}v_j²|` has a two-sided local maximum at `0` up to `O(ε³)`. This gives `Im(e^{−iα}Σ M_jτ_jv_j²)/λ = −δ` but no contradiction yet.
- **Ideas:**
  - a Perron–Frobenius analogue for Hankel operators with symbol `Σ M_j e^{−ζ̄_j s}`;
  - analyticity in the relative phases plus one explicitly nondegenerate point on the orbit, giving nondegeneracy except at isolated points;
  - a search for a symmetric counterexample with `m = 3`, which would itself be informative: a first-order-invisible cluster.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:**
- **Strongest positive survivor:**
- **New insight:**
- **Status:**

## Log
- 2026-10-11 — created in 0-backlog from goal-loop row 962.
