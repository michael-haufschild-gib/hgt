# G3 — the corank / holonomy dichotomy (§60)

- **ID:** G3-corank-dichotomy
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/G3-holonomy-dichotomy.md · 00-status row #20
- **Statement:** An infinite-base diagonal is holonomic ⟺ `corank(Λ) < ∞`, via
  `dim ⟨g⟩-closure = corank(Λ)`; arithmetic (`Λ = 0`) is the `corank = ∞`, non-integrable extreme.

## Goal
Frames holonomicity through `corank(Λ)` (a would-be native invariant, C3) by tying it to geometric
integrability. The structural twin of G1, and the other leading C5 candidate (the Door-2 verdict below
grades it BRIDGE).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: paper proof in `multi-q-difference-galois-foundations §60` (both directions,
  all bases)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Door-2 verdict (2026-06-19): BRIDGE, not NATIVE
(⟹) is §59's argument; (⟸) is §49.2 + Lipshitz 1988 (the diagonal of a `D`-finite series is `D`-finite —
an import). The invariant `corank(Λ)` is the dimension of a torus-subgroup closure — a classical
algebraic-group invariant renamed — so it **also fails Door-3**. BRIDGE, not the C5 keystone. Full
reasoning: `../../door/door-C5-irreducibility-and-door-2-retest.md`.

## Next steps
1. As a BRIDGE it may still be **formalized** (the `dim ⟨g⟩-closure = corank(Λ)` identity; finite
   annihilator slices ledgered, `finitePrimeLogAnnihilator_eq_singleton`) and written up.
2. C5 now needs a theorem using the `σ_p` **jointly and irreducibly** — see the bucket's "forward" note.

## Log
- 2026-06-19 — created in 2-fully-proven (paper proof exists; next gate is Lean + the Door-2 verdict)
- 2026-06-19 — Door-2 verdict: **BRIDGE** (also fails Door-3). Stays in 2-fully-proven as a proved bridge theorem; C5 candidacy closed.
