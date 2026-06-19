# G1 — difference Hölder (§59)

- **ID:** G1-difference-holder
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/G1-difference-holder.md · 00-status row #3
- **Statement:** `ζ` and every arithmetic L-function satisfy no finite-order linear `q`-difference
  equation (difference-category Hölder).

## Goal
Was the leading C5 candidate (the Door-2 verdict below grades it BRIDGE): a theorem meant to turn the
infinite-base structure N1 from optional into necessary. With Hölder's differential half it places `ζ`
in the native zone.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: paper proof in `multi-q-difference-galois-foundations §59` (Galois-dimension
  argument: a holonomic diagonal forces a finite-dimensional `s`-difference-Galois group, but the
  arithmetic `s`-monodromy `g = (p^{-1})_p` has infinite-dimensional Zariski closure when `Λ = 0`)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Door-2 verdict (2026-06-19): BRIDGE, not NATIVE
Stripped of multi-`q` vocabulary the proof is single-operator difference Galois (the one shift `s↦s+1`,
van der Put–Singer; ADH is the named tool) + closure-of-`⟨g⟩`-in-`𝕋^∞` `= corank` (Kronecker–Weyl) +
`{log p}` ℚ-independent (unique factorization). The simultaneous-`σ_p` group `G_L` is never used, so a
parent proves it: §59 is a genuine **BRIDGE** (it internalizes and generalizes Hölder), **not** the C5
keystone. Full reasoning: `../../door/door-C5-irreducibility-and-door-2-retest.md`.

## Next steps
1. As a BRIDGE it may still be **formalized** and written up — but it no longer counts toward C5. The
   `{log p}` floor is ledgered (`logPrime_no_rat_relation`).
2. C5 now needs a theorem using the `σ_p` **jointly and irreducibly** — see the bucket's "forward" note.

## Notes
- This is the **difference**-category statement. Literal *differential* Hölder for `ζ` is an import
  (Hölder 1887); differential Hölder for general L is a separate open item.

## Log
- 2026-06-19 — created in 2-fully-proven (paper proof exists; next gate is Lean + the Door-2 verdict)
- 2026-06-19 — Door-2 verdict: **BRIDGE** (not NATIVE). Stays in 2-fully-proven as a proved bridge theorem; C5 candidacy closed.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the whole-ticket statement quantifies over `ζ` and arithmetic `L`-functions and relies on the external difference-Galois/Hölder machinery cited as §59 / vdPS / ADH. The local Lean development has no formal definitions of this category, arithmetic `L`-functions, or the imported theorem, so there is no no-hypothesis Lean proof of the stated ticket. The existing prime-log anchors are only the frequency floor.
