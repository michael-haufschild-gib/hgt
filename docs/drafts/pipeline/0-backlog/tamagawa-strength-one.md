# Positive-direction strength = exactly 1 (Tamagawa / no-margin threshold, SEED-B)

- **ID:** tamagawa-strength-one
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FUTURE
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#67 SEED-B), ../../door/bucket-the-no-margin.md · 00-status row #105
- **Statement:** The archimedean continuation "pump" `= L_∞(1) · Res_{s=1} ζ = (π^{−1/2} Γ(½)) · 1 = 1`
  **exactly** (`Γ(½) = √π`). **Conjecture:** the single positive direction has strength **exactly 1**
  (Tamagawa), and **1 is exactly the threshold** for a second positive direction — the no-margin as a
  theorem about the archimedean continuation engine at the paired seam points `{0, 1}`.

## Goal
An **exact-identity hook** for the no-margin: the knife-edge is not approximate — the strength of the
one positive direction equals the Tamagawa number 1, which is *precisely* the threshold for criticality.
This gives `no-margin-uniform-bound.md` a concrete, computable anchor (the `{0,1}` seam points and the
`Γ(½) = √π` identity), distinct from the asymptotic two-rate signature.

## Door passport
- **Door-1/4:** the pump is the archimedean continuation engine at the paired seam points `{0,1}` (the
  native archimedean place); `L_∞(1) = π^{−1/2}Γ(½)` is its explicit value.
- **Door-2:** the identity `(π^{−1/2}Γ(½))·1 = 1` is elementary (BRIDGE); the **claim that 1 is the
  threshold for a second positive direction** is the native-candidate content (the no-margin as a theorem).

## Gates
- [ ] 0 → 1  in-progress: the pump identity restated; "strength = Tamagawa = 1 = threshold" given an
  operational meaning (what a "second positive direction" is, and why 1 is its onset)
- [ ] 1 → 2  fully-proven: the threshold claim proved (1 = the onset of a second positive direction)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Make precise the "positive directions" of the continuation engine at `{0,1}`, compute the first
direction's strength via `L_∞(1) · Res_{s=1}ζ = (π^{−1/2}Γ(½)) · 1 = 1`, and show 1 is the critical
threshold for a second direction to open — the no-margin as an exact archimedean theorem.

## Cross-references
- `no-margin-uniform-bound.md` — the no-margin open core this gives an exact anchor for.
- `weil-positivity-operator.md` — the "positive direction" is the operator's positive cone.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — the `{0,1}` paired seam points.

## Log
- 2026-06-19 — created in 0-backlog. Tamagawa strength = 1 (SEED-B): the no-margin as an exact-identity
  theorem at the archimedean continuation engine.
