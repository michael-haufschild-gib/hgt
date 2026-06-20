# [FALSIFIED as a theorem] Tamagawa strength = 1: trivial identity + ill-posed threshold (SEED-B)

- **ID:** tamagawa-strength-one
- **Stage:** 5-failed
- **Type:** FALSIFIED-as-theorem (2026-06-19, Professor) — exact identity is a trivial BRIDGE (ζ normalization); the "1=threshold" conjecture is not a well-posed theorem (unconditional residue cannot force RH-conditional margin; coherent reading is EMBASSY)
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

## VERDICT — 2026-06-19 (Professor): conjecture FAILS as a theorem; trivial-identity BRIDGE + EMBASSY analogy

Interrogated the two parts (scientific-method: strip to essentials, attack as false, verify).

**Part 1 — the exact identity: TRUE but TRIVIAL (BRIDGE).** `pump = L_∞(1)·Res_{s=1}ζ = (π^{−1/2}Γ(½))·1 = 1
= Res_{s=1}Λ` (verified, `Γ(½)=√π`, Dirichlet residue 1). This is **just the standard normalization** of the
completed `Λ` (the simple pole at `s=1` has residue 1). Not new content; not worth a standalone card.

**Part 2 — the "1 = threshold for a second positive direction" conjecture: NOT a well-posed theorem.**
- **The forcing reading is INCOHERENT.** `Res_{s=1}ζ = 1` is **UNCONDITIONAL** (Dirichlet: `lim(s−1)ζ(s)=1`,
  no reference to the zeros), whereas the no-margin / Weil-positivity threshold (`λ_min(W)→0`) is
  **RH-CONDITIONAL** (a spectral fact about the zeros). An unconditional constant **cannot force** an
  RH-conditional threshold. The pole at `s=1` (a trivial pole) is categorically distinct from the
  Weil-operator spectrum (the zeros) — conflating "residue at the trivial pole" with "onset of a second
  positive direction of the zero-spectrum" is a **category slip**.
- **"A second positive direction" is undefined** here; no construction makes `1` its onset (gate 0→1 openly
  admits this).
- **The only coherent reading is an EMBASSY analogy:** "unit gain (residue 1) = marginal stability." That is a
  *metaphor* (the archimedean pump is marginally stable), not a theorem about the zeros; it does not connect
  the residue to the actual no-margin.

**Disposition.** By the terminalization criterion (a conjecture → 5-failed if it reduces to a known wall or is
incoherent): the coherent part reduces to the **no-margin = RH** (already carded, `no-margin-uniform-bound`,
OPEN CORE), and the forcing part is **incoherent** (unconditional ≠ conditional). So the *claimed* "no-margin
as an exact archimedean theorem" does **not** exist. → `5-failed`.

**Salvage (kept, not lost):** (i) the trivial identity `Res_{s=1}Λ=1` is ζ's normalization — known, BRIDGE,
folded into general FE normalization; (ii) the "unit-gain = marginal-stability" picture is EMBASSY (inspiration
for the no-margin, but not a mechanism). Nothing terminalizable as a new theorem. The real no-margin content is
`no-margin-uniform-bound.md` (RH-axis, separate, open). Verified: `computations/2026-06-19-... (inline; residue
unconditional)`.
