# The seam firewall — finite-place ⊥ archimedean positivity (G6 / SEED-A)

- **ID:** seam-firewall
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#67 SEED-A), ../../door/bucket-the-seam-archimedean-obstruction.md · 00-status row #106
- **Statement:** The **multiplicative (finite-place) Galois data** and the **archimedean continuation
  data** are difference-Galois-**independent** in the strip — **no finite-place positivity forces the
  archimedean positivity.** If TRUE, it sharpens why number-field RH is irreducibly harder than
  function-field RH (an extra place the finite places cannot reach); if FALSE (some higher `ind(D)`
  constraint survives), it is a **route to RH**.

## Goal
The **structural reason A1 (RH) is not free.** The seam bucket's central diagnosis — multiplicative-only
methods are apex-blind — turned from an empirical observation into a **posable independence statement**.
A decisive result either way is foundational: independence confirms the wall is genuinely the extra
archimedean place; a surviving constraint would be a positivity route across the seam.

## Door passport
- **Door-4:** the statement is exactly about the seam (`{multiple bases} ∩ {archimedean place}`) — the
  native zone where all parents fail; over `F_q` there is no archimedean place, so the firewall is vacuous
  there (Door-5 calibration: the firewall is what ℚ adds).
- **Door-2:** the content is the *independence of the two place-blocks* in the difference-Galois group —
  a native structural claim, not a renamed classical separation. **Caveat:** tagged "RH-equivalent —
  needs hook"; the work is to give it an explicit difference-Galois hook so it is not content-free (§42
  trap).

## Gates
- [ ] 0 → 1  in-progress: the two place-blocks defined; "difference-Galois-independent in the strip" given
  an operational meaning; the `ind(D)` constraint posed as the falsifier; an explicit hook found (avoid §42)
- [ ] 1 → 2  fully-proven: independence proved (A1 not free) OR a surviving constraint found (a route to RH)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Split `G_L` into the finite-place (multiplicative, trace-class, `⊗`) block and the archimedean
(derivation `D`, additive, `⊕`) block; pose their difference-Galois independence. The obstruction class
is `ω` (`compute-omega-h2-gl.md`): `ω ≠ 0` is the `[𝔾_a, 𝔾_m] ≠ 0` non-interaction = the firewall;
`ind(D)` (the index of the archimedean derivation) is the candidate surviving constraint to test.

## Cross-references
- `compute-omega-h2-gl.md` — `ω = [𝔾_a, 𝔾_m]` is the firewall's obstruction class.
- `a1-a2-unification-brick.md` — the firewall is why the two faces don't conspire (the seam).
- `../../door/bucket-the-seam-archimedean-obstruction.md` — the structural diagnosis this card poses.

## Log
- 2026-06-19 — created in 0-backlog. The seam firewall (G6, SEED-A): finite-place ⊥ archimedean
  positivity — the structural reason A1 is not free, posed as a difference-Galois independence statement.
