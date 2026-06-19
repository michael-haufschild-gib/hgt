# The live motivic period tower — two non-interacting Galois towers (SEED-U)

- **ID:** motivic-period-tower
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FUTURE
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#80 SEED-U), ../../door/bucket-the-seam-archimedean-obstruction.md, ../../door/G2-multi-q-siegel-shidlovsky.md · 00-status row #102
- **Statement:** The transcendence tower recurses **motivically, not spectrally**: `𝒫_𝒵 = ℚ⟨P_k⟩`
  carries a **motivic Galois action** (Kontsevich–Zagier / mixed-Tate); the "fixed point" = the
  pro-unipotent radical of its motivic Galois group. **Conjecture:** the field has **TWO Galois towers**
  — a **dead spectral one** (the superzeta `𝒵` has no Euler product, by the First Theorem, so
  `ζ → 𝒵 → …` does not recurse spectrally) and a **live motivic one** — and the **seam is their
  non-interaction** (`[𝔾_a, 𝔾_m] ≠ 0`). **Falsifiable** via Voros's explicit `𝒵(2m) ∈ {π, ζodd,
  Stieltjes}`.

## Goal
Locates the **correct recursion** for the transcendence tower (motivic), correcting the seam-collapse
category error "fixed point = the prime." Routes G2 into Nesterenko / motivic-Galois territory (a domain
*with* transcendence tools) and gives the seam a precise tower form. **Falsifiable**, hence real (not a
content-free restatement).

## Door passport
- **Door-1:** the dead-spectral side is witnessed natively (`SuperzetaResolvent`: the superzeta is the
  additive resolvent trace `Σ_i(1−r_iX)^{−1}`, Σ not ∏ — a Lean theorem).
- **Door-2:** the motivic tower itself is classical motivic Galois theory (IMPORT); the **non-interaction
  with the spectral tower** (the seam) is the native diagnosis. The §42 discipline is met by
  falsifiability.

## Gates
- [ ] 0 → 1  in-progress: the two towers pinned (spectral dead via the First Theorem; motivic live via
  `ℚ⟨P_k⟩`); the non-interaction stated; the Voros `𝒵(2m)` falsifier set up
- [ ] 1 → 2  fully-proven: the motivic Galois action on `{P_k}` computed; the non-interaction proved (or the
  falsifier triggered)
- [ ] 2 → 3  formalized — `SuperzetaResolvent` ledgers the dead-spectral side; the motivic side is the target
- [ ] 3 → 4  publication-ready

## Approach
Compute the motivic Galois action on `ℚ⟨P_k⟩` (the superzeta values); check against Voros's explicit
`𝒵(2m) ∈ {π, ζodd, Stieltjes}` (the falsifier). Use the First-Theorem fact (superzeta has no Euler
product) to kill the spectral recursion, leaving the seam = the towers' non-interaction.

## Cross-references
- `tate-prime-rigidity.md` — the motivic block of the secular weld is the live tower's content.
- `g2-dss-lower-bound.md` — routes DSS into the motivic-Galois framework.
- `../../door/bucket-realization-and-fake-family.md` — the superzeta-is-a-fake verdict (no Euler product).

## Log
- 2026-06-19 — created in 0-backlog. The live motivic period tower (SEED-U / B23): two non-interacting
  Galois towers, the seam in tower form; falsifiable via Voros.
