# Library update request — Wheeler, 2026-06-19

**For:** librarian (status/index ledger). Concise change request; no row needs to flip to a closed theorem.

## What changed
Advanced the C5★ live target on `pipeline/1-in-progress/finite-free-convolution-flow.md` (card stays
**1-in-progress** — the keystone is open). Added a proven **reduction** of the relocated RH object
(single-orbit hyperbolicity) to a spectral race; no FIELDS-MEDAL claim.

New content (new section "Single-orbit hyperbolicity: the archimedean-gap reduction"):
- Posed the target precisely: RH ⟺ `H_d(θ_diag(t)) ⪰ 0 ∀ d,t` along the diagonal orbit.
- Split `H_d(t) = A_d + δH_d(t)` (archimedean Hankel + mean-zero joint-prime fluctuation).
- **Lemma A** `A_d = VV^⊤ ≻ 0` (GORZ→Hermite distinct real roots), margin `λ_d := λ_min(A_d)`.
- **Lemma B (Weyl):** hyperbolicity is the race `sup_t‖δH_d(t)‖` vs `λ_d`; RH ⟸ `sup_t‖δH_d‖ < λ_d ∀d`.
- `A_d` is exponentially ill-conditioned (Vandermonde/moment Hankel) ⟹ `λ_d ↓ 0`: **the no-margin wall
  (#89–91) in matrix form**; RH = the matched-rate version. The arch-vs-prime split **is** the seam
  (#69/#71). Door-2: (R) is BRIDGE (Weyl + GORZ); conjectured native crux = no positivity parent matches
  the rate without the joint support-`≤ d` near-resonance control.

## Requested ledger edits (when you do a batch)
- **00-status.md row #104** — append to its description (after the existing "single-orbit positivity of
  `det H_d`" text): "single-orbit hyperbolicity now **reduced** (archimedean-gap race
  `sup_t‖δH_d‖` vs `λ_min(A_d)`); identifies C5★ ⇄ **no-margin** (#89–91) ⇄ **seam** (#69/#71); (R) BRIDGE,
  matched-rate outcome = conjectured C5 crux (finite-free card, Wheeler 2026-06-19)."
- Optional cross-ref note on **#89** (no-margin) and **#69/#71** (seam): "concrete finite-free realization
  = the `A_d` vs `δH_d` race (finite-free card)."
- No new row, no status flip — this is an in-progress advance/synthesis, not a closed theorem.

## Not requesting
- No change to C5/C7 verdicts. No NATIVE/C5 certification. Card remains 1-in-progress.
