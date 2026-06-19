# Ticket: ω splits (DSS/RH conflation resolved) + wild-kernel-freeness moonshot

**Date:** 2026-06-19
**Type:** sharpening of a shared Fields-Medal card (`compute-omega-h2-gl.md`) + index/status note. Do not edit door/00-* or compute-omega directly — race avoidance.

## New card
`../0-backlog/omega-splits-wild-kernel-freeness.md` — CONJECTURE (native) + moonshot, FIELDS MEDAL, Door BRIDGE (the split-diagnosis + `H²(free)=0` mechanism). Goal-directed (user: attack whether `ω` vanishes via the constraint/Galois).

## Correction to `compute-omega-h2-gl.md` (the conflation)
`compute-omega` asserts both `ω=0⟺RH` (§S/§T, polarization) and `ω=0⟺DSS` (§U/§V, ABP-lift). **These can't both hold** — RH and DSS are orthogonal (#54/#137), else `RH⟺DSS`. **Resolution: `ω` splits**, `ω = ω_mot ⊕ ω_pol`:
- `ω_mot=0 ⟺ motive/Tannakian exists ⟺ DSS` (transcendence axis);
- `ω_pol=0 ⟺ Q_W⪰0 ⟺ RH` (localization axis; leading member = the curvature `log|ξ| concave`, `phase-cancellation-crux` §3);
- `ω=0 ⟺ DSS ∧ RH` (motive **with** polarization). Respects orthogonality; matches §T treating `Q_W` as a separate datum. **Suggest folding this split into compute-omega** so the card no longer reads as `RH⟺DSS`.

## Moonshots (transcendence/Galois route — bank as sharpenings)
1. **`ω_mot=0 ⟺ K (wild kernel) free pro-unipotent`**, via the rigorous `H²(free Lie)=0`. **Apex = freeness, not infinitude:** §V's hypertranscendence gives `K` infinite-rank for free; the real question is whether infinite `K` is *free* (no exponential-period relations beyond shuffle) = DSS-cross. A **Galois-structural** target, bypassing direct Schanuel.
2. **The missing F₁ Frobenius (open since §U/§V) IS the Stokes automorphism** of the archimedean irregular connection (Sabbah wild-Hodge). Constraint-determined (read off resurgence), not flow-propagated — the exact "constraint not flow" F₁. Resolves §V's "the infinite lift must exist — what is it?".
3. **Self-correction (computed):** the **Γ-factor's** Stirling Stokes data are **Tate** (Borel poles at `2πik`, residues `1/(2πik)` = powers of `2πi`; the `a_∞=½log2π=−ζ'(0)` floor) — *not* the obstruction. The genuine wild kernel is the **`γ_E`/digamma connection** (`e^{-x}\log x`). Retarget the freeness test there.

## Status/door note
No NATIVE/C5 count change. This sharpens the **D4 (`ω`) apex** on the transcendence axis: the open core is now "**is the digamma/wild kernel `K` free**" (Stokes-decidable) rather than abstract Schanuel; and `ω` is explicitly two faces (DSS `ω_mot` / RH `ω_pol`). Cross-links: `corank-seam-invariant` (`K` free = `corank^{(T)}=∞ ∀T`), memory `exponential-period-dss-cross` (the `K`, exponential corank), `phase-cancellation-crux` (`ω_pol`).

## Net
+1 in-progress card (the ω-split + 2 moonshots + self-correction); **resolves a latent RH/DSS conflation** in compute-omega; relocates the DSS apex to wild-kernel freeness (Stokes-decidable), ahead of the Schanuel framing.
