# Gauge-fixed total `++-` Teukolsky cokernel Schur section

- **ID:** hawking-total-ppminus-cokernel-schur
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `ThetaCuspHawkingAIMEThirdOrderSourceCohomology.lean` · `ThetaCuspHawkingAIMEThirdOrderFieldRedefinition.lean`
- **Statement:** For the augmented gauge-fixed Einstein--Teukolsky boundary operator, the total resonant `++-` coefficient is the left-cokernel pairing of its cubic retarded Schur complement; lower-order horizon/flux data cannot determine it without the third jet.

## Goal
Replace coordinate-dependent AIME, cascade, and direct-channel coefficients by one on-shell boundary-value section. Derive the section from the retarded second-order boundary solver and identify the exact remaining nonlinear horizon datum.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: exact Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper with proof and Lean certificate

## Approach
Treat horizon and outer radiation conditions as components of one augmented nonlinear map `F`. Write its Taylor data as `(L,B,C)`. If `p,m` are linear branches and `R₊₊,R₊₋` are complete causal quadratic response maps satisfying `Lγ(Rγ q)+q=0`, then

`u₊₊ = R₊₊(B(p,p)/2)`, `u₊₋ = R₊₋((B(p,m)+B(m,p))/2)`.

The exact total source is

`S₊₊₋ = B(p,u₊₋)+B(m,u₊₊)+(C(p,p,m)+C(p,m,p)+C(m,p,p))/6`.

For symmetric Fréchet derivatives this becomes

`S₊₊₋ = B(p,R₊₋ B(p,m)) + B(m,R₊₊(B(p,p)/2)) + C(p,p,m)/2`.

The total cokernel section is `Σ₊₊₋ = ell(S₊₊₋)`. Since `F` contains bulk and both boundary residuals, `R₊₋` includes stationary horizon-charge closure and `R₊₊` includes full discrete-plus-continuum causal propagation. No separate boundary lift or named diagram remains.

**[PROVED HERE]** Taylor expansion gives the two quadratic equations coefficientwise. Their declared causal solution property gives the displayed responses. The `x²y` coefficient of `F` is exactly the displayed source; applying the augmented left state gives `Σ`. A residual boundary-preserving gauge change or quadratic field redefinition changes the total source by `Lξ`, so `ell L=0` proves invariance. Conversely, replacing `C(p,p,m)/2` by an arbitrary target-grade correction `w` changes `Σ` by `ell(w)` while preserving `L`, `B`, both quadratic response maps, and every lower-order flux law. If `ell(w₀)=1`, scaling `w₀` realizes any desired scalar section. Hence the third jet is indispensable.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Lower-order horizon dynamics does not fix `C`; adding a target-grade third-jet correction changes the section without changing any linear or quadratic datum.
- **Strongest positive survivor:** The augmented retarded cubic Schur section is the unique total on-shell object determined by the three-jet and complete causal quadratic response.
- **New insight:** “Direct”, AIME, exchange, prompt, discrete, and continuum pieces are presentations of one Schur section. RH incidence can only be asked of their total. The first missing physical input is now the actual gauge-fixed Einstein boundary three-jet, not another positivity law.
- **Status:** `[BRIDGE] [PAPER-PROVED]`. Generic Schur/effective-vertex mechanism is established mathematics; exact augmented `++-` specialization is absent from audited corpus and black-hole literature. Lean formalization pending.

## Log
- 2026-08-25 — Created directly in Stage 1. Existing corpus proves total-source coordinate invariance but does not construct the augmented retarded Schur section.
- 2026-08-25 — Horizon-flux-only determination falsified. Stronger three-jet Schur theorem paper-proved and promoted to Stage 2.
