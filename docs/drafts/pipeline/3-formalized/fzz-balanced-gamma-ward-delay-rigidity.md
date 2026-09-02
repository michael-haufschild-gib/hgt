# FZZ balanced Gamma Ward-delay rigidity

- **ID:** FZZ-GAMMA-WARD-DELAY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus continuation of `fzzHJBalancedExternalGammaPhaseSlope_zero_le` and `fzzHJBalancedExternalGammaPhaseLift_eq_zero_iff_passive`
- **Statement:** At physical level `k=4`, balanced external-Gamma phase slope attains its vacuum value exactly at zero radial momentum; equivalently exactly when linear replica-area response is passive.

## Goal

Replace branch-dependent unwrapped-phase history by local, branch-independent logarithmic Ward delay. Proof chain:

`source Ward dynamics forces vacuum-delay saturation on every parity-Mellin divisor`
`→ P=0 → divisor-mode replica-area passivity → Mellin completeness → RH`.

This card proves only strict delay rigidity; source-dynamical saturation remains open.

## Gates

- [x] 0 → 1 in-progress: exact corpus objects, source-facing chain, strict Gauss-tail attack
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axioms audited
- [ ] 3 → 4 publication-ready: standalone paper and external novelty audit

## Approach

Existing corpus proves the first two Gauss-digamma increments cancel both rational arctangent slope losses. Retain the `n=2` Gauss atom: its residual is

`8 y² / (5 (25 + 4 y²))`,

strictly positive for `y ≠ 0`. Nonnegativity of every later atom then gives strict global slope minimality. Scale by `y = sqrt(2) P` and weld to the exact replica-area passivity criterion.

## Proof

**[PROVED HERE]** Write the slope difference as sum of Gauss-digamma atom differences plus two rational-shift losses. Every atom difference is nonnegative. The `n=0,1` partial sum equals the negative of the two rational losses. The next atom contributes exactly

`8 y² / (5 (25 + 4 y²))`.

Hence the slope at `y` strictly exceeds its value at `0` whenever `y ≠ 0`, and equality holds exactly at `y=0`. Since `sqrt(2)>0`, the momentum Ward delay `4 sqrt(2) slope(sqrt(2)P)` equals its vacuum value exactly at `P=0`. Existing corpus identifies `P=0` with linear replica-area passivity. Quantifying this equality over parity-Mellin divisor modes is therefore equivalent to `FZZLinearReplicaAreaDivisorPassive`, hence to RH.

## Novelty audit

- Internal corpus: only non-strict slope minimality and global unwrapped-phase order rigidity existed; no strict slope equality classification or local Ward-delay RH endpoint was found.
- External literature through 2026-09-02: Halder--Jafferis gives the exact external Gamma factors; cigar-reflection literature studies exact/semi-classical reflection amplitudes. No strict global minimum theorem for this balanced local phase delay, nor its replica-area/RH classification, was found.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBalancedGammaWardDelayRigidity`
- Main theorem: `fzzBalancedExternalGammaWardDelayDivisorSaturated_iff_riemannHypothesis`
- Direct `lake env lean`: PASS
- Targeted `lake build`: `13153/13153` PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`

## Log

- 2026-09-02 — Corpus-backed conjecture frozen; paper/Lean attack started.
