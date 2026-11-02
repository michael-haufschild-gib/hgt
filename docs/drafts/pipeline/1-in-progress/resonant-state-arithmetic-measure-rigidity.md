# Arithmetic measure rigidity of resonant states

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0211/obstacles-summary.md`, §2.4 (read-only).
- **Goal:** Find an arithmetic rigidity mechanism selecting `Re ρ = 1/2` from resonant states, without assuming positivity or a zero-location estimate.

## Established boundary

The corpus proves exact truncated norms, partner angles, first two Hecke moments and a Cauchy spectral kernel (`EisensteinResonantStateNorm`, `EisensteinResonantPartnerAngle`, `EisensteinHeckeSecondMoment`, `EisensteinResonantSpectralKernel`). The Hecke variance already equals `2(1-p^{Re ρ-1})`; deriving it again adds no mathematics.

Petridis–Raulf–Risager, *Quantum Limits of Eisenstein Series and Scattering States*, Theorem 1.1, identifies local scattering-state limits as `E(z,2-β)dμ` along the sequences covered there. This is a family retaining β, not a theorem selecting β. Source: <https://arxiv.org/abs/1111.6615>. No analytic statement from this paper is assumed in Lean.

## Current conjectures

1. At a resonance, the exact Hecke action on truncations is a sum of two shifts in cutoff height:
   `T_p τ_Y = p^u τ_(pY) + p^(-u) τ_(Y/p)`, `u=ρ/2-1/2`.
2. The Gram kernel of truncations at different heights is their smaller-height squared norm. Normalizing and using logarithmic height gives `exp(-a|x-y|)`, `a=(1-Re ρ)/2`.
3. These identities determine the joint Hecke correlations and isolate which information survives beyond the universal cusp profile. Rigidity must constrain that remaining information, rather than require vanishing truncation error.

## Open dependency

No microlocal limit, Hecke recurrence, entropy bound or classification selecting β has been proved. The positive finite-measure hypotheses of standard entropy arguments cannot be silently transferred to non-square-integrable resonant states.
