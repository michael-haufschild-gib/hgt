# Arithmetic measure rigidity of resonant states

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0211/obstacles-summary.md`, §2.4 (read-only).
- **Goal:** Find an arithmetic rigidity mechanism selecting `Re ρ = 1/2` from resonant states, without assuming positivity or a zero-location estimate.

## Established boundary

The corpus proves exact truncated norms, partner angles, first two Hecke moments and a Cauchy spectral kernel (`EisensteinResonantStateNorm`, `EisensteinResonantPartnerAngle`, `EisensteinHeckeSecondMoment`, `EisensteinResonantSpectralKernel`). The Hecke variance already equals `2(1-p^{Re ρ-1})`; deriving it again adds no mathematics.

Petridis–Raulf–Risager, *Quantum Limits of Eisenstein Series and Scattering States*, Theorem 1.1, identifies local scattering-state limits as `E(z,2-β)dμ` along the sequences covered there. This is a family retaining β, not a theorem selecting β. Source: <https://arxiv.org/abs/1111.6615>. No analytic statement from this paper is assumed in Lean.

## Cutoff model: paper derivation, Lean verification pending

Write `τ_(u,Y)=Λ^Y E_u`, `B(u)=Λ(2u)`, with `Λ(1+2u)=0`, `Re u<0`, `Im u>0`.

For `Y≤Z`, `τ_(v,Z)-τ_(v,Y)` is the constant Fourier mode on `(Y,Z]`. The other truncated state has zero constant mode there. Hence mixed-height pairings equal their value at `min(Y,Z)`. Maass–Selberg then gives, for distinct parameters as well as equal ones,

`〈τ_(u,Y),τ_(v,Z)〉 = -B(u)conj(B(v)) min(Y,Z)^(-u-conj(v))/(u+conj(v))`.

This is exactly the Gram kernel of the elementary functions
`1_(0,Y](y) B(u)y^(-u-1/2)` in `L²(dy)`. These functions exist for every `Re u<0`, with no zero condition. Thus the complete cutoff Gram data have a positive realization throughout that half-plane.

The single Weyl term also gives
`T_p τ_(u,Y)=p^u τ_(u,pY)+p^(-u)τ_(u,Y/p)`.
For `F_(u,Y)=Y^u τ_(u,Y)`, this becomes `T_p F_(u,Y)=F_(u,pY)+F_(u,Y/p)`.
At equal parameter, normalized pairings in logarithmic height have kernel
`exp(-a|x-y|+it(x-y))`, `u=-a+it`. All finite Hecke words therefore read one common height-translation representation, rather than independent prime directions, when all intermediate cutoffs stay at least one.

## Next conjecture: the compact-core return

The Gram proof requires cutoffs at least one: above that height the fundamental domain contains complete horocycles. A Hecke word whose shifted cutoffs remain at least one is therefore represented by elementary cusp powers. Crossing below one encounters incomplete horocycles and modular identifications. The coordinate formula for `heckeTruncated` must not be confused with a proof of automorphic truncation at these smaller heights.

Determine the exact compact-core return correction for genuine automorphic truncation, then test whether its repeated returns enforce a restriction on the decay rate. This is the first place where spatial localization can distinguish the modular surface from the elementary cutoff model. No such restriction has been established.

**First-prime candidate.** At cutoff one, write `z=x+iy∈fd` and
`h_k(z)=2y/((x+k)²+y²)`. The missing automorphic cusp subtraction in the two downward branches of `T₂` should be
`B(u)/√2 · Σ_(k=-1,0,1) 1_(h_k>1) h_k^(1/2-u)`.
These return regions are the disks `(x+k)²+(y-1)²<1`. To verify: classify primitive rows in the two Hecke images, prove that rows with `|c|≥2` cannot return above height one, account for the `±` row multiplicity, and compare the resulting operator with genuine automorphic truncation. The correction is subtracted from the coordinate Hecke formula. This remains a conjectured source identity, not an assumed input.

## Open dependency

No microlocal limit, Hecke recurrence, entropy bound or classification selecting β has been proved. The positive finite-measure hypotheses of standard entropy arguments cannot be silently transferred to non-square-integrable resonant states.
