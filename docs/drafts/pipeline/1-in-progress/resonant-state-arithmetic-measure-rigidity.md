# Arithmetic measure rigidity of resonant states

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0211/obstacles-summary.md`, §2.4 (read-only).
- **Goal:** Find an arithmetic rigidity mechanism selecting `Re ρ = 1/2` from resonant states, without assuming positivity or a zero-location estimate.

## Established boundary

The corpus proves exact truncated norms, partner angles, first two Hecke moments and a Cauchy spectral kernel (`EisensteinResonantStateNorm`, `EisensteinResonantPartnerAngle`, `EisensteinHeckeSecondMoment`, `EisensteinResonantSpectralKernel`). The Hecke variance already equals `2(1-p^{Re ρ-1})`; deriving it again adds no mathematics.

Petridis–Raulf–Risager, *Quantum Limits of Eisenstein Series and Scattering States*, Theorem 1.1, identifies local scattering-state limits as `E(z,2-β)dμ` along the sequences covered there. This is a family retaining β, not a theorem selecting β. Source: <https://arxiv.org/abs/1111.6615>. No analytic statement from this paper is assumed in Lean.

## Cutoff model: formalized

Exact declarations, proof and audit: [the joint cusp model](../3-formalized/resonant-cutoff-cusp-model.md).

Write `τ_(u,Y)=Λ^Y E_u`, `B(u)=Λ(2u)`, with `Λ(1+2u)=0`, `-1/2<Re u<0`, `Im u>0`, and cutoffs at least one.

For `Y≤Z`, `τ_(v,Z)-τ_(v,Y)` is the constant Fourier mode on `(Y,Z]`. The other truncated state has zero constant mode there. Hence mixed-height pairings equal their value at `min(Y,Z)`. Maass–Selberg then gives, for distinct parameters as well as equal ones,

`〈τ_(u,Y),τ_(v,Z)〉 = -B(u)conj(B(v)) min(Y,Z)^(-u-conj(v))/(u+conj(v))`.

This is exactly the Gram kernel of the elementary functions
`1_(0,Y](y) B(u)y^(-u-1/2)` in `L²(dy)`. These functions exist for every `Re u<0`, with no zero condition. Thus the complete cutoff Gram data have a positive realization throughout that half-plane.

The single Weyl term also gives
`T_p τ_(u,Y)=p^u τ_(u,pY)+p^(-u)τ_(u,Y/p)`.
For `F_(u,Y)=Y^u τ_(u,Y)`, this becomes `T_p F_(u,Y)=F_(u,pY)+F_(u,Y/p)`.
The finite-combination isometry also holds for simultaneous transforms at arbitrary primes `p_i` when `Y_i≥p_i`, including all mixed terms between primes and states.

## Compact-core return

The Gram proof requires cutoffs at least one: above that height the fundamental domain contains complete horocycles. The proposed extension to repeated Hecke words is the same cusp model whenever all shifted cutoffs remain at least one; this still needs a formal induction. Crossing below one encounters incomplete horocycles and modular identifications. The coordinate formula for `heckeTruncated` must not be confused with a proof of automorphic truncation at these smaller heights.

The compact-core return distinguishes the modular surface from the elementary cutoff model. Its exact source term must be retained before attempting a limiting recurrence equation. No restriction selecting the decay rate has been established.

**First-prime return: formalized.** Write `h_k(z)=2y/((x+k)²+y²)`. The globally automorphic truncation at height one differs from coordinate Hecke truncation by the subtraction
`D_u(z)=B(u)/√2 · Σ_(k=-1,0,1) 1_(h_k>1) h_k^(1/2-u)`.
The return regions are exactly `(x+k)²+(y−1)²<1`. Primitive-row classification, signed multiplicities and modular invariance are checked in Lean.

On `R={|x|≤1/4, 7/4≤y≤15/8}`, only the central return survives. Lean proves
`∫_R |D_u|² dμ ≥ (−2 Re u)/128 · ||τ_(u,1)||²`.
The full automorphic residual also satisfies
`∫_R |(T₂−λ₂)Λ¹_aut E_u|² dμ ≥ (−2 Re u)/512 · ||τ_(u,1)||²`.
The proof compares moduli, so both bounds hold at every frequency, including `Re u=−1/4`. This rules out an `L²` Hecke-quasimode approximation for cutoff-one truncations at fixed negative rate. Exact identities, paper proof and Lean certificates: [automorphic dyadic return](../3-formalized/resonant-automorphic-dyadic-return.md).

**Next limit candidate.** Put `R'={1/8≤x≤1/4, 7/4≤y≤15/8}`. For resonances `u_n=a_n+it_n` with `a_n→a∈(-1/2,0)` and `t_n→∞`, the normalized squared full dyadic residual on `R'` should converge weakly to
`(-2a)[2^(2a)y^(1−2a)+h_0^(1−2a)/2] dμ`.
The sole oscillatory cross term has phase `t_n log(4/(x²+y²))`, whose `x` derivative stays away from zero on `R'`. Prove this limit directly from the actual source identity. It would identify a positive source term in the limiting Hecke equation; it would not establish invariance or entropy of the resonant-state measure itself.

## Open dependency

No microlocal limit, Hecke recurrence, entropy bound or classification selecting β has been proved. The positive finite-measure hypotheses of standard entropy arguments cannot be silently transferred to non-square-integrable resonant states.
