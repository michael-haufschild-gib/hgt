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

**Compact-core source limit: formalized.** For resonances `u_n=a_n+it_n` with `a_n→a∈(-1/2,0)` and `t_n→∞`, the normalized squared full dyadic residual on the entire rectangle `R` converges weakly to
`(-2a)[2^(2a)y^(1−2a)+h_0^(1−2a)/2] dμ`.
The relative phase is analytic and nonconstant on each horizontal slice, so its pushforward is absolutely continuous even across `x=0`. Dephasing, varying-amplitude convergence, nonvanishing of `B(u)`, and actual Maass–Selberg normalization are checked in Lean. The limiting source is strictly positive for every negative rate, including the critical rate. [Exact statement and proof](../3-formalized/resonant-core-source-limit.md).

**Uniform cutoff gap: formalized.** For every `Y≥1`,
`||(T₂−λ₂)Λ^Y_aut E_u||² ≥ (-2 Re u)||Λ^Y E_u||²/1024`.
For `Y≥2`, the exact normalized mass is `2^(-2 Re u)−2^(2 Re u)`.
The three-return decomposition and global integrability are also checked.
[Statement, proof and audit](../3-formalized/resonant-uniform-cutoff-hecke-gap.md).

**Finite cutoff packets: formalized.** Every finite complex packet `F=Σ c_j Λ_aut^(Y_j) E_u`, with `Y_j≥2`, satisfies
`||(T₂−λ₂)F||² ≥ (2^(Re u)+2^(-Re u)−2)² ||F||²`.
The coefficient is positive at every negative rate, including the critical rate. An exact residual isometry retains all cross terms before applying the unitary-dilation factorization. [Proof and audit](../3-formalized/resonant-cutoff-packet-gap.md).

**Height law and cusp escape: formalized.** For `κ=-2 Re u`, the actual normalized height marginal is `ν_Y=Y^(-κ)ν_1+κY^(-κ)1_(1,Y](y)y^(κ-1)dy`. After rescaling height by `Y`, every bounded measurable test with `|f|≤M` has error at most `2MY^(-κ)` from the power-law probability `κt^(κ-1)dt` on `(0,1]`. Fixed-height mass is at most `(C/Y)^κ`; it vanishes as `Y→∞` uniformly in ordinate when `κ` stays positive away from zero. This positive limiting law retains the decay rate. [Proof and Lean certificates](../3-formalized/resonant-cusp-height-law.md).

## Open dependency

The source-side results in `MayerScattering/FareyLewisTransferAndCuspSeparation` distinguish two inputs. `eisensteinLewisPeriod_dyadicCuspEnergy_integrable_iff_resonance` characterizes resonance by finite dyadic cusp energy. The critical-line equivalence additionally requires zero co-isometry defect; no implication from finite cusp energy to that vanishing is proved. Three-term and modular-inversion invariance alone also hold for non-resonant Eisenstein periods. They cannot supply the missing classification.

`MayerWindowFoldTransfer` identifies the co-isometry defect with a logarithmic window-Frobenius defect and bounds it through symmetric and antisymmetric folds. Thus this particular defect is already connected to window geometry; introducing it again would not furnish an independent rigidity mechanism.

Congruence lifting preserves the obstruction: `CongruenceScattering.constantTerm_order` and `fullConstantTerm_pole_iff` retain the complete scattering pole divisor, including multiplicities, at every principal level and height. Changing level alone supplies no restriction on the decay rate.

`SelbergScatteringNativeResidual.xi_residual_isGLB` gives the sharp native Laplacian residual floor `|γ|(1−β)/2` at the scattering energy of `ρ=β+iγ`, with explicit packets approaching it. Under scaling by `γ⁻²`, this floor becomes `(1−β)/(2|γ|)` and tends to zero at large ordinate; it does not obstruct semiclassical transport at that scale. The dyadic Hecke residual studied here remains of order one. `SelbergScatteringCutoffForcing` also proves that the actual differential cutoff forcing is nonzero despite a vanishing bilinear pairing.

No microlocal limit, Hecke recurrence, entropy bound or classification selecting β has been proved. The positive finite-measure hypotheses of standard entropy arguments cannot be silently transferred to non-square-integrable resonant states.
