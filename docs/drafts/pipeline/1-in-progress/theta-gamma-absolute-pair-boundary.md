# Gamma normalization and the absolute-pair boundary

- **Stage:** 1-in-progress.
- **Question:** Does Gamma normalization permit a summable absolute majorant over all ordinary pairs?
- **Corpus inputs:** `WeilWorkDeficitMellin.scaled_mellin`, `BlackHoleRingdown.norm_modifiedBesselKOrder_sharp_of_nonneg`, `StretchedBose.norm_Gamma_ge`, `thetaPairCenterTailSpectrum_eq`.

For fixed `q>0`, conjecture

`B_q(2τ)/|Γ(9/4+iτ)|² → 1` as `τ→∞`.

The complete Mellin mass gives `T_p(τ,0)=|Γ((p+1)/2+iτ)|²/4`. The sharp contour bound with imaginary order and `B=1` gives

`|K_(2iτ)(2u)| ≤ eπ(1+2τ)u⁻¹ exp(−πτ)`.

The resulting candidate error bound is

`|B_q(2τ)−[|Γ(9/4+iτ)|²−(3/2)|Γ(5/4+iτ)|²]|`
`≤ eπ[(8/7)q^(7/2)+10q^(3/2)](1+2τ)exp(−πτ)`.

The corpus Gamma lower bound at real part `1/4`, followed by two recurrences, gives
`|Γ(9/4+iτ)|² ≥ [Γ(1/4)²/25]τ²exp(−πτ)` for `τ≥1`.
Thus the normalized error would decay at least as `O_q(1/τ)`. These estimates are drafted in `BesselSharpPrefix.lean` and `GammaQuarterFloor.lean`; neither has passed its Lean audit. The density error and normalized limit still require formalization.

If proved, every fixed ordered-pair amplitude has normalized limit `4/(sqrt(πnm))`. Even the diagonal limits form a divergent harmonic series. Therefore no summable absolute majorant over all pairs can be uniform in frequency on this Gamma scale.

Positive survivor to audit: every finite pair head has leading normalized form

`(4/sqrt π)|Σ_(n≤M) n^(-1/2) exp(ib log n)|²`,

with an explicit error tending to zero for each `M`. This factorization preserves aggregate phase cancellation. It does not justify interchanging the infinite pair sum or the unbounded center integral with the high-frequency limit. Those failures distinguish an actual aggregate payment from termwise domination.
