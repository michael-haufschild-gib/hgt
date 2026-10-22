# MSC physical-overlap diagonal-rigging classification

- **ID:** MSC-DIAG
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` route MSC; physical regular-germ and Hilbert-wall chain
- **Statement:** For every `σ>1`, reciprocal positive diagonal Hilbert rigging simultaneously admits physical MSC column at `ρ` and literal Möbius overlap covector iff `Re ρ>1`.

## Goal

Kill all coefficient-faithful diagonal Hilbert/Gelfand completions of physical MSC denominator at every strict-right Xi zero, not only fixed-power riggings.

## Gates

- [x] 0 → 1  in-progress: source-pure MSC overlap pairing; exact route consumer identified
- [x] 1 → 2  fully-proven: complete proof below; no open dependency
- [x] 2 → 3  formalized: `admitsMSCPhysicalOverlapDiagonalRigging_iff`; targeted build and axiom audit pass
- [ ] 3 → 4  publication-ready

## Proof

Let `c_n(ρ,σ)` be physical complex-damped Möbius column and `b_n(σ)` base Möbius overlap covector. Existing coefficient identities give

`|c_n(ρ,σ)| |b_n(σ)| = μ²(n)n^{-Re ρ}/Z_sq(σ)`.

Thus source–covector product density is independent of aperture `σ`, apart from positive scalar `Z_sq(σ)⁻¹`.

A positive reciprocal diagonal rigging `w_n` requires

`Σ w_n|c_n|² < ∞` and `Σ w_n⁻¹|b_n|² < ∞`.

Weighted AM–GM gives `2|c_n||b_n| ≤ w_n|c_n|²+w_n⁻¹|b_n|²`; hence `Σ|c_n||b_n|<∞`. Exact squarefree mass abscissa then forces `Re ρ>1`.

Conversely, if `Re ρ>1`, choose balanced weight

`w_n = exp((Re ρ-σ)log n)`.

Both weighted square densities equal `μ²(n)n^{-Re ρ}/Z_sq(σ)`, hence are summable. This proves iff.

For strict-right Xi zero, `1/2<Re ρ<1`; no such rigging exists. Existing residue split supplies physical MSC regular germ and limit `2` (energy `4`), so obstruction applies to actual RH route chain.

## No-go closure

- **Exact killing mechanism:** reciprocal reweighting cannot change coefficientwise source–covector product; its squarefree Dirichlet abscissa is `Re ρ=1`.
- **Strongest positive survivor:** exact invariant and canonical balanced weight above; non-diagonal or genuinely distributional completion only.
- **New insight:** physical MSC overlap wall is absolute-convergence wall, independent of Hilbert aperture and weight choice.
- **Novelty audit:** no matching theorem found through 2026-08 in Hedenmalm [arXiv:2606.17494](https://arxiv.org/abs/2606.17494), weighted Dirichlet-space RH work [arXiv:2206.02654](https://arxiv.org/abs/2206.02654), Meyer nuclear-Fréchet spectral model [math/0412277](https://arxiv.org/abs/math/0412277), or corpus search.
- **Formal status:** `RHTower/Hedenmalm/HedenmalmGammaSewnSquarefreeFisherDiagonalRiggingNoGo.lean`; targeted build passes; axioms only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-09-01 — dependency-closed proof formalized; Stage 3.
