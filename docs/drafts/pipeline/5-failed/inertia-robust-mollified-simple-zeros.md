# Inertia-robust mollified simple zeros (beyond 2/3 unconditionally)

- **ID:** inertia-mollified-simple-zeros
- **Stage:** 0-backlog
- **Type:** FALSIFIED (the improvement mechanism and its near-line refinement); closed
- **Source:** HF signature form (HF-F7, HF-F15); route 1 principle "integer bounded by a trace budget" (R1-L10); Alpöge–Furman arXiv 2608.13637; Conrey–Ghosh–Gonek (1998), 19/27 simple zeros under RH
- **Statement:** Make the Conrey–Ghosh–Gonek mollified Cauchy–Schwarz argument unconditional using Sylvester inertia on the off-line `(1,1)` blocks, and so prove `N*_simple(T,2T) ≥ (c − o(1))N(T,2T)` with some `c > 2/3` unconditionally.

## Why it is plausible
- CGG need RH only to read the holomorphic sum `Σ_ρ ζ'(ρ)M(ρ)ζ'(1−ρ)M(1−ρ)` as `Σ|ζ'(ρ)M(ρ)|²`.
- Unconditionally, off-line pairs `{ρ, 1−ρ̄}` enter that sum as `2Re(a_ρ conj a_{ρ'})`: Hermitian `(1,1)` blocks, exactly Alpöge–Furman's structure.
- Alpöge–Furman removed RH from Montgomery's argument (2/3) this way. The mollifier analogue is not in their paper, which says "No mollifier … is used".

## Obstacles (Phase 4)
1. **Normalization.** A-F need `‖v_ρ‖ ≤ 1` per zero, to get `tr P ≤ N₀`. Mollified weights `ζ'(ρ)M(ρ)` are unbounded per zero.
2. **Direction of inertia.**
   - The CS denominator needs `Σ_{on}|a|² ≤` a computable quantity. That uses `n₋(Q) ≤ #pairs`: `P ⪯ G + Q₋` with `rank Q₋ ≤ b`, so `P ⪯ G` on `ker Q₋`, which has codimension at most `b`.
   - A-F's rank-trace lemma uses `n₊`. A single CS functional has rank one and can be killed by a codimension-`b` restriction, so a Gabor-localized family of mollified functionals is needed.
3. **Analytic input.** The HS norm of the mollified Gabor Gram matrix is a mollified pair correlation, `Σ_{ρ,ρ'} ζ'M(ρ)ζ'M(1−ρ)ζ'M(ρ')ζ'M(1−ρ') K(γ−γ')`. I don't know it to be computed anywhere; it is the hard input.

## Plan
1. Formulate and prove the matrix lemma: an inertia-robust multi-functional Cauchy–Schwarz / rank inequality using `n₋(Q) ≤ b`, the codimension counting, and a numerator family of rank `≫ b`. Formalize in Lean (finite-dimensional).
2. Identify the unconditional analytic inputs: the localized first and second holomorphic moments (CGG-type contour integrals), and the mollified Gabor pair correlation (restricted support).
3. Solve the resulting LP / optimization over the mollifier and window; check whether `c > 2/3`.

## Phase 4 verdict (2026-09-26): FALSE as stated
- **Robust CGG lemma [paper, easy].** Let `Π` project orthogonally to the at most `2p` localized off-line vectors. Then `ΠGΠ = ΠPΠ` and `Πs = Πs_on`. Cauchy–Schwarz on the on-line part gives `s₁ ≥ c(N − 2p)` with `c = 19/27` (CGG ratio, unconditional holomorphic moments), counting only the on-line zeros left after removal.
- **LP with Alpöge–Furman.**
  - Their constraints are `3s₁ + 4(s₂+p) ≥ (4−R)N` and `s₁ + 2(s₂+p) ≤ N`. The minimum `s₁ = 2N/3` is attained on the family `s₂ + p = N/6`.
  - Robust CGG excludes the multiplicity end (`p = 0` forces `s₁ ≥ 0.70N`).
  - It does not exclude the off-line end: `s₁ = 2N/3` is feasible once `p ≥ ((1 − 2/(3c))/2)N ≈ 0.026N`.
  - So the constant 2/3 does not move.
- **Why.** Removing each off-line pair costs two zeros of effective sample, so the CGG constraint is `c(N−2p)`. At the A-F extremal (`p ≈ N/6`) this gives only `c·(2/3)N ≈ 0.47N`.
- **Survivor (conditional, [paper]).** An unconditional bound `p ≤ 0.026N` on off-line pairs within `O(1/log T)` of the line, which is what can be numerous, would give more than 2/3 simple on-line zeros via A-F plus robust CGG. Selberg-type density does not reach this scale (Levinson only gives ≥ 41% exactly on the line).
- **Refined conjecture (next loop).** Near-line pairs look on-line in both Gram structures.
  - For a pair with offset `δ ≪ 1/log T`, `v_ρ ≈ v_{1−ρ̄}`. The A-F block `2(aaᵀ − bbᵀ)` is then rank-one PSD up to `O((δL)²)`, and the CGG pair term `2Re(a_ρ conj a_{ρ'}) = |a_ρ|² + |a_{ρ'}|² − |a_ρ − a_{ρ'}|²` is a sum of squares up to `O(δ log T)`.
  - So pairs with `δ log T < λ₀` behave like two on-line zeros. For the statement "simple zeros", on or off the line, they count correctly.
  - Only pairs with `δ log T ≥ λ₀` need the projection (cost 2 each). Selberg's density theorem gives at most `C e^{−λ₀/4} N` of them.
  - Target: unconditionally, `N_simple ≥ (19/27)(1 − 2Ce^{−λ₀/4})N − O(err(λ₀))`. This beats 2/3 if the explicit density constant `C` and the near-pair error cooperate.
  - Inputs to check: explicit Selberg-density constants at scale `λ/log T`; whether CGG's holomorphic second moment is unconditional (Gonek-type contour lemma); the near-pair error bound.
- **Matrix tool [paper].** A codimension-robust rank bound: if `G = P + Q`, `P ⪰ 0` with `rank ≤ r`, and `range Q ⊆ E` with `dim E ≤ k`, then `r ≥ (tr G − Σ_{i≤k} λ_i(G))²/‖G‖²_HS`. Proof: compress to `E^⊥`, then Ky Fan and Cauchy–Schwarz on eigenvalues.

## Refinement verdict (2026-09-26): FALSE quantitatively (the needed input is stronger than the target)
- **Explicit Selberg density** (Simonič arXiv 1910.08274, Thm 1 and eq. (5)): `N(σ,2T) − N(σ,T) ≤ 5.357 T^{1−(σ−½)/4} log T` for `T ≥ 10^50`; the method floor is 3.259. At `σ = ½ + λ/log T` this is `≲ 33.7 e^{−λ/4} N(T,2T)`.
- **The gap.** Far pairs `≤ 0.026N` needs `λ₀ ≥ 28.7`. The near-pair PSD approximation needs `δ log T ≪ 1`, i.e. `λ₀ ≪ 1`. The gap is a factor of about `e^7`.
- **Circularity.** The input the LP needs ("≤ 0.026N off-line pairs near the line", i.e. ≈ 95% of zeros on the line) is stronger than the target (≈ 70% simple) and far beyond SOTA (≈ 41% on the line).
- **SOTA update.** Lamzouri, arXiv 2609.02882 (Sept 2026), gives a Hilbert-space version of Alpöge–Furman: 67.25% simple and on the line, 88.76% simple or on the line, 83.62% distinct. No mollifiers.
- **Status.** NO POSITIVE SALVAGE beyond the two paper tools (the robust CGG lemma and the codimension-robust rank bound).

## Relation to RH
A proportion result: it does not decide RH (individual-zeros gate). It is the strongest frontier-moving candidate found in the route-1 / HF loops.

## Log
- 2026-09-26 — refinement FALSE quantitatively (Simonič constants; the needed input is ≈ 95% of zeros on the line); project closed.
- 2026-09-26 — Phase 4: FALSE as an improvement mechanism. A-F's off-line extremal survives robust CGG; the improvement needs near-line pair density `p ≤ 0.026N`.
- 2026-09-26 — created from R1-L10 / HF L9: the second-moment rank-trace is saturated, so mollified weights are the next input.
