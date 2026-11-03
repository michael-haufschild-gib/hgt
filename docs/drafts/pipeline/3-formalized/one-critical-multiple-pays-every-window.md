# One critical multiple pays every window

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ1k; route obstacle B5.
- **Statement:** For every `p > 1`, there is `C(p) > 0`, independent of window length, such that every real compactly supported C² test `H` on `(-∞,0]` satisfies
  `Q(H) ≥ -C(p) ∫ exp(-pu) H(u)² du`.

This gives one positive range of critical multiples `K`, independent of aperture, for every bulk exponent `β > 0` (`p = β+1`). It does not assert positivity of `Q` itself or uniform finite-`N` convergence over growing windows.

## Proof [PROVED HERE]

Write `M_p = ∫ exp(-pu)H²`. For each `t ≥ 0`, conjugating by `exp(-pu/2)` and using `u+t ≤ 0` on the correlation support gives
`|∫ H(u)H(u+t)du| ≤ exp(-pt/2) M_p`.
Consequently the absolute prime debit is at most
`2 M_p Σ_{n≥2} Λ(n)n^{-(p+1)/2}`, a convergent series for `p > 1`.
The archimedean jump energy is nonnegative and its diagonal costs at most `|Ω(0)| M_p`.
Weighted Cauchy–Schwarz bounds the two pole moments by
`|∫ H exp(±u/2)|² ≤ M_p/(p±1)`.
The inequality `2ab ≥ -a²-b²` therefore bounds their pole contribution below by
`-(1/(p+1)+1/(p-1)) M_p`.

Thus one may take
`C(p) = |Ω(0)| + 2 Σ_{n≥2} Λ(n)n^{-(p+1)/2} + 1/(p+1) + 1/(p-1)`.
Every term is finite and nonnegative; the last two are positive. Combining the exact Weil decomposition with these bounds proves the statement.

For completeness, the correlation estimate follows pointwise from weighted Young:
`2|H(u)H(u+t)| ≤ exp(pt/2)H(u)² + exp(-pt/2)H(u+t)²`.
Where the product is nonzero, `u+t ≤ 0`; hence the right side is at most
`exp(-pt/2)[exp(-pu)H(u)² + exp(-p(u+t))H(u+t)²]`.
Where the product is zero the desired bound holds directly. Integration and translation invariance prove the estimate.

For the pole estimate write
`H(u)exp(±u/2) = [exp(-pu/2)H(u)] exp((p±1)u/2)`
on `u≤0`; the second factor has squared norm `1/(p±1)` there. The exact archimedean–prime–pole decomposition and convergence of the von Mangoldt Dirichlet series at `(p+1)/2>1` are existing corpus theorems.

For any profile with `β>0`, bulk constant `J>0`, and `κ>0`, take
`0<K<βJ/(κ C(β+1))`. Then
`κQ(H)+(βJ/K)M_{β+1}(H) ≥ (βJ/K-κC(β+1))M_{β+1}(H)>0`
for every nonzero test on every window. The same inequality applies to the real and imaginary parts of each finite complex linear combination. Thus every independent finite window family has a positive definite pencil at this single `K`; its established critical-curve limit gives eventual positivity of that family's complete Gram matrix.

## Existing boundary

`TheCountPaysTheSecondOrderBelowAUniformMultiple` uses `10+72exp(A/2)` and discards the aliasing weight except for its lower bound `1`. Corpus searches for weighted half-line Weil floors and aperture-independent critical multiples found no matching theorem. The proof retains the weight in the shift and pole estimates.

## Lean

- WTZ `TheAliasingWeightPaysEveryWindow`: `weilQuad_ge_neg_exponentialMass`, the complete weighted floor with explicit constant.
- AHD `OneCriticalMultiplePaysEveryWindow`: `exists_positive_multiple_for_all_windows`, the aperture-independent positive pencil range; `tilted_exists_positive_multiple_inheriting_all_windows`, eventual positivity for each fixed independent family, with all tilted-profile and bulk inputs discharged.
- Both source files pass `lake --old env lean`; main declarations depend only on `propext`, `Classical.choice`, `Quot.sound`. Both modules are wired into their umbrellas.

B5 is solved. Σ1k remains partial: the equality case is not settled, and no uniform starting index over growing families is asserted.

## Gates

- [x] Precise source-side statement and proof mechanism.
- [x] Complete paper proof; corpus novelty audit against the aperture-dependent bound.
- [x] Lean formalization, direct checks, dependency audit, umbrella integration.
