# Growing-conductor prime sources have uniform logarithmic decay

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** For every `A≥0` and integer `k≥0`, all sufficiently large `Y` satisfy, simultaneously for every `X≥Y`, every modulus `q≤(log Y)^A` and every signed residue pattern `F`,

`|Σ_(n≤X) F(n mod q)Λ(n) − κ_q(F)X| ≤ [X/(log Y)^k]Σ_r|F(r)|`,

where `κ_q(F)=φ(q)^(-1)Σ_(r unit)F(r)`. One starting horizon precedes all quantifiers over modulus, pattern and larger endpoint.

## Proof

[PROVED HERE] The [uniform logarithmic-derivative bound](../3-formalized/dirichlet-logarithmic-derivatives-have-uniform-conductor-cost.md), [complete actual Perron contour estimate](../3-formalized/actual-character-contours-have-uniform-conductor-cost.md), [common tent decay](growing-conductor-character-tents-share-one-decay-rate.md), and [signed unsmoothing and finite-character recovery](growing-conductor-character-sums-retain-signed-unsmoothing.md) give constants `a>0,C≥0,Z≥3` such that every reduced residue class of every `q≤(log X)^A` has prime error at most `CX exp(−a(log X)^(1/10))` for `X≥Z`.

A prime in a nonunit residue class divides `q`. The whole contribution is therefore at most `θ(q)`, which has a common bound `DX exp(−a(log X)^(1/10))` on the same growing family beyond one further horizon. Every residue's proper prime powers are bounded by the scalar mass `ψ(X)−θ(X)≤2√X log X`, absorbed by the same physical error. Thus all residue indicators, including nonunits, share one actual Mangoldt rate.

Choose `Y` beyond these common horizons with `C'(log Y)^k exp(−a(log Y)^(1/10))≤1`. For `X≥Y`, both the allowed modulus range and the logarithmic decay are monotone, so every residue indicator has error at most `X/(log Y)^k`. The identities

`F(n mod q)=Σ_r F(r)1_(n mod q=r)` and `κ_q(F)=Σ_r F(r)κ_q(1_r)`

then give the stated signed-pattern bound by the finite triangle inequality. Prime powers, principal characters and nonunit residue classes are all retained.

## Formalization and scope

Lean: `GaloisForLFunctions/CriticalArithmeticCorrelationTheory/GrowingConductorPrimeSourcesHaveUniformLogarithmicDecay.lean`; audit pending. All analytic producers are actual Dirichlet functions and sums, with no prime-distribution input assumed. Abel transport to the residue-Mertens finite part remains to formalize. The complete-Weil weighted residual sum, effective negative-eigenvector confinement and physical separated-bump loss remain open.
