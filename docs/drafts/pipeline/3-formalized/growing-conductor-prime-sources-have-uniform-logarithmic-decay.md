# Growing-conductor prime sources have uniform logarithmic decay

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For every `A≥0` and integer `k≥0`, all sufficiently large `Y` satisfy, simultaneously for every `X≥Y`, every modulus `q≤(log Y)^A` and every signed residue pattern `F`,

`|Σ_(n≤X) F(n mod q)Λ(n) − κ_q(F)X| ≤ [X/(log Y)^k]Σ_r|F(r)|`,

where `κ_q(F)=φ(q)^(-1)Σ_(r unit)F(r)`. One starting horizon precedes all quantifiers over modulus, pattern and larger endpoint.

## Proof

[PROVED HERE] The [uniform logarithmic-derivative bound](../3-formalized/dirichlet-logarithmic-derivatives-have-uniform-conductor-cost.md), [complete actual Perron contour estimate](../3-formalized/actual-character-contours-have-uniform-conductor-cost.md), [common tent decay](../3-formalized/growing-conductor-character-tents-share-one-decay-rate.md), and [signed unsmoothing and finite-character recovery](../3-formalized/growing-conductor-character-sums-retain-signed-unsmoothing.md) give constants `a>0,C≥0,Z≥3` such that every reduced residue class of every `q≤(log X)^A` has prime error at most `CX exp(−a(log X)^(1/10))` for `X≥Z`.

A prime in a nonunit residue class divides `q`. The whole contribution is therefore at most `θ(q)`, which has a common bound `DX exp(−a(log X)^(1/10))` on the same growing family beyond one further horizon. Every residue's proper prime powers are bounded by the scalar mass `ψ(X)−θ(X)≤2√X log X`, absorbed by the same physical error. Thus all residue indicators, including nonunits, share one actual Mangoldt rate.

Choose `Y` beyond these common horizons with `C'(log Y)^k exp(−a(log Y)^(1/10))≤1`. For `X≥Y`, both the allowed modulus range and the logarithmic decay are monotone, so every residue indicator has error at most `X/(log Y)^k`. The identities

`F(n mod q)=Σ_r F(r)1_(n mod q=r)` and `κ_q(F)=Σ_r F(r)κ_q(1_r)`

then give the stated signed-pattern bound by the finite triangle inequality. Prime powers, principal characters and nonunit residue classes are all retained.

## Formalization and scope

Lean: `GaloisForLFunctions/CriticalArithmeticCorrelationTheory/GrowingConductorPrimeSourcesHaveUniformLogarithmicDecay.lean`.

Declarations in `GaloisForLFunctions.CriticalArithmeticCorrelationTheory`:

- `exists_conductor_uniform_residueMangoldtReading_indicator_power_log`.
- `eventually_conductor_uniform_residueMangoldtReading_log_error`.
- Direct Lean check passed; transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.

All analytic inputs are proved for the actual Dirichlet functions and sums. The weighted complete-Weil residual estimate, negative-eigenvector confinement and physical separated-bump loss remain open.
