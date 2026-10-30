# Growing-conductor character tents share one decay rate

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For every `A≥0`, there exist `κ>0`, `C≥0`, `X₀≥3` such that, simultaneously for all `X≥X₀`, `q≤(log X)^A` and nonprincipal characters `χ mod q`,

`|Σ_n χ(n)Λ(n) max(log(X/n),0)| ≤ CX exp(−κ(log X)^(1/10))`.

## Proof

[PROVED HERE] Set `u=(log X)^(1/10)`, `ε=1/(10A+1)` and `R=10A+3`. Take the constants `a,B₀` of the [actual uniform Perron bound](../3-formalized/actual-character-contours-have-uniform-conductor-cost.md), with `a≤1/8`. Put `c=a/R²`, `D=1+c`, `T=exp(Du)−3`, `δ=c/(Du)^9`, `k=c/D^9` and `B=B₀R³`.

For `u≥6`, `q≤u^(10A)` gives `q^ε≤u` and `log q≤10A·u`. Since `1≤D≤2`, `log(T+5)≤3u`, hence `L=log(q(T+5))≤Ru`. Thus

`δ q^ε L² ≤ [c/u³]u(Ru)²=a`,

so the chosen width lies in the actual zero-free rectangle. Also `B₀q^εL³≤B(Du)^9`. The contour estimate therefore has the same three terms as the fixed-character bound, now with constants independent of `q,χ`.

The displacement is `δ log X=ku`; `T≥exp(Du)/2`. Consequently the two tails cost at most `C_t u^18 X exp(−(D−k)u)`, the left edge at most `C_v u^9 X exp(−ku)`, and both horizontal edges at most `C_h X exp(−(2D−k)u)`. Since `k≤c`, both `D−k` and `2D−k` are at least `1`. With `d=min(1,k)>0`, all terms are at most a fixed multiple of `u^18 X exp(−du)`. The proved polynomial-exponential absorption inequality bounds this by `CX exp(−du/2)`. Choose `κ=d/2` and `X₀=max(3,exp(6^10))`.

## Formalization and scope

Lean: `GaloisForLFunctions/RHTower/ConductorUniform/DirichletCharacterUniformPowerLog.lean`.

- `RHTower.exists_conductor_uniform_character_tent_power_log`.
- Direct Lean check passed; transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.

The common horizon precedes the quantifiers over modulus and character. The estimate concerns the actual signed tent sum, including prime powers.
