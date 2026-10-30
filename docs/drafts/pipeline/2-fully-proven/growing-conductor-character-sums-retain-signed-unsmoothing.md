# Growing-conductor character sums retain signed unsmoothing

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** For each `A≥0`, one rate `ρ>0`, constant `C≥0` and horizon control both actual nonprincipal character sums `Σ_(n≤X)χ(n)Λ(n)` and `Σ_(p≤X)χ(p)log p` by `CX exp(−ρ(log X)^(1/10))`, uniformly over `q≤(log X)^A`.

## Proof

[PROVED HERE] Take the [common signed tent rate](growing-conductor-character-tents-share-one-decay-rate.md), with constants `κ,C₀`, and the ordinary proved von Mangoldt rate `κψ,Cψ`. Set `ρ=min(κ/2,κψ)`, `u=(log X)^(1/10)`, `η=exp(−ρu)`, `Y=(1+η)X` and `h=log(1+η)≥η/2`. Since `Y≥X`, every modulus allowed at `X` is also allowed at `Y`.

The exact signed unsmoothing defect satisfies

`|Tentχ(Y)−Tentχ(X)−h Ψχ(X)| ≤ h(ψ(Y)−ψ(X))`.

Both tent values together cost at most `3C₀X exp(−κu)`, and `exp(−κu)≤η²`. After division by `h`, this costs at most `6C₀Xη`. The ordinary rate bounds the short-interval mass by `(1+3Cψ)Xη`. Hence `|Ψχ(X)|≤(6C₀+1+3Cψ)Xη`, with constants independent of modulus and character.

The difference between the character von Mangoldt sum and the character prime sum is bounded by the ordinary positive proper-prime-power mass `ψ(X)−θ(X)≤2√X log X`. The proved scalar absorption estimate puts this below `X exp(−ρu)` beyond one additional common horizon. Increasing the constant by one proves the prime version.

For the principal character, the correction from the ordinary prime sum is bounded by `θ(q)≤Dq≤D(log X)^A`. Every fixed logarithmic power is eventually below `X exp(−cu)` for any fixed `c>0`: first absorb it into `√X`, then use the proved scalar proper-power envelope. Combine this correction with the ordinary prime-number-theorem rate and take the smaller exponent. Thus all characters share one estimate for `Θχ(X)−1_(χ=1)X`; the same modulus correction pays nonunit residue classes.

For a reduced residue class, exact finite-character orthogonality gives `θ(X;q,r)=φ(q)^(-1)Σχ χ(r)^(-1)Θχ(X)`. Subtract the principal main term `X/φ(q)`, use `|χ(r)|≤1`, and sum the common character errors. The number of characters is exactly `φ(q)`, so the normalization cancels it. Every reduced class of every allowed modulus therefore has the same prime error bound.

## Formalization and scope

Lean: `GaloisForLFunctions/RHTower/DirichletCharacterUniformSums.lean`; audit pending. Neither complex signed sum is treated as monotone. Only the ordinary positive mass pays the unsmoothing defect. Nonunit residue indicators and finite signed-pattern expansion remain to complete the actual residue-source theorem.
