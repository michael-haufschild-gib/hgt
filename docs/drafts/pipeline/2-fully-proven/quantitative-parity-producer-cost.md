# Quantitative cost of parity producers

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Wall:** Π3
- **Statement:** There is an absolute `C>0` such that, for every `0<ε≤1`, a balanced nonnegative integer factorial producer has normalized slope `<1+ε`, alphabet radius at most `exp(exp(C/ε))`, and normalized Stirling error at most `exp(exp(C/ε))`.

## Proof [PROVED HERE]

Write `m(N)=Σ_{n≤N}μ(n)/n` and `S(N)=−Σ_{n≤N}μ(n)log(n)/n`. The corpus gives `|m(N)|≤C₀/(1+log N)⁴` and `S(N)→1`. Abel summation gives

`S(N)+m(N)log N = Σ_{j<N}m(j)(log(j+1)−log j)`.

For `N≥3`, the absolute tail is at most `C₀/(N log⁴N)+C₀/(3log³N)`. The boundary is at most `C₀/log³N`, hence `|S(N)−1|≤3C₀/log³N`.

Choose `ℓ=⌈K₀/ε⌉+10`, `B=2^ℓ+1`, `M=max(4ℓ+2,⌈48(2+log(B!))/ε⌉+6)`, and `P=2^M B!`. A fixed sufficiently large `K₀` makes the three tail errors and normalization error in the existing Möbius–Farkas proof smaller than their allotted multiples of ε. Upward rational rounding preserves all residue inequalities; denominator clearing gives the integer producer with every letter dividing `P` and slope `<1+ε`.

Let `g` be its step weight and `S` its unnormalized slope. The positive pronic expansion gives `g(r)≤Sr(r+1)`. Therefore `|g(r)−g(r−1)|≤Sr(r+1)`. Möbius inversion and `Σ_{d|k}d(d+1)≤4k²` give `|c(k)|≤4Sk²`. Summing the Stirling errors yields `E≤4SP³(5+log P)`. Since `S/m≤2`, `E/m≤8P³(5+log P)`; no denominator cost remains.

Finally `ℓ=O(1/ε)`, `log(B!)≤B log B`, and `M=O(log(B!)/ε+ℓ)`, so `log P≤exp(C₁/ε)`. Increasing the absolute constant absorbs the polynomial factor in `P`. The geometric telescoping prime-count bound consequently has the form `ψ(x)≤(1+ε)x+exp(exp(C/ε))log²x`, `x≥2`.

## Lean obligations

- `ArithmeticKreinLangerTheory/TheMobiusNormalizationHasARate.lean`: normalization bound written; check pending.
- `MultivariateParityAuxiliariesReachTheMainTerm.lean`: expose support in rational rounding, fixed-scale Farkas feasibility, and `exists_producer_with_quantitative_support`; checks pending.
- Finish the period growth estimate and combine with the polynomial alphabet cost. Ledger unchanged until the complete cost theorem passes.
