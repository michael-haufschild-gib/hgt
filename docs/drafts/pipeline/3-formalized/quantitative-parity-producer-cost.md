# Quantitative cost of parity producers

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Π3
- **Statement:** There is an absolute `C>0` such that, for every `0<ε≤1`, a balanced nonnegative integer factorial producer has normalized slope `<1+ε`, alphabet radius at most `exp(exp(C/ε))`, and normalized Stirling error at most `exp(exp(C/ε))`.

## Proof

Write `m(N)=Σ_{n≤N}μ(n)/n` and `S(N)=−Σ_{n≤N}μ(n)log(n)/n`. The corpus gives `|m(N)|≤C₀/(1+log N)⁴` and `S(N)→1`. Abel summation gives

`S(N)+m(N)log N = Σ_{j<N}m(j)(log(j+1)−log j)`.

For `N≥3`, the absolute tail is at most `C₀/(N log⁴N)+C₀/(3log³N)`. The boundary is at most `C₀/log³N`, hence `|S(N)−1|≤3C₀/log³N`.

Choose `ℓ=⌈K₀/ε⌉+10`, `B=2^ℓ+1`, `M=max(4ℓ+2,⌈48(2+log(B!))/ε⌉+6)`, and `P=2^M B!`. A fixed sufficiently large `K₀` makes the three tail errors and normalization error in the existing Möbius–Farkas proof smaller than their allotted multiples of ε. Upward rational rounding preserves all residue inequalities; denominator clearing gives the integer producer with every letter dividing `P` and slope `<1+ε`.

Let `g` be its step weight and `S` its unnormalized slope. The positive pronic expansion gives `g(r)≤Sr(r+1)`. Therefore `|g(r)−g(r−1)|≤Sr(r+1)`. Möbius inversion and `Σ_{d|k}d(d+1)≤4k²` give `|c(k)|≤4Sk²`. Summing the Stirling errors yields `E≤4SP³(5+log P)`. Since `S/m≤2`, `E/m≤8P³(5+log P)`; no denominator cost remains.

Finally `ℓ=O(1/ε)`, `log(B!)≤B²`, and `M=O(log(B!)/ε+ℓ)`, so `log P≤exp(C₁/ε)`. Increasing the absolute constant absorbs the polynomial factor in `P`. Geometric telescoping gives `ψ(x),θ(x)≤(1+ε)x+12 exp(exp(C/ε))log²x`, `x≥2`.

## Lean

- `ArithmeticKreinLangerTheory/TheMobiusNormalizationHasARate.lean`: `exists_abs_moebiusLogHarmonicPartial_sub_one_le`.
- `ArithmeticKreinLangerTheory/MultivariateParityAuxiliariesReachTheMainTerm.lean`: `exists_producer_with_quantitative_support`.
- `ArithmeticKreinLangerTheory/TheParityProducerHasAQuantitativeCost.lean`: `exists_producer_with_double_exp_cost`, `exists_psi_le_double_exp_producer_cost`, `exists_theta_le_double_exp_producer_cost`, and `exists_parity_producer_with_quantitative_cost`.
- Coefficient input: `ArithmeticAuxiliaryDynamics.IsProducer.stencilErrorConst_le`.

All three modules checked individually; wired into `ArithmeticKreinLangerTheory.lean`.

## Remaining wall

Polynomial cost in `1/ε` remains open. This theorem gives a uniform upper rate, without a matching lower rate; Π3 remains partially solved.
