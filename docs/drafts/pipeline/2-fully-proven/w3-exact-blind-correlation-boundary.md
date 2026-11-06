# W3: the exact blind correlation has exponent one

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean in progress)
- **Statement:** For every probability measure on the modular arc, the scalarized test's autocorrelation `K` satisfies `|K(x)|≤C exp(−a exp|x|)` for some `a,C>0`. No such bound exists with `exp(b|x|)` for any `b>1`. In particular, the constructed integer-blind test attains this boundary.

## Proof

The single test has the entire autocorrelation of the positive shifted-Gamma mixture. For each family member, the corpus bounds the difference between its correlation and its radius-`L` truncation by
`2 M A² (j!(3/2)^j)² exp(−(π/6)exp(2(L−1)))`.
Choose `L=|x|/2`: the truncated correlation vanishes at lag `x`. Sum the nonnegative weights using their weighted factorial summability. This gives the upper bound with `a=(π/6)exp(−2)>0`.

Suppose a bound with exponent `b>1` held. It would make the Fourier transform `H` of `K` entire. Strip inversion gives `H(z)=Φ(z)Φ(−z)=Ξ(z)²R(z)` on `|Im z|<501/1000`. Every Xi zero lies in `|Im z|<1/2`; `R` is analytic there. Thus the entire divisor of `H` contains that of `Ξ²`, with full multiplicity. The capacity theorem `kb≤2`, with `k=2`, forces `K=0` almost everywhere. Fourier inversion at zero contradicts `H(0)=Φ(0)²≠0`.

This realizes the sharp squared-divisor boundary with an integer-blind correlation, strengthening the nonblind theta-square model. Blindness and Xi divisibility coexist precisely at the exponent-one boundary in this construction.

## Lean

Construction and positive-strip lemmas are prerequisites. The truncation estimate is
`CriticalHardyTheoryOfTheWindowCone.abs_crossCorr_truncTest_sub_le`; the lower obstruction is
`ExactExtremal.ae_eq_zero_of_doubleExp_XiC_pow_divisor`. Formal assembly pending.
