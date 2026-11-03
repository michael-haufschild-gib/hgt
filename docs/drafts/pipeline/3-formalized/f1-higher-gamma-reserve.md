# Higher Gamma lags and first-moment reserve

- **ID:** F1-HGR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Failed two-moment payment](../5-failed/f1-primitive-variance-joint-payment.md)
- **Statement:** Every real odd C² test supported in `[-1/2,1/2]` satisfies
  `Q≥P+(193/10000)E+M₃/960+M₄/192` and
  `Q≥P+(193/10000+17/23040)E+(13/3840)m²`. Some such test has `P+E/64<0<Q`.

Here `E=∫F²`, `m=∫xF`, `C(t)=∫F(x)F(x+t)dx`, `Mₖ=∫₀¹tᵏ(E−C(t))dt`, and
`P` is the exact retained Gamma/prime/pole form. The proved remainder identity is
`Q=P+∫₀¹r(t)(E−C(t))dt+2δE`, where

`r(t)=e^(t/2)/sinh t−1/t−1/2+t/24+t²/16`,
`δ=archLevyAntideriv(1)−log2−π/4+1/4−1/96`.

## Local remainder

For `0<z≤1/2`, set `A=1−z²/6+z⁴/60`, `B=1−z²/2+z⁴/6`. Both lie in `[0,1]`.
The proved exponential Taylor remainder gives

`sinh z≤z+z³/6+z⁵/120+z⁶/617`,
`cosh z≤1+z²/2+z⁴/24+z⁶/617`.

The residual identities are

`A(z+z³/6+z⁵/120)+z⁶/617−z
 =z⁵(−1/360+z/617+z²/720+z⁴/7200)≤0`,
`B(1+z²/2+z⁴/24)+z⁶/617−1
 =z⁴(−1/24+z²/16+z⁴/144+z²/617)≤0`.

Thus `A≤z/sinh z` and `B≤1/cosh z`. Set `z=t/2` and use
`e^(t/2)/sinh t=1/(2sinh z)+1/(2cosh z)` to obtain
`r(t)≥t³/960+t⁴/192` on `0<t≤1`. Since `E−C(t)≥0`, integration retains
`M₃/960+M₄/192`. Compact C² regularity supplies all required integrability.

## Exterior reserve

Five positive Laplace modes give

`archLevyAntideriv(1)≥2[v+v⁵/5+v⁹/9+v¹³/13+v¹⁷/17]`, `v=e^(−1/2)`.

The exponential Taylor upper bound at `1/2` proves `v≥60653/100000`. Substitution,
`log2<693147181/10⁹`, and `π<3141593/10⁶` give `δ>193/20000` by rational arithmetic.
Combining this with the local remainder proves the first asserted bound.

## Moment credit

Odd correlation cancellation gives `M₀=E` and `M₂=E/3+m²`. On `[0,1]`,

`t³/960+t⁴/192−(13/3840)t²+1/2560
 =(t−1/2)²(t+1/4)/960+(t²−1/4)²/192≥0`.

Multiply by `E−C(t)` and integrate. The local remainder is at least
`(13/3840)M₂−M₀/2560=17E/23040+13m²/3840`, proving the second bound.

## Lean

`TheGammaRemainderRetainsHigherLags` proves
`retainedGammaRemainderWeight_ge_higher_lags`, `retainedGammaRemainder_ge_higher_lags`,
`gamma_tail_one_stronger_reserve`, `weilQuad_ge_retainedOddGamma_add_higher_lags`,
and `weilQuad_ge_retainedOddGamma_add_moment_reserve`. The module compiles with
`[propext, Classical.choice, Quot.sound]` only and is umbrella-imported.

## Repair of the quadratic cutoff

For `F(x)=2x(1−4x²)²` on `|x|≤1/2`, zero outside, use the
[exact correlation, mass, position and logarithmic data](../5-failed/f1-primitive-variance-joint-payment.md).
For every natural `k`, direct integration of that correlation gives

`Mₖ=256/[315(k+3)]−128/[21(k+5)]+128/[15(k+6)]
 −512/[105(k+8)]+128/[63(k+10)]−256/[693(k+12)]`.

Let `l=693147180/10⁹`, `h=693147181/10⁹`. In the correlation polynomial evaluate
positive powers at `h` and negative powers at `l`, giving `C(log2)≤c₊<0`.
Since `log2/√2≥49/100`, the prime gain is at least `−2(49/100)c₊`.
The proved sinh residual estimate gives
`sinhPairing(F)²/2≤(97/192)m²+(97/483840)E`, and
`γ+logπ+log2≤c₁=577216/10⁶+11448/10⁴+h`. Hence

`P(F)+(193/10000)E+M₃/960+M₄/192`
` ≥ L−c₁E−M₁/24−m²/16−(97/192)m²−(97/483840)E`
`   −2(49/100)c₊+(193/10000)E+M₃/960+M₄/192 > 0`.

The final strict inequality is rational and kernel-checked with
`E=128/3465`, `m=4/105` and the displayed exact lag data.
The same support-preserving smooth family used for `P+E/64<0` converges in mass,
retained form and every polynomial lag moment. For the latter, correlations are
bounded by `1`, so `2|tᵏ|` dominates the weighted deficit on `[0,1]`.
Dominated convergence preserves both strict signs simultaneously. The universal
higher-lag bound then gives an actual odd C² test with `P+E/64<0<Q`.

`TheHigherGammaReserveRepairsTheQuadraticCutoff` proves
`quadraticCutoffWindow_jump_moment`,
`retainedOddGamma_quadraticCutoff_add_higher_reserve_pos`, and
`exists_odd_unit_reservedGamma_neg_weil_pos`. Its individual source check passes;
all three transitive-axiom audits are `[propext, Classical.choice, Quot.sound]` only.
The module is umbrella-imported.

Complete odd unit-window positivity remains open.
