# Uniform contours for growing-conductor prime sources

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For every `A,k>0`, one horizon gives the actual signed residue-Mangoldt error `≤X(log X)^(-k)Σ_r|F(r)|` simultaneously for every `q≤(log X)^A` and every residue pattern `F`.

## Source gap

`eventually_residueMangoldtReading_log_error` fixes `q` before choosing its horizon. Its character proof uses compactness at bounded heights. The conductor-confinement route needs growing families, so finite maxima over fixed moduli do not discharge this gap.

## Analytic construction

The corpus supplies `uniform_zero_free_region`, `siegel_zero_free` and `L_logDeriv_partial_fraction_all`. For each `ε>0`, combine their zero exclusions at width

`δ=a_ε q^(-ε)/log(q(T+5))²`.

At the center `2+it`, each local zero contributes at least one quarter of its multiplicity to the real part of the partial fraction. The absolute-convergence bound there therefore bounds total local multiplicity by `C log(q(T+5))`. At `|Re s-1|≤δ`, every local zero is at distance at least `3δ`. The resulting [paper proof](../2-fully-proven/dirichlet-logarithmic-derivatives-have-uniform-conductor-cost.md) gives a complete rectangle bound

`|L'/L(s,χ)|≤C_ε q^ε log(q(T+5))³`,

uniform over all nonprincipal characters, including real characters. These estimates use actual Dirichlet functions; no zero-free or prime-distribution input may remain assumed.

The [actual uniform contour bound](../2-fully-proven/actual-character-contours-have-uniform-conductor-cost.md) retains both tails and both horizontal edges; its Lean draft awaits audit. Selecting a common scale and signed unsmoothing must yield the stated growing-modulus source estimate. Abel transport supplies its residue-Mertens version. The weighted sum of all eight complete-Weil residual terms and effective negative-eigenvector confinement remain separate obligations.

## Contour scale

For `A≥0`, put `u=(log X)^(1/10)`, `ε=1/(10A+1)` and `R=10A+3`. On `q≤u^(10A)` and `u≥6`, one has `q^ε≤u` and `log q≤10A·u`. Set `d=a_ε/R²`, `D=1+d` and `T=exp(Du)-3`. Since `d≤1/8`, `log(q(T+5))≤Ru`. The narrower width `δ=d/(Du)^9` therefore lies in the proved rectangle, whose logarithmic-derivative bound is at most `B_εR³(Du)^9`. Its displacement exponent is `δ log X=(d/D^9)u`; both vertical decay and right-line tail decay are exponential in `u`. Polynomial absorption gives the common tent-sum rate. The full natural zero-free width need not give a decaying right-line tail at this height.
