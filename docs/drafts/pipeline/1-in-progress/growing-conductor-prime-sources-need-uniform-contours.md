# Uniform contours for growing-conductor prime sources

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For every `A,k>0`, one horizon gives the actual signed residue-Mangoldt error `≤X(log X)^(-k)Σ_r|F(r)|` simultaneously for every `q≤(log X)^A` and every residue pattern `F`.

## Source gap

`eventually_residueMangoldtReading_log_error` fixes `q` before choosing its horizon. Its character proof uses compactness at bounded heights. The conductor-confinement route needs growing families, so finite maxima over fixed moduli do not discharge this gap.

## Analytic construction

The corpus supplies `uniform_zero_free_region`, `siegel_zero_free` and `L_logDeriv_partial_fraction_all`. For each `ε>0`, combine their zero exclusions at width

`δ=a_ε q^(-ε)/log(q(T+5))²`.

At the center `2+it`, each local zero contributes at least one third of its multiplicity to the real part of the partial fraction. The absolute-convergence bound there therefore bounds total local multiplicity by `C log(q(T+5))`. At `|Re s-1|≤δ`, every local zero is at distance at least `3δ`. This should give a complete rectangle bound

`|L'/L(s,χ)|≤C_ε q^ε log(q(T+5))³`,

uniform over all nonprincipal characters, including real characters. These estimates use actual Dirichlet functions; no zero-free or prime-distribution input may remain assumed.

The actual Perron identity, both tails, both horizontal edges, and signed unsmoothing must then yield the stated growing-modulus source estimate. Abel transport supplies its residue-Mertens version. The weighted sum of all eight complete-Weil residual terms and effective negative-eigenvector confinement remain separate obligations.
