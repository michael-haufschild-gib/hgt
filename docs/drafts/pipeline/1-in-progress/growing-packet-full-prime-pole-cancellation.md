# Growing-packet full prime–pole cancellation

- **ID:** growing-packet-full-prime-pole-cancellation
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../reports/review-3110/obstacles-summary.md, A2 at `dbc7d26186`
- **Statement:** For some explicit `c>0`, the full prime–pole remainder divided by `√Y` tends uniformly to zero on bounded-coefficient packets with both cell indices at most `exp(c√log Y)`.

## Existing inputs

`TheFullPrimeWindowCancelsTheGrowingHeadPole` identifies the literal all-prime mixed source and proves cancellation for each fixed finite packet. `Sieve.ChebyshevSharpSelfRateOne.exists_abs_sum_vonMangoldt_sub_self_kappa_one_rate` gives unconditional error `B x exp(−√log x/960000)`.

## Proposed proof

Use the existing Suzuki prime hinge `F(t)=Σ_(n≤exp t) Λ(n)n⁻¹ᐟ²(t−log n)`.
`SuzukiScrewGrowthBound.abs_suzukiPrimeErrorIntegral_le`, applied to the explicit
Chebyshev rate, gives `|F(t)−4exp(t/2)|≤C exp(t/2−δ√t)` with
`δ=1/1920000`, after absorbing its linear boundary correction.

For intervals `[a,b)` and `[c,d)`, their correlation at lag `s` is
`H(c−b−s)−H(c−a−s)−H(d−b−s)+H(d−a−s)`, where `H(x)=max(0,x)`.
Thus the literal prime coupling is a four-hinge difference; a Haar detail
uses two such differences. The exponential main terms equal the first mixed
pole exactly. `HaarCellPoleBound.abs_haarProfile_exp_pos_le` and the exact
coarse negative exponential moment bound the second mixed pole by `8/Y`
after normalization, independently of the cell indices.

For detail and window indices at most `M`, all hinge arguments lie between
`log Y−log(M+1)` and `log Y+log(M+1)`. The resulting normalized pair error is
`≤C(M+1)exp(−(δ/2)√log Y)+8/Y`. Summing bounded coefficients over at most
`M²` pairs costs `(M+1)³`. The candidate explicit packet exponent is
`c=δ/12=1/23040000`; the resulting error decays as
`O(exp(−(δ/4)√log Y))`.

The exact Euler-source identity transfers this bound to any common physical
horizon `X` with `M≤X` and `Y(M+1)≤X+1`.

`ArithmeticIndexDescent.QuantitativePrimeHinges` proves
`exists_screwPrimeSum_explicit_classical_rate`; its direct Lean audit passed
with only standard axioms. `PrimeWindowHingeIdentities` also passed its direct
audit: ten exact-source and endpoint identities, including
`fullPrimeWindowCoupling_haar_sub_main_eq`.
The uniform pair and packet estimates still require compiler verification.

## Gates

- [x] Exact source and unconditional analytic input identified.
- [ ] Uniform quantitative window and packet estimates proved.
- [ ] Lean formalization, direct file audit, and transitive axiom audit.
