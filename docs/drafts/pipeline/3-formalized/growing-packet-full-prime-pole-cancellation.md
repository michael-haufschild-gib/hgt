# Growing-packet full prime–pole cancellation

- **ID:** growing-packet-full-prime-pole-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../../reports/review-3110/obstacles-summary.md, A2 at `dbc7d26186`
- **Statement:** The full prime–pole remainder divided by `√Y` tends uniformly to zero on bounded-coefficient packets with both cell indices at most `exp(√log Y/23040000)`.

## Uniform bound

There is `C>0` such that, eventually in `Y`, for every
`M≤exp(√log Y/23040000)`, every finite `S⊆{1,…,M}²`, and every coefficient
family with `|c_ab|≤B`,

`|Σ_(a,b)∈S c_ab fullPrimeWindowRemainder(Y,a,b)|`

`≤ C|B| exp(−√log Y/7680000)`.

The threshold and `C` are independent of the packet and coefficients.

## Existing inputs

`TheFullPrimeWindowCancelsTheGrowingHeadPole` identifies the literal all-prime mixed source and proves cancellation for each fixed finite packet. `Sieve.ChebyshevSharpSelfRateOne.exists_abs_sum_vonMangoldt_sub_self_kappa_one_rate` gives unconditional error `B x exp(−√log x/960000)`.

## Proof

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
`M²` pairs costs `(M+1)³`. The explicit packet exponent is
`c=δ/12=1/23040000`; the resulting error decays as
`O(exp(−(δ/4)√log Y))`.

The exact Euler-source identity transfers this bound to any common physical
horizon `X` with `M≤X` and `Y(M+1)≤X+1`.

## Lean declarations and audit

- `ArithmeticIndexDescent.QuantitativePrimeHinges`:
  `exists_screwPrimeSum_explicit_classical_rate`.
- `ArithmeticIndexDescent.PrimeWindowHingeIdentities`:
  `fullPrimeWindowCoupling_haar_eq_hinges`,
  `fullPrimeWindowCoupling_haar_sub_main_eq`.
- `ArithmeticIndexDescent.GrowingPacketPrimePoleCancellation`:
  `exists_fullPrimeWindowRemainder_uniform_pair_rate`,
  `exists_fullPrimeWindowRemainder_growing_packet_rate`,
  `fullPrimeWindowRemainder_uniform_growing_packets`,
  `allPrimesMixedSource_uniform_growing_packets`.

All three modules passed direct Lean checks without warnings and are wired into
the programme umbrella. All fifteen public axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`; no proof holes or resource-limit overrides.

## Gates

- [x] Exact source and unconditional analytic input identified.
- [x] Uniform quantitative window and packet estimates proved.
- [x] Lean formalization, direct file audit, and transitive axiom audit.
