# Actual smooth taper transport in logarithmic stabilizer rows

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](../1-in-progress/parity-stabilizer-logarithmic-coalescent-calibration.md).
- **Lean:** `TransThresholdPairCorrelation/StabilizerTaperTransport.lean`.

## Statements

For every admissible standard taper `g=autocorr(φ²)`,

`|g(x)−g(y)|≤2|x−y|`.

The constant is independent of taper length, collar and monotone transition
profile (`abs_taperAutocorrelation_sub_le`).

Let `V` be the finite even-shift logarithmic stabilizer row with the extra
factor `g(log(m+2r))−g(log m)`, retaining the square-root pair weight.
For compact C⁴ Ω, m>0 and 2R≤m,

`|V|≤8 O(Q)[M₀/T+16T³D₄]/T`,

where `O(Q)=Σ_{q≤Q,odd}μ²(q)/φ(q)`, `M₀=∫|Ω|`, and
`D₄=∫|Ω''''|` over the extended support interval
(`abs_stabilizerTaperVariation_le`). For each fixed smooth height profile,
there is C≥0 such that `|V|≤C O(Q)/T` for T≥1, uniformly over all admissible
standard tapers (`WindowProfile.exists_stabilizerTaperVariation_le`).

## Proof

Put F=φ². Compact support, C¹ regularity, `0≤F≤1` and `∫|F'|=2` give
`|g'(t)|=|∫F(u)F'(u+t)du|≤2`. The mean-value inequality proves the
Lipschitz bound. Since `log(m+2r)−log m=log(1+2r/m)`, endpoint variation
is bounded by twice the absolute logarithmic first moment. The previously
formalized decay estimate gives the explicit bound and fixed-profile scaling.

## Consequence and scope

The actual taper may be retained through signed spatial/diagonal cancellation
without a taper-length loss in endpoint transport. Aperture reindexing,
global primitive-sample calibration and actual prime discrepancy remain open.
The cosine-shaped taper in the separate cosine certificate requires its own
compatibility argument.

All three transitive axiom audits use only `propext`, `Classical.choice` and
`Quot.sound`; the final direct leaf check passes.
