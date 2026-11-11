# The step-packet matrices at ratios four and seven with an explicit block error

- **ID:** A135
- **Stage:** 3-formalized
- **Lean:** `AbsoluteGeometryOfSpecZ/TheStepPacketMatricesAtFiniteScaleHaveAnExplicitError.lean`

## Statement

For a divisor constant on the `J` blocks of `B` points above `RB`, `R + J ≤ QR`:

`|combW(block σ)/B − 𝔚_Q(stepPacket σ)| ≤ 6(J+1)·E(R+J, Q, B)·Σσ_j²`,
`E(X, Q, B) = (2X + 16(1 + log 2XB) + 2ψ(Q))/B`.

Ratio four (`Q = 4`, `J = 3R`, `ψ(4) = log 12`) and ratio seven (`Q = 7`, `J = 6R`,
`ψ(7) = log 420`) are the instances. The entries of `𝔚_Q` on step packets are the closed forms of
`packetForm_flatPacket_eq` through `stepEntry`. Transfer both ways: a margin `μ₀` of the matrix gives
`combW ≥ (μ₀/2)BΣσ²` at every `B` with `6(J+1)E ≤ μ₀/2`; a comb bound `c` at one `B` gives
`𝔚_Q ≥ (c − 6(J+1)E)Σσ²`.

## Proof

The comb form of one window `(aN, bN]` is exact: `2(H_{bN} − H_{aN})(b−a)N`, the jet energy via
`X(A,B) = ½(S(B) − S(B−A) + S(B+A+1) − S(B+1)) − ¾H_A`, `S(M) = MH_M − M`, the counterterm
`log(aN)! − aN log 2π`, and contact counts `⌊bN/k⌋ − aN`. Errors: `0 ≤ H_n − log n − γ ≤ 1/n`;
`0 < log n! − (n log n − n) ≤ 1 + ½ log n`; `|count − (b/k − a)⁺N| ≤ 1`. One window is within
`E(b, Q, N)`; a nested entry within `3E`; the polar sum over `J+1` nested windows and
`Σ nestedCoeff² ≤ 4Σσ²` give the factor `6(J+1)`.

Declarations: `abs_combForm_blockFunction_div_sub_le`, `…_ratioFour`, `…_ratioSeven`,
`le_combForm_of_packetForm_ge`, `packetForm_ge_of_combForm_ge`, `abs_combForm_window_div_sub_le`.

## Scope

No sign of `𝔚_4` or `𝔚_7` is certified: that is a computation of the matrix spectrum (RH at
ratio four leaves the first contact `log 2`), outside this formalization.
