# F2 — reflection forced by actual Cauchy averaging

- **Stage:** 1-in-progress
- **Question:** Does compatibility with actual Cauchy averaging force the sharp reflection multiplier, even when no multiplier form is assumed for the candidate operator?
- **Inputs:** The physical field antiunitary in `ArithmeticMellinReflection`; the explicit Cauchy factor and its pending norm classification in `CauchyReflectionOrder`.
- **Scope:** The actual Epstein-to-core averaging bridge, not the full Mayer transfer family or Krein positivity.

## Candidate source statement

Let `A_s` be actual logarithmic Cauchy convolution divided by `Γℝ(2s)`, with Fourier multiplier `a_s(t)=symbol(2s,it)/Γℝ(2s)`. This kernel is integrable on the unweighted logarithmic line. Its multiplier is continuous and nowhere zero, hence the operator is injective with dense range.

The physical field reflection `J` forces, on the range of `A_s`,

`R_s A_s = A_(s♯) J`.

The Fourier formula predicts the actual adjoint identity `J A_s J=A_s†`. Writing `R_s=T_s J` then turns compatibility into the bounded linear factorization `T_s A_s†=A_(s♯)`. Localized interval tests should force `|a_(s♯)(t)|≤‖T_s‖|a_s(t)|`, without assuming that `T_s` is a multiplier. The only possible correction is therefore `B_s=a_(s♯)/conjugate(a_s)`. A bounded compatible reflection should exist exactly for `Re s≥1/4`, with the sharp norm proposed for `B_s`; dense range should give uniqueness. In the other direction, it remains a densely defined reflection with explicit Gamma order.

## Proof questions

- Identify the unweighted logarithmic convolution with its literal Fourier multiplier on all `L²` inputs.
- Derive the necessary pointwise quotient bound from operator factorization, using localized interval tests or an existing relative multiplier theorem.
- Construct the bounded compatible operator and prove uniqueness on the dense averaging range.
- Attach the identity to the actual resonant field and core columns. Keep full transfer intertwining and signed positivity separate.
