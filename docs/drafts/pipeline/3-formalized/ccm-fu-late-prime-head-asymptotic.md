# CCM-FU: actual late-prime head compensation

- **ID:** CCM-FU-LPHA
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [prime-pair obstruction](../5-failed/ccm-fu-prime-pair-energy.md)
- **Statement:** With the actual channel sum `S(M)`, half-prime head `H(M)` and positive late-prime mass `T(M)`, `S(4N)/T(4N) → 0`, `H(4N)/T(4N) → 1`, and `H(4N)/(4N) → +∞`.

## Goal

Identify the intermediate head itself and its leading signed compensation. The previous obstruction proves only that the combined absolute head and final sum cannot have a common linear budget. This theorem determines which term carries the macroscopic mass. It does not supply the critical `S(M)=O(M)` residual required by SD1.

## Dependency-closed paper proof

The corpus's quantitative PNT gives `|psiDefect(k)| log(k)/k → 0`: the Chebyshev error is bounded by `C k exp(-c sqrt(log k))`, and the constant Gamma boundary has vanishing logarithmic normalization.

For `M ≥ k ≥ exp(2)`, antitonicity of `log(x)/sqrt(x)` and `sqrt(k+1)-sqrt(k) ≤ 1/sqrt(k)` imply

`log(M)/sqrt(M) * (sqrt(k+1)-sqrt(k)) |psiDefect(k)| ≤ |psiDefect(k)| log(k)/k`.

The finitely many earlier terms contribute a fixed constant times `log(M)/(M sqrt(M))`, tending to zero. Cesàro averaging of the displayed right side proves `S(M) log(M)/(M sqrt(M)) → 0` using the exact Möbius inversion/channel identity.

The existing prime-window lower bound gives `T(4N) ≥ N sqrt(N)/(80 log(2N))` eventually. Since `log(2N) ≤ log(4N)` eventually, the preceding little-o bound implies `S(4N)/T(4N) → 0`. The exact identity `H-S=T` gives `H/T → 1`. Finally `T(4N)/(4N) → +∞` and eventual `H/T ≥ 1/2` imply `H(4N)/(4N) → +∞`.

## Formalization

[MobiusDivisorLatePrimeHeadAsymptotic.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorLatePrimeHeadAsymptotic.lean) supplies seven unconditional public declarations:

- `tendsto_psiDefect_mul_log_div`;
- `sum_mobiusDivisorDilationChannel_eq_psiDefect_abel`;
- `tendsto_sum_mobiusDivisorDilationChannel_log_normalized`;
- `eventually_mobiusDivisorLatePrimeMass_ge`;
- `tendsto_total_div_mobiusDivisorLatePrimeMass`;
- `tendsto_mobiusDivisorHalfPrimeHead_div_latePrimeMass`;
- `tendsto_mobiusDivisorHalfPrimeHead_div_atTop`.

Scratch proof and final leaf both pass `lake env lean`; the final check produces only this module's exact olean. The module is wired once into `RHTower.lean`; no umbrella or large build is run. A single scratch axiom audit of these seven new public declarations reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Global `scripts/formal_tools.py lint` passes with existing file-size warnings. No numerical experiment or numerical certificate is used.

## Current frontier

The actual intermediate head, independently of any desired final bound, is asymptotic to positive superlinear late-prime mass. Leading compensation is therefore established source data. The required final signed residual remains `S(M)=O(M)`; neither this asymptotic nor its PNT input proves SD1 or RH.
