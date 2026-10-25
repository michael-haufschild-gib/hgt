# Uniform logarithmic cancellation in Möbius floor sums

- **ID:** uniform-logarithmic-cancellation-in-mobius-floor-sums
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../2-fully-proven/uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** Truncated Möbius floor sums have every logarithmic saving around their harmonic mean, uniformly over every cutoff.

Write `S_U(n)=Σ_(d≤U)μ(d)⌊n/d⌋` and `H_U=Σ_(d≤U)μ(d)/d`.
For every `q∈ℕ`, one nonnegative constant and one eventual threshold give

`|S_U(n)−nH_U|≤C_q n/(log n)^q`

for all cutoffs U. The floor sum is exactly the undamped Vaughan convolution
with second cutoff one, so the checked uniform convolution rate applies.

The finite estimates are also certified. Rounding gives `|S_U(n)−nH_U|≤U`.
Möbius inversion gives
`S_U(n)=1−Σ_(k≤n)Σ_(U<d≤⌊n/k⌋)μ(d)` for positive n. If common envelopes
`|M(x)|≤Lx` and `|H_x|≤K` hold for x≥D, the cutoff-uniform error is at most
`D+1+2Ln h(n)+Kn`, where h(n) is the ordinary harmonic sum. The actual
Mertens and harmonic logarithmic rates discharge these envelopes and give
the unconditional finite logarithmic bound.

## Lean audit

Module: [UniformLogarithmicCancellationInMobiusFloorSums.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformLogarithmicCancellationInMobiusFloorSums.lean).

- `abs_pmUndampedMobiusFloorPrefix_sub_mean_le`
- `pmUndampedMobiusFloorPrefix_eq_one_sub_tail`
- `abs_pmUndampedMobiusFloorPrefix_sub_one_le`
- `abs_pmUndampedMobiusFloorPrefix_sub_mean_le_uniform`
- `exists_uniform_pmUndampedMobiusFloorPrefix_log_bound`
- `pmUndampedVaughanConvolutionPrefix_one_right`
- `exists_uniform_pmUndampedMobiusFloorPrefix_log_rate`

Final direct `lake --old env lean` check passed. All seven transitive axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The BVI
umbrella import is present. No olean was needed; the owned scratch was removed.
Full Q-I remains open: logarithmic savings supply no fixed power gain.
