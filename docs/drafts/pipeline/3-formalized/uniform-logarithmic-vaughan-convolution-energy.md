# Uniform logarithmic energy in the Vaughan convolution

- **ID:** uniform-logarithmic-vaughan-convolution-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** The actual Vaughan convolution fluctuation and all truncated Möbius receivers have every logarithmic pronic norm saving, uniformly over their cutoffs, below half damping.

## Exact result

Let `0<ε<1/2` and `β=1-2ε`. Write
`r_(U,V)=μ_≤U*μ_≤V*1-H_UH_V` and let `A_(r,ε)` be its centered damped
floor prefix. For every integer `q≥0`, a constant and threshold independent
of `U,V` give

`‖A_(r_(U,V),ε)‖_T ≤ C_q sqrt(T^β)/(log T)^q`.

The same estimate holds for every truncated Möbius prefix, with one constant
and threshold independent of its truncation cutoff. Zero cutoffs are included.

A summable reciprocal majorant first gives a common linear prefix bound.
For the actual convolution fluctuation, the majorant is twice the Vaughan
divisor-square majorant. Its eventual smooth-power bound absorbs the finite
head, yielding one global bound. The checked logarithmic prefix-to-energy
transfer then applies with all arithmetic inputs discharged.

## Lean audit

Module: [UniformLogarithmicEnergyInTheVaughanConvolution.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformLogarithmicEnergyInTheVaughanConvolution.lean).

Five public theorems:

- `abs_weightCenteredPrefix_le_linear_of_majorant`
- `abs_pmVaughanConvolutionFluctuationPrefix_le_linear`
- `exists_uniform_pmVaughanConvolutionFluctuationPrefix_rpow_bound`
- `exists_uniform_pmVaughanConvolutionFluctuation_pronicNorm_log_rate`
- `exists_uniform_patternPrefix_truncatedMoebius_pronicNorm_log_rate`

Corrected scratch checks and all five transitive axiom audits passed with
only `propext`, `Classical.choice`, and `Quot.sound`. Producing and final
direct `lake --old env lean` checks passed. The module is wired into the
BVI umbrella. Its scratch file was removed; no limits were raised.

The actual interior specialization is now checked in
[its companion card](logarithmic-energy-savings-for-the-mobius-interior.md).
The complete uniform Gram law remains under verification. These logarithmic
estimates give no fixed power saving; full Q-I remains open.
