# A dominant ordinate forces current divergence

- **Stage:** 3-formalized
- **Source:** review-0911 §11.6, A67.

## Statement

For an actual finite top layer `G`, group zero copies by their ordinate.
If one ordinate `γ` has Gamma mass
`# {q∈G : Im q=γ} exp(πγ/4)` larger than the total Gamma mass of the other
ordinates, the corrected infinite prime current has norm tending to
infinity at every supercritical exponential damping speed.

## Proof

Equal ordinates have the same phase. Reverse triangle inequality bounds
the finite wave sum below by the positive difference of the two masses,
uniformly in height. The normalized actual current differs from this wave
sum by a term tending to zero. Its normalizing Gaussian mode has norm
tending to infinity. Thus growth holds at every sufficiently large height;
Kronecker recurrence is unnecessary under strict dominance.

Multiplicity must be included. Dominance of a single divisor copy is a
sufficient special case, but does not cover a repeated dominant zero.

## Inputs

- `not_asymptoticAbscissaLaw_has_escaping_layer_profile`.
- `norm_exceptionalOrdinateWave`.
- `tendsto_norm_gaussianMode_atTop_of_positive_rate`.

The corpus already proves unbounded recurrent excursions for every
nonempty finite top layer, without dominance. This target strengthens
excursions to a full limit for the dominant case.

## Lean

`ExceptionalLayerTheory/ADominantOrdinateForcesCurrentDivergence.lean`:
`ordinateDominanceMargin_le_norm_wave` and
`not_asymptoticAbscissaLaw_has_dominant_ordinate_divergence`.
Direct audit passed; transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.
