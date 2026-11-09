# Actual Weil lag has residual cancellation bases

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacles:** B13, B112; topological size of recurrent-base families.
- **Statement:** For every positive accuracy sequence, actual Weil lag has a dense G-delta of bases with infinitely many readings below that sequence. One residual set works for every exponential decay rate. Under AAL failure, its positive part has Hausdorff dimension zero.
- **Consequence:** Actual zeta already has residual recurrence at every real rate, unconditionally. Adding this property to ZAL adds no arithmetic restriction; the positive-dimensional recurrence input remains substantive.

## Corpus evidence

`RHTower.frequently_integerLag_le_neg` in `WeilLagFunctionOmega.lean` and `RHTower.frequently_integerLag_gt` in `WeilLagFunctionRecurrence.lean` give both signs at arbitrarily large logarithmic arguments. Unconditional continuity gives arbitrarily large zeros. `RHTower.weilLagFunctionReal_neg` supplies reflection. The preceding dimension theorem applies under AAL failure.

## Proof

Write `Phi(t)=weilLagFunctionReal t`. The corpus proves continuity and evenness unconditionally. It also proves `Phi(log n)>c/2` for arbitrarily large integers `n`, where `c=poleSharpConstant>0`, and `Phi(log n)<=-eta` for arbitrarily large integers, for some `eta>0`. Given `T`, choose such a positive reading with `n>exp(T)`, then a negative reading with index `m>=n`. The intermediate value theorem gives a zero in `[log n,log m]`, hence beyond `T`. No zero-configuration assumption enters this step.

Let `f` be any continuous even real function with unbounded positive zeros. Fix `0<=a<b` and a level cutoff `N`. Choose a zero `z` larger than both `bN` and `ab/(b-a)`, and put `n=floor(z/b)+1`. Then `n>=N`, `n>0`, and `z<bn<=z+b`. Moreover `ab<z(b-a)` implies `a(z+b)<zb`; multiplying `bn<=z+b` by `a>=0` gives `an<z`. Thus `a<z/n<b` and `f(n(z/n))=0`. Any interval meeting the positive half-line contains such a positive subinterval. An interval lying on the negative half-line is handled by reflection. Therefore every tail of the integer-dilated zero sets meets every open interval.

For an arbitrary countable family `epsilon(m,n)>0`, set
`U(m,N)=union_{n>=N}{ell: |f(n ell)|<epsilon(m,n)}`.
Continuity makes each set open; the exact-zero argument makes each dense. Baire's theorem gives a dense G-delta `S=intersection_{m,N} U(m,N)`. Its members satisfy every accuracy schedule infinitely often. Every nonempty open interval meets `S` uncountably: otherwise its intersection with `S` and its intersection with the meagre complement of `S` would make that open interval meagre, contradicting Baire's theorem.

Apply this to actual `Phi`. For `epsilon(m,n)=exp(-(m+1)n)`, the resulting single residual set has, at each positive base `ell`, infinitely many readings bounded by `exp(a n ell)` for every real rate `a`. Indeed, choose a natural `m>-a ell` and compare exponents. The recurrence constant is exactly one. Under AAL failure, the positive part lies in the recurrence-base set at rate `a=-1`, strictly below `zetaZeroAbscissa-1/2`; the preceding dimension theorem gives Hausdorff dimension zero.

## Novelty and Lean certificate

The corpus provides unconditional sign oscillation at logarithmic integer arguments and a residual cancellation example for a finite cosine pair. The new conclusion concerns arbitrary prescribed accuracies along integer multiples of one base for the **actual Weil lag**, unconditionally. Topological recurrence is already satisfied by zeta; under AAL failure its rapid-cancellation bases are nevertheless zero-dimensional. The general sampling lemma, actual-zeta specialization, and dimension comparison count together.

All new declarations belong to `GaloisForLFunctions.InfiniteRankWeilTheory`:

- `ResidualSamplingCancellation.lean`: `dense_samplingCancellationBases`, `isGδ_samplingCancellationBases`, `mem_samplingCancellationBases_iff`, and `not_countable_inter_Ioo_of_dense_isGδ`.
- `ZetaResidualSampling.lean`: `exists_actualLag_zero_ge`, `actualLag_samplingCancellation_residual`, `not_countable_lagRapidCancellationBases_inter_Ioo`, `exists_residual_actualLag_recurrence_all_rates`, and `dimH_positive_lagRapidCancellationBases_eq_zero_of_not_asymptoticAbscissaLaw`.

Final direct audit: `lake --old env lean GaloisForLFunctions/InfiniteRankWeilTheory/ZetaResidualSampling.lean`, exit zero. Transitive axiom audits returned only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into the programme umbrella.
