# F2 — the first-prime trace controls whole-Haar admission

- **Stage:** 3-formalized
- **Result:** For `Re s>0` and an actual `C²` stage-`A` window test, the first source Hecke image of `windowPeriodLift s H` has finite Haar square energy on `(0,∞)` iff `H(−log2)=0`. Every test is admitted exactly when `A≤log2`.
- **Scope:** This concerns the actual paired WTZ period lift and both physical endpoints. It does not assert stability under later Hecke words or positivity of the Weil form.

## Proof

Put `ψ=windowPeriodLift s H`, `q=2^(−2s)` and `f=T₂,s ψ`. Compact support of the original window gives a positive lower cutoff for `ψ`. For all sufficiently small positive `a`, three branches vanish, leaving the exact formula

`f(a)=q ψ((a+1)/2)`.

The lift is differentiable near `1/2`; no issue at the glued logarithmic endpoint enters. Thus `f(a)→qψ(1/2)=ψ(2)` as `a→0+`, where the equality is the actual modular-inversion law. The existing zero-set identity gives `ψ(2)=0 ⇔ H(−log2)=0`.

If this trace is nonzero, continuity bounds `|f(a)|` below by a positive constant near zero. Finite Haar square energy would then make `a⁻¹` integrable there, contradicting the sharp power-integrability criterion. This proves necessity.

If the trace vanishes, differentiability gives `|f(a)|≤Ca` near zero, so `|f(a)|²/a≤C²a`. The existing source-Hecke decay theorem supplies finite upper Haar energy when `Re s>0`. Its uniform bound and measurability control the intervening compact interval. Hence the entire Haar square energy is finite.

For `A<log2`, the trace lies outside the support. At `A=log2`, continuity and vanishing to the left force the endpoint value to be zero. For `A>log2`, the existing first-prime bump has trace one and is excluded. Therefore universal whole-Haar admission has the closed threshold `A≤log2`.

The existing endpoint bump with nonzero right germ, but zero value at `−log2`, has no finite Hecke output cutoff. The trace classification nevertheless gives it finite whole-Haar energy. This exhibits the strict difference between pointwise trace admission and the germ condition for compact support.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/WholeHaarHeckeWindowAdmission`:

- `haarSquareIntegrable_zero_trace`
- `hecke_windowPeriodLift_finite_whole_haar_iff`
- `hecke_windowPeriodLift_all_whole_haar_iff`
- `exists_first_prime_window_finite_haar_noncompact`

Individual final `lake --old env lean` audit passed without warnings. All four declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Umbrella import wired.
