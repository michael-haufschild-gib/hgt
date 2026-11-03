# F2 — intrinsic whole-Haar admission of actual PM cores

- **Stage:** 3-formalized
- **Result [K]:** For `0<Re s<1/2`, `Im s>0`, the actual PM core belongs to `L²((0,∞),da/a)` iff its Mayer state is resonant.

## Exact boundary and admission law

`lim_(a→0+) core_s(a)=−ζ(2s)`.

Consequently, whole-Haar square energy is finite iff `ζ(2s)=0`, equivalently iff the actual Mayer state satisfies its fixed-state equation. This identifies the resonant parameter set through the physical core norm without imposing resonance in the core definition. It neither selects the critical line nor proves positivity.

## Proof

The literal logarithmic decomposition is

`core_s(exp(−x))=(k_s*h_s)(x)−ΓR(2s)ζ(2s)∫_(−∞)^x k_s`.

Here `h_s` is bounded and exponentially decaying, `k_s∈L¹`, and the actual Cauchy kernel has mass `ΓR(2s)⁻¹`. Dominated convergence makes the convolution vanish and the cumulative mass converge. Transfer through `x=−log a` gives the lower trace. Finite Haar energy forces this trace to vanish; the resonant endpoint estimates prove the converse. The source-state resonance criterion completes the equivalence.

## Lean

Module: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CoreHaarResonanceAdmission`.

- `mayerPeriodCore_lower_trace`
- `mayerPeriodCore_finite_whole_haar_iff_zeta_zero`
- `mayerPeriodCore_finite_whole_haar_iff_resonance`

Individual `lake --old env lean` audit passes without warnings. All three transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Umbrella import wired.
