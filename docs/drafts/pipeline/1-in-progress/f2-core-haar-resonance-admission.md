# F2 — intrinsic whole-Haar admission of actual PM cores

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For `0<Re s<1/2`, `Im s>0`, the actual PM core belongs to `L²((0,∞),da/a)` exactly when its Mayer state is resonant.

## Mathematical target

Prove the exact lower trace `lim_(a→0+) core_s(a)=−ζ(2s)`. Finite Haar energy forces this trace to vanish. Conversely the audited resonant endpoint estimates give finite energy. The existing source-state resonance criterion then identifies physical admission with the actual Mayer fixed-state equation.

This would identify the resonant parameter set by a physical norm condition, without selecting zeros in the definition of the core family. It does not select the critical line or prove positivity.

## Inputs and proof route

The literal logarithmic decomposition is

`core_s(exp(−x))=(k_s*h_s)(x)−ΓR(2s)ζ(2s)∫_(−∞)^x k_s`,

where `h_s` is bounded and exponentially decaying and `k_s∈L¹`. The actual Cauchy kernel has unit zeroth Mellin mass, hence `∫k_s=ΓR(2s)⁻¹`. Dominated convergence gives `(k_s*h_s)(x)→0` and convergence of its cumulative mass. Transfer through `x=−log a` yields the trace.

Existing results characterize the unaveraged theta field's zeroth Mellin admission. The missing claim concerns the actual Cauchy-averaged PM core and whole-Haar square energy.

## Verification

Paper dependency check complete; Lean proof pending. No conclusion about complete Weil positivity.
