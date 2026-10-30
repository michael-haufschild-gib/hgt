# The cyclotomic tail fits the three-quarters scale

- **ID:** cyclotomic-tail-fits-three-quarters-scale
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Source:** fourth-power-mesh-signed-saving; `CompletedArithmeticForms.ChebyshevCyclotomicCompletion`
- **Statement:** At conductor `Q=N+1`, the actual cyclotomic remainder outside its first and last `K` modes is at most `288 NQ/K`, for integers `K≥1`.

## Mathematical content

Put `a_j=chebyshevConductorCoeff j`, `ζ_k=exp(2πik/Q)` and
`P(ζ)=Σ_{1≤j<Q} a_j Σ_{0≤l<j} ζ^l`. The remainder is
`R_N=Q⁻¹Σ_{1≤k<Q}|(1+ζ_k)P(ζ_k)|²`.
Its far part retains `K<k` and `K<Q−k`.
Taking `K=⌈√Q⌉` gives far energy at most `288 N√Q`.
Only the at most `2⌈√Q⌉` remaining modes need a signed estimate.
This does not bound those modes or resolve the fourth-power covariance question.

## Paper proof

The proved coefficient envelope gives `Σ_{j≤N}|a_j|≤12√N`.
The exact identity `(1−ζ)P(ζ)=Σa_j−Σa_jζ^j` therefore gives
`|(1−ζ)P(ζ)|≤24√N` on the unit circle.
For `1≤k<Q`, put `r=min(k,Q−k)`. Jordan's sine inequality gives
`|1−ζ_k|=2 sin(πk/Q)≥4r/Q`, while `|1+ζ_k|≤2`.
Hence `|(1+ζ_k)P(ζ_k)|²≤144 Q²N/r²`.
Use `r⁻²≤k⁻²+(Q−k)⁻²`. On the far set, each inverse-square sum
is at most `Σ_{n>K}n⁻²≤1/K`; the second uses the injective change
`k↦Q−k`. Dividing by `Q` proves the stated bound. Root enumeration
and partitioning the finite sum give the exact near-plus-far decomposition.

## Verification

- [x] Dependency-closed paper proof.
- [ ] Lean formalization and standard-axiom audit.
