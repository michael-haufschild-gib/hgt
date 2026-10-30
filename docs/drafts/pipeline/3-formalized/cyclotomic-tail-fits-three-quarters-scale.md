# The cyclotomic tail fits the three-quarters scale

- **ID:** cyclotomic-tail-fits-three-quarters-scale
- **Stage:** 3-formalized
- **Type:** THEOREM
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

The primitive order of `ζ_k` is `Q/gcd(Q,k)`. Since `gcd(Q,k)` divides both
`k` and `Q−k`, this gives `Q≤orderOf(ζ_k)·min(k,Q−k)`.
Consequently every primitive conductor at most `L` is in the far packet when
`KL<Q`. The remaining band has small angular frequency and large primitive
conductor; fixed-conductor limits do not control it.

## Verification

- [x] Dependency-closed paper proof.
- [x] Lean formalization and standard-axiom audit.

`CompletedArithmeticForms/ChebyshevCyclotomicTail.lean` proves:

- `chebyshevCyclotomicRemainder_eq_far_add_near`: exact partition.
- `cyclotomicMode_gap`, `chebyshevCyclotomic_mode_le`: root spacing and individual mode bound.
- `chebyshevCyclotomicFar_le`: `288 N(N+1)/K` for every `K≥1`.
- `chebyshevCyclotomicFar_sqrt_le`: `288 N√(N+1)` outside the square-root band.
- `chebyshevCyclotomicNear_card_le`: at most `2K` remaining modes.
- `orderOf_cyclotomicMode`, `le_orderOf_cyclotomicMode_mul_min`,
  `cyclotomicMode_far_of_orderOf_le`: exact conductor and angular-frequency separation.

Foreground `lake --old env lean` check and standard-axiom audits passed for all
ten declarations, including `norm_cyclotomicMode`. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Imported by `CompletedArithmeticForms.lean`.
