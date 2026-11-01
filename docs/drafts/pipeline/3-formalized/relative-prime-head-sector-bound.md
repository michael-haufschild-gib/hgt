# Relative prime-head sector bound

- **ID:** critical-rigidity-relative-prime-head
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Every finite actual prime-dilation head has squared conductor norm at most its active-prime mass times the exact diagonal adjunction energy, uniformly in the prime cutoff.

## Objects

Use normalized Ramanujan coordinates. Let `Δ_k a` be the actual coefficient change under `n↦kn`, and put

`L_Q(a)=Σ_(m≤Q) [log m+tameDifferent(m)] a_m²`,

`A_Q=Σ_(p≤Q, p prime) log p/(p−1)`,

`G_S(a)=Σ_(k∈S) Λ(k)/k · Δ_k a`.

Here `S` is any finite set of integers. The source weights are the actual von Mangoldt function.

## Dependency-closed proof

The exact prime-dilation identity already proves
`Σ_k Λ(k)/k · ||Δ_k a||² = L_Q(a)`.
Only prime powers whose prime is at most `Q` can change a retained conductor. Their total reciprocal Mangoldt mass is at most `A_Q`, independently of `S`. Weighted Cauchy–Schwarz, followed by the exact square identity, therefore gives

`||G_S(a)||² ≤ A_Q L_Q(a)`.

Ordinary Cauchy–Schwarz gives the mixed estimate

`|<b,G_S(a)>|² ≤ A_Q ||b||² L_Q(a)`.

The corpus's elementary prime-mass bound gives `A_Q≤14(1+log Q)`. No largest-conductor replacement for `L_Q(a)` is required. Finite-window sampling of the resulting normalized packet then gives

`Σ_(A<n≤A+K) [Σ_(k∈S) Λ(k)/k (F_a(kn)−F_a(n))]²`
`≤ [K+Q(Q−1)] A_Q L_Q(a)`.

## Novelty and scope

The square identity and reciprocal prime-mass bound are existing results in `SuccessorShellArithmetic`. This consequence keeps their exact conductor energy in a uniform mixed/head estimate. Existing absolute packet bounds replace that energy by a worst-conductor multiple of coefficient mass. The present estimate supplies relative prime control; it does not absorb the Gamma–pole–shell remainder of the complete Weil form.

## Lean

`CriticalScaleArithmeticRigidity/RelativePrimeHeads.lean`.

Declarations: `primeHeadCoefficient_sq_sum_le`, `primeHeadCoefficient_mixed_sq_le`, and `primeHead_window_sq_le`. Direct audit passed; only `propext`, `Classical.choice`, `Quot.sound`.
