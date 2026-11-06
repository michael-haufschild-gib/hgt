# Strict Laguerre positivity inside the Vinogradov–Korobov boundary

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ78
- **Statement:** For all sufficiently large `|x|`, the actual cosine producer satisfies
  `A_h′(x)² − A_h(x)A_h″(x) > 0` whenever
  `h > 1/2 − vkHadamardWidth(|x| + 1)`.

## Proof

The corpus proves the non-strict inequality in this window. The following argument
also excludes equality.

1. Choose `T = γ + 1`, where VK gives `|Im w| ≤ 1/2 − w(|Re w|)`
   for Xi zeros above `γ`. If `|x − Re w| < 1`, then
   `γ ≤ |Re w| < |x| + 1`; monotonicity of `w` gives `|Im w| < h`.
   Also `w(|x| + 1) ≤ 1/4`, hence `h > 0`.
2. Every nonreal producer zero `z` belongs to a Xi defect disk:
   `(Re w − Re z)² + (Im z)² + h² ≤ (Im w)² < 1/4`.
   Its witness cannot satisfy `|x − Re w| < 1`, by step 1.
   Thus `|Re z − x| > 1/2 > |Im z|`. Real producer zeros other
   than `x` also satisfy `(Im z)² < (Re z − x)²`.
3. Off the divisor, the even order-one Hadamard factorization gives
   `A_h′² − A_h A_h″ = A_h² Σ_z (x − z)⁻²`, counting multiplicities.
   Termwise differentiation is justified on a zero-free disc: nearby poles
   are finite; the remaining logarithmic-derivative terms have a summable
   `O(|z|⁻²)` majorant. Each inverse-square summand has positive real part
   by step 2. The sum is nonempty because the positive sech handoff to Xi
   forces `A_h` to have a real zero. Hence the Laguerre expression is positive.
4. At `A_h(x)=0`, every Xi zero satisfies
   `(Im w)² < (x − Re w)² + h²`: step 1 handles nearby zeros;
   `(Im w)² < 1/4` handles the others. The defect-trace simplicity theorem
   gives `A_h′(x) ≠ 0`, so the expression equals `A_h′(x)² > 0`.

All inputs are unconditional corpus theorems: VK displacement, defect disks,
order-one Hadamard factorization, the real-zero existence theorem and local
phase monotonicity.

## Lean

Module: `GaloisForLFunctions/ZeroConfigurationGeometry/CosineProducerStrictWindow.lean`.
Namespace: `GaloisForLFunctions.ZeroConfigurationGeometry`.

- `exists_cosineProducer_strict_laguerre_vk`: the producer inequality above.
- `exists_xi_strict_laguerre_vk`: equivalently, for large `|Im s|` and
  `Re s > 1 − vkHadamardWidth(|Im s|+1)`,
  `(Im ξ′(s))² + Re ξ(s) Re ξ″(s) > 0`.

Direct `lake --old env lean` audit passed. Both transitive axiom lists contain
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.

## Scope

This strengthens the known nonnegative VK region to a strict region inside
`0 < h < 1/2`. Positivity throughout that entire band remains open. No numerical
input or additional zero hypothesis is used.
