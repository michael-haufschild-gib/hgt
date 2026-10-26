# The inverse pole power spans the cofactor kernel

- **ID:** adr-cofactor-kernel-line
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `0 < ε < 1/2` let `q_ε(n) = Σ_{d≤n} μ(d) d^{-ε} ⌊n/d⌋^{1−ε}`. Then `q_ε` lies in the
  pole-trace domain `𝒳_ε`, `𝓛(q_ε) = 1`, `q_ε + D̃q_ε = 0`, and the kernel of the renormalized
  residual `I + D̃` on `𝒳_ε` is exactly the line `ℝ q_ε`.

## Paper proof
1. **Size of `q_ε`.** Split the Möbius sum at `D = ⌊√n⌋`. Head: `Σ_{d≤D} μ(d)d^{-ε}(n/d)^{1−ε} =
   n^{1−ε} m(D)`, `m(D) = Σ_{d≤D} μ(d)/d`, plus rounding `≤ D` (mean value, `α ≤ 1`). Tail: Abel
   summation against `M(x) ≪ x e^{-√(log x)/12}` with the monotone weight `w(d) = d^{-ε}⌊n/d⌋^{1−ε}`,
   `d·w(d) ≤ n^{1−ε}`, gives `≪ e^{-√(log D)/12} n^{1−ε}(3 + log n)`.
2. **`m(D) → 0` with rate.** Abel: `m(D) = M(D)/(D+1) + Σ_{d≤D} M(d)/(d(d+1))`; the full series is
   `0` because `m(D) → 0` (PNT); the tail beyond `D` is `≪ e^{-√(log D)/24}`.
3. Hence `|q_ε(n)| n^{-(1−ε)-1} ≪ e^{-√(log n)/48}/n + n^{-(1−ε)-1/2}`, summable: `q_ε ∈ 𝒳_ε`.
4. **Trace.** For real `w > 1 − ε`, Fubini over `(d, n)` and the block identity
   `Σ_{r<d} cell_w(md + r) = d^{-w} cell_w(m)` give `Σ q_ε(n) cell_w(n) = Δ(w)/ζ(w + ε)`,
   `Δ(w) = Σ m^{1−ε} cell_w(m)`. As `w ↓ 1 − ε`: `(w − α)Δ(w) → α` (explicit pole-sum remainder) and
   `(w − α)ζ(w + ε) → 1` (residue). Dominated convergence gives `Σ q_ε(n) cell_α(n) = α`, i.e. `𝓛 = 1`.
5. **Kernel.** `Σ_{j≤n} j^{-ε} q_ε(⌊n/j⌋) = n^{1−ε}` (Möbius floor inversion), so
   `(I + D̃)q_ε = n^{1−ε} − 𝓛(q_ε)n^{1−ε} = 0`. Conversely a residual-zero row equals `𝓛(v) q_ε`.

## Lean
`ArithmeticDefectRigidity/TheInversePolePowerSpansTheCofactorKernel.lean`:
`exists_abs_moebiusHarmonic_le`, `abs_inversePolePower_le`, `inversePolePower_mem_poleTraceDomain`,
`hasSum_dil_mul_mellinCell`, `hasSum_inversePolePower_mul_mellinCell`,
`poleTrace_inversePoleVector`, `renormalizedResidualOperator_inversePoleVector`,
`renormalizedResidual_eq_zero_iff`, `ker_renormalizedResidualOperator`. Standard axioms only.

## Insight
The renormalized inversion is not injective: its kernel is one explicit line, and membership of
that line in the trace domain is exactly the prime number theorem with a rate. A row is determined
by its residual only modulo `ℝ q_ε`, and the trace `𝓛` is the coordinate along that line.
