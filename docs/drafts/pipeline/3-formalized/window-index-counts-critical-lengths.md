# The window index counts critical lengths

- **ID:** window-index-counts-critical-lengths
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411, §2.1, A10.
- **Scope:** Continuity and critical-length calculus only. Quantitative location from
  right zeros and the resolved-count/Shannon gap remain open.

## Statement

Let `ι(A)` be the negative index of ζ's Weil form on a window of length `A`,
and put `Lₙ = sup {A : ι(A) ≤ n}` in `EReal`. Then

1. `ι(A) = #{n ∈ ℕ : Lₙ < A}` at every real length.
2. `Lₙ` is nondecreasing; only finitely many indices satisfy `Lₙ ≤ A` for any finite `A`.
3. `Lₙ = ∞` iff the number of distinct zeros right of the critical line is at most `n`.

The strict inequality in (1) fixes the value at each jump. No positivity or RH hypothesis
is assumed.

## Proof

[PROVED HERE] For any tempered zero configuration, set `tⱼ = 1 − 1/(j+2)` and
`fⱼ(u)=f(u/tⱼ)`. A test supported in `[-a,a]` contracts to `[-atⱼ,atⱼ]`.
Fourier scaling gives `f̂ⱼ(z)=tⱼ f̂(tⱼz)`. Since `1/2 ≤ tⱼ < 1`, the existing
quadratic Fourier decay bound gives a uniform bound
`|f̂ⱼ(z)| ≤ C_f/(1+|Re z|)²` on `|Im z|≤1/2`.
The transforms converge pointwise to `f̂`. Products for two tests are dominated by
`(4C_f C_g/3)m_ρ/(1+|γ_ρ|²)`, summable by temperedness. Thus every finite
zero-side Gram matrix converges entrywise. Lower semicontinuity of its negative
index preserves all its negative squares in a strictly smaller window.

Taking suprema over finite families proves
`ι(A)=sup_{0<B<A}ι(B)` for `A>0`. The index is zero for `A≤3/5`, so every
sublevel set `{A : ι(A)≤n}` is downward closed and contains its finite right
endpoint. Consequently `A≤Lₙ ↔ ι(A)≤n`, or `Lₙ<A ↔ n<ι(A)`.
Since `ι(A)` is finite, the latter set is exactly `{0,…,ι(A)−1}`, proving (1).
Nested sublevel sets give monotonicity. The indices with `Lₙ≤A` lie among those
with `Lₙ<A+1`, proving local finiteness. Finally, `Lₙ=∞` iff `ι(A)≤n` for every
`A`; the existing exhaustion theorem identifies `sup_A ι(A)` with the cardinal
of the right-zero set, proving (3).

## Lean

- `ArithmeticCastelnuovoSeveri/InwardDilationPreservesTheWindowIndex.lean`:
  `tendsto_W_indexInwardScale`, `hodgeDefectAt_eq_iSup_lt`.
- `CohomologyOfWindowsOfSpecZ/TheWindowIndexCountsCriticalLengths.lean`:
  `le_windowIndexCriticalLength_iff`, `windowIndex_eq_encard_criticalLengths`,
  `finite_criticalLengths_le`, `windowIndexCriticalLength_eq_top_iff`,
  `windowIndexCriticalLength_lt_top_iff`.

Both source files passed direct `lake --old env lean` checks and are imported by
their owning umbrellas. Eight transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`.
