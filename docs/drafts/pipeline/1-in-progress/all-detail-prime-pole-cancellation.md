# Prime–pole cancellation uniform over all Haar details

- **Stage:** 1-in-progress
- **Type:** CANDIDATE; paper argument, Lean formalization incomplete.
- **Parent:** SC arithmetic mixed-source control.

Let `R(Y,a,b)` be the literal full prime-window coupling minus both mixed
pole terms, divided by `√Y`. Set `m_a=haarMass(a)` and
`w_b=logCellWidth(b)`, the original squared Hilbert masses.
The target is an absolute constant `C>0` such that, for all sufficiently
large natural `Y`, every

```text
M ≤ exp(√log Y/184320000),   X∈ℕ,
Σ_{a=1}^X m_a d_a² ≤ 1,     Σ_{b=1}^M w_b q_b² ≤ 1
```

satisfies

```text
|Σ_{b=1}^M q_b Σ_{a=1}^X d_a R(Y,a,b)|
  ≤ C exp(−√log Y/92160000).
```

There is no restriction on the detail horizon `X`. The same estimate
should hold for the literal all-prime source at every common horizon `N`
with `X≤N` and `Y(M+1)≤N+1`. Coefficients are real.
The `√Y` normalization remains; this is not a complete Weil index bound.

## Paper argument

Support restricts the full trace to prime powers
`m≤2Y(b+1)e^(−u)`. Weighted Chebyshev gives
`0≤T_(Y,b)(u)/√Y≤4C₀√(2b+2)e^(−u/2)`.
The unsigned Haar contracting moment is at most `2m_a/√(2a)`.
Both signed pole moments satisfy the same bound, while the coarse
contracting moment has absolute value at most two. Consequently

```text
R(Y,a,b)² ≤ C₁(b+1)m_a/[a(a+1)].
```

Weighted Cauchy–Schwarz, `w_b≥1/(b+1)`, and the telescoping pronic tail give

```text
|Σ_{b=1}^M q_b Σ_{a=A+1}^X d_a R(Y,a,b)|²
  ≤ C₁(M+1)³/(A+1).
```

For the remaining rows, unit mass gives
`|d_a q_b|≤7(A+1)(M+1)`. The existing growing-packet theorem bounds their
sum by this coefficient bound times `C₂ exp(−√log Y/7680000)` whenever
`A≤exp(√log Y/23040000)` and `M≤A`.

Put `r=1/184320000`, `t=√log Y`, and `A=⌊exp(8rt)⌋`.
Natural `M≤exp(rt)` implies `M≤A`. The finite block is bounded by
`28C₂ exp(−15rt)`; the tail square is at most `8C₁ exp(−5rt)`.
Their sum is at most `(28C₂+8C₁+1)exp(−2rt)`.
Exact prime support identifies every admissible common-horizon source
with this same matrix remainder.

## Rank-one consequence to formalize

Write `H_±(d)=Σ_a d_a∫h_a(u)e^(±u/2)du` and
`V_+(q)=Σ_b 4q_b(√(2b+2)−√(2b))`. The same uniform bound should give

```text
|Σ_b q_b Σ_a d_a C_Y(a,b)/√Y − H_−(d)V_+(q)|
  ≤ (C+16) exp(−2r√log Y).
```

Here `C_Y` is the literal full prime-window coupling. The exact opposite
pole is `(2/Y)H_+(d)Σ_b q_b∫q_b^cell(u)e^(−u/2)du`.
The existing Haar pole theorem gives `|H_+(d)|≤1`; unit coarse mass gives
an absolute bound `2(M+1)²` for the latter sum. Thus the opposite pole is
at most `4(M+1)²/Y≤16 exp(−2r√log Y)` for large `Y`.
This is a rank-one approximation of the normalized mixed source, without
a sign assertion for the complete Weil form.

## Audit

Corpus search found fixed-family and growing-square cancellation, the
pointwise window limit, and the bounded Haar pole functional; no all-detail
Hilbert operator estimate was found. The mass identities are already
proved by `integral_haarSectionProfile_sq` and `inner_coarseAtom`.
`fullPrimeWindowTrace_div_sqrt_le_exp` in `FullPrimeWindowTraceDecay.lean`
proves the refined trace bound. `FullPrimeWindowHaarDecay.lean` proves
the unsigned Haar moment and normalized full-prime row bounds. Their direct
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The joint row estimate and
`exists_fullPrimeWindowRemainder_hilbert_tail_bound` in `PrimeWindowRowTails`
pass direct audits with the same standard axioms. The growing-coarse
operator estimate and rank-one consequence remain unformalized.
External priority is unchecked.
