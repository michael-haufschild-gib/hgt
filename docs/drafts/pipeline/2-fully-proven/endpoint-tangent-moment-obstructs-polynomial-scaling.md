# Endpoint tangent moment forces a surviving singular shift

- **ID:** B130-endpoint-tangent-moment
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean in progress)
- **Source:** [Analytic prime smoothing](../3-formalized/universal-moving-branch-for-analytic-prime-smoothing.md).

## Statement

Let `Ψ` be analytic on a disc of radius `R>1`, with `Ψ(0)=1`,
`Ψ(1)=-1`, and `Re Ψ′(1)=0`. Write `Ψ(z)-1=Σ b_k z^k`.
Then some `k≥1` has `Re b_k>0`. The profile

`Q(w)=ζ(2)exp(-Σ b_k log(w+k))`, `Re w>0`,

admits no entire extension, hence agrees with no polynomial there.
Every finite real affine average of normalized unimodular analytic
profiles satisfies these conditions, including averages whose first
imaginary Taylor coefficients cancel.

## Proof and positive survivor

Taylor convergence on a larger disc permits differentiation at one:
`Σ b_k=-2`, `Σ k b_k=Ψ′(1)`, with absolute convergence of both sums.
If every `Re b_k≤0`, the nonpositive summands `k Re b_k` have sum zero,
so every nonconstant `Re b_k=0`. This contradicts `Σ Re b_k=-2`.
Choose `k≥1` with `Re b_k>0`.

On the connected domain `Re w>-(k+1), Im w>0`, continue `Q` as

`Q_{k+1}(w) exp(-Σ_{j≤k} b_j log(w+j))`,

where `Q_{k+1}` is the normally convergent logarithm tail. This agrees
with `Q` on the right half-plane. Along `w=-k+it`, `t↓0`, remove its
`k`th factor. The remaining unit converges to

`B_k=Q_{k+1}(-k) exp(-Σ_{j<k} b_j log(j-k)) ≠ 0`.

The principal logarithm is continuous from the upper half-plane at
negative real numbers. Consequently

`Q(-k+it) exp(b_k log(it)) → B_k ≠ 0`.

But `|exp(b_k log(it))|=t^(Re b_k) exp(-Im b_k·π/2)→0`.
An entire extension would be bounded at `-k`, contradicting this limit.
This identifies a specific surviving singular shift, beyond merely
excluding polynomial scaling.

For a unimodular profile, differentiating `|Φ(x)|²=1` at `x=1` from
the left, with `Φ(1)=-1`, gives `Re Φ′(1)=0`. Real affine averaging
preserves this derivative condition and the two endpoint values.

## Stronger necessary endpoint bound

For any normalized analytic `Ψ`, existence of an entire extension of
`Q` forces `Re Ψ′(1)≤-2`. Indeed, an entire extension excludes every
positive-real coefficient by the shifted singularity argument. For
`k≥1`, nonpositive `Re b_k` gives `k Re b_k≤Re b_k`. Summing yields
`Re Ψ′(1)≤Σ Re b_k=-2`. Thus every endpoint derivative with real part
strictly greater than `-2` is obstructed, beyond the tangent-zero class.
Corpus search found no matching bound. The affine profile `1-2z`
suggests equality is attainable; that explicit profile calculation is
not part of the present formalized claim.

## Scope

This is a theorem about the canonical profile of the mean Taylor
coefficients. An actual arithmetic mixture still needs its own
shifted-prime expansion and regular-part control. B130 remains open.
No matching obstruction was found in the corpus. External novelty
has not been assessed.

## Next candidate

`Φ±(z)=1-4z²+2z⁴ ± 2iz(1-z²)√(2-z²)` should give normalized
unimodular profiles whose mean has `b₂=-4`, `b₄=2`. Its expected
profile is `ζ(2)(w+2)⁴/(w+4)²`: the first shift is a zero, the later
shift a pole. The pair and its arithmetic realization are unformalized.
