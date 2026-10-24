# Uniform leading matrix for moving Vaughan cutoffs

- **ID:** uniform-vaughan-gram-leading-term
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** For every positive damping, the normalized Vaughan Gram differs from the outer product of its explicit cutoff-dependent means by a quantity tending uniformly to zero over both cutoffs.
- **Novelty status:** Structural specialization of uniform dominated convergence. No external novelty claim.

## Exact statement

Use the existing vector `c(U,V)=pmPronicVaughanMean ε U V`. For every `ε>0` and
`i,j∈Fin 5`,

`sup_(U,V) |G_ij(T;U,V)/T-c_i(U,V)c_j(U,V)| → 0`.

The supremum is notation for the uniform quantified bound; no extended-real supremum
is needed in Lean. Consequently, whenever both cutoff schedules tend to infinity,

`G_ij(T;U(T),V(T))/T → ρ² v_i v_j`, where `v=(1,1,-1,0,-1)`.

In particular `G(N²;N,N)/N²→ρ² vvᵀ` and `D(N²;N,N)/N²→4ρ²`.
This describes the leading matrix at the actual square-root cutoffs. It gives no power
saving for the smaller signed residual.

## Uniform floor-mean lemma

Let `a_θ(d)` be any family with `|a_θ(d)|≤b(d)`, `b(d)≥0`, and
`Σ_(d≥1)b(d)/d<∞`. For `n≥1`, set

`q_n(d)=floor(n/d)/n`, `A_θ=Σ_(d≥1)a_θ(d)/d`,
`Δ_b(n)=Σ_(d≥1)b(d)/d-Σ_(d≥1)b(d)q_n(d)`.

Since `0≤q_n(d)≤1/d`, absolute convergence gives

`|Σ_d a_θ(d)q_n(d)-A_θ|≤Σ_d b(d)(1/d-q_n(d))=Δ_b(n)`.

The unsigned divisor mean theorem gives `Δ_b(n)→0`, independently of `θ`.
All sums with `q_n` are finite. The zero index contributes zero throughout. Thus the
lemma does not assume uniformity of pointwise convergence; it proves it from one
summable majorant. Existing input: `pm_tendsto_divisor_average`.

## Application to the five pieces

For the first two pieces use `a_U(d)=μ(d)d^(-ε)1_(d≤U)` and `b(d)=d^(-ε)`.
The small-small piece has coefficient

`a_(U,V)(d)=-d^(-ε)Σ_(abk=d,a≤U,b≤V)μ(a)μ(b)`.

Its absolute value is at most `d^(-ε)τ(d)^2`: a triple `(a,b,k)` is determined by
the pair of divisors `(a,b)`, so there are at most `τ(d)^2` triples. The majorant
divided by `d` is summable by `summable_divisor_sq_rpow` at exponent `(1+ε)/2`.
The coefficient's mean is the already proved fixed-cutoff limit
`-Z A_U A_V`, by uniqueness of limits. No new infinite convolution evaluation is
needed. Here `Z=ζ(1+ε)` and `A_U=Σ_(d≤U)μ(d)d^(-1-ε)`.

The pole piece has error at most `1/(2n)` from its mean `-ρ`. The exact five-piece
identity and `I(n)/n→0` determine the both-large error. Thus there exists one
nonnegative scalar sequence `e(n)→0` such that, for all cutoffs and all five indices,

`|p_i(n;U,V)/n-c_i(U,V)|≤e(n)` for `n≥1`.

The means are uniformly bounded: `|A_U|≤Z`, and the explicit formulas bound all five
by `B=1+ρ+2Z+Z³`. Therefore

`|p_i(n)p_j(n)/(n(n+1))-c_i c_j|`
`≤e(n)(2B+e(n))+B²/(n+1)`.

The scalar right side tends to zero and is independent of the cutoffs. Its Cesàro
mean tends to zero, proving the uniform Gram law.

Finally absolute convergence gives `A_U→ρ` as `U→∞`. Substituting `Zρ=1` in the
explicit five means gives `ρ(1,1,-1,0,-1)`. Composing the uniform estimate with
arbitrary divergent cutoff schedules proves the moving-cutoff corollaries. The
square-root case agrees with the independently proved exact vanishing of row and
column 3 throughout the horizon `N²`.

## Audit and status

The corpus has the fixed-cutoff classification, exact square-root vanishing,
absolute reciprocal tails, and divisor mean theorem. The initial uniform-mean search
did not surface the stated uniform five-piece Gram law. This is an internal
structural extension, not a claimed new analytic estimate.

Further corpus inputs checked in source: `MTUniformDivisorBounded.arithmeticFunction_mul`
adds the two divisor exponents plus one, so three unit-bounded factors have the required
square-divisor majorant. `cubeFibre_card_le_divisors_sq` supplies the equivalent finite
product-fibre counting argument. `pmPowerDampedReciprocalTail_le_half_exponent_moment`
gives an explicit alternative tail bound for the two small legs.
The directly applicable real-valued interface is
`norm_mul_apply_le_divisors_pow_add_succ` in `Sieve/HeathBrownDyadicCoefficientBound.lean`;
two applications with unit-bounded factors give exponent two. The same module already proves
`norm_truncatedMoebius_le_one`.

Paper proof dependency-closed. Lean implementation has not started. The full Q-I task
remains open. Formalization should retain the uniform quantifiers and discharge the
coefficient majorants, rather than adding them as assumptions to the arithmetic result.

## Log

- 2026-10-25 — Strengthened the fixed-cutoff classification by a common summable majorant.
