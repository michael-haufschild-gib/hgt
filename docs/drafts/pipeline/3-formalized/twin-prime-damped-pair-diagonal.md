# A quantitative damping diagonal for prime pairs

- **ID:** twin-prime-damped-pair-diagonal
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE
- **Source:** [RH-language synthesis](../1-in-progress/twin-prime-rh-language-reformulation.md)
- **Statement:** The actual damped divisor response divided by damping approximates von Mangoldt with error at most `ε log²(n)/2`. At `ε=log⁻⁴(X+h+2)`, the finite pair error is at most `1/log(X+h+2)` and tends to zero, including squarefree projection onto genuine prime pairs.

## Purpose and status

This pays the passage from a shrinking-damping physical pair response to the actual prime-pair observable. It supplies no lower bound for that response. The signed finite-horizon/period discrepancy remains the analytic target. No novelty claim is made for this elementary approximation.

The previous goal turn made progress: it read the twelve requested programmes, checked the source and singular-series declarations, and recorded a complete paper reduction with a specific open discrepancy. It did not prove the goal.

## Dependency-closed paper proof

Set `τ_ε(n)=∏_{p∣n}(1-p^{-ε})` and `r_ε(n)=τ_ε(n)/ε`, with `ε>0` and `n≥2`. Every factor lies in `[0,1]`, and retaining one prime factor gives `0≤r_ε(n)≤log n`.

If `n=p^a`, `r_ε(n)=(1-exp(-ε log p))/ε`. The inequalities
`1-u≤exp(-u)≤1-u+u²/2` for `u≥0` give
`0≤log p-r_ε(n)≤ε log²p/2≤ε log²n/2`.

Otherwise choose distinct primes `p,q` dividing `n`. Keeping these two factors gives
`0≤τ_ε(n)≤ε² log p log q≤ε² log²n/4`, because `pq∣n`. Here `Λ(n)=0`. Hence in both cases

`|r_ε(n)-Λ(n)|≤ε log²n/2`.

For `2≤n≤X`, put `m=n+h`, `L=log(X+h+2)`, with `h≥0`. The exact product difference is
`r(n)r(m)-Λ(n)Λ(m)=(r(n)-Λ(n))r(m)+Λ(n)(r(m)-Λ(m))`.
All four nonnegative factors are bounded by `L`; its absolute value is at most `ε L³`. Sum over `[2,X]`, whose size is at most `X`, and divide by `X`. If `X=0` the defined average is zero, and if `X=1` the interval is empty. Thus the finite estimate covers every natural horizon.

Multiplying each summand by `μ(n)² μ(n+h)²∈{0,1}` preserves the bound and projects the comparison sum exactly onto prime pairs. Choosing `ε=log⁻⁴(X+h+2)` makes the bound exactly `1/log(X+h+2)`, which tends to zero for every fixed natural gap. The sharp `log(X+h)` variant and the unprojected proper-prime-power removal estimate remain paper deductions on the parent card; they are not additional claims of this certificate.

All estimates are unconditional; positivity of damping and the integer ranges are genuine object side conditions.

## Lean certificate

Leaf: [DampedPairDiagonal.lean](../../../../formal/GaloisForLFunctions/twin-prime/DampedPairDiagonal.lean).

- `normalizedDampedResponse_exp_error (t : ℝ) (n : ℕ)`: point error at damping `exp(-t)` and index `n+2`.
- `dampedPairDiagonal_error (X h : ℕ)`: explicit finite error against von Mangoldt pairs.
- `primePairDiagonal_error (X h : ℕ)`: explicit finite error against the actual prime-pair log average.
- `dampedPairDiagonal_tendsto (h : ℕ)`: unprojected difference tends to zero.
- `primePairDiagonal_tendsto (h : ℕ)`: projected difference tends to zero.

These five capstones have no proposition-valued premises. The damping schedule
is defined explicitly and its positivity is proved. They do not assert that the
prime-pair average itself converges, has a positive lower bound, or is nonzero
in every tail.

The foreground leaf command passed:

`lake --old env lean GaloisForLFunctions/twin-prime/DampedPairDiagonal.lean`

All five `#print axioms` audits returned only
`[propext, Classical.choice, Quot.sound]`. Temporary audit directives removed;
the checked definitions and proofs were unchanged.

## Gates

- [x] Exact statement and complete paper proof.
- [x] Corpus-first dependency search; product formula and exponential estimate located.
- [x] Lean leaf and standard-axiom audit.
- [x] Umbrella and index integration; umbrella not built.

## Log

- 2026-10-23 — Began formalizing the quantitative physical diagonal. Infinitude remains unproved; no analytic lower-bound premise is to be introduced.
- 2026-10-23 — Certified both finite diagonal errors and both zero-error limits, including exact projection onto prime pairs. All five capstones passed the foundational axiom audit. No lower bound or twin-prime infinitude theorem claimed.
