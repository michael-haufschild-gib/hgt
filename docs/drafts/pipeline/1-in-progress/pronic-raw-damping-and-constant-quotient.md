# Raw pronic damping and the constant quotient

- **ID:** pronic-raw-damping-constant-quotient
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper), Lean and final novelty audit pending
- **Source:** BVI README §5, topic 6; THIM–BVI programme candidate 003.
- **Statement:** The literal raw arithmetic transition is compact on the pronic Hilbert space
  at every positive damping and forms a strongly continuous semigroup including zero.
  Its quotient by constants survives at all dampings; entrance centering does not admit
  even a closable extension at or below half damping.

## Scope and normalization guard

Write H for sequences on positive integers with norm squared
`Σ_n |b(n)|²/[n(n+1)]`, and P_η for the existing literal kernel in
`ArithmeticDampingTransitionKernel`. This card concerns P_η acting on b itself.

The arithmetic source read by the Markov chain is the **mean** of its prefix, not the prefix.
The existing `arithmeticDampingCenteredMean_eq` identifies it with A_η(n)/n.
Consequently the actual receiver is
`Σ_n A_η(n)²/[n(n+1)] = Σ_n (n/(n+1)) |A_η(n)/n|²`.
It is NOT the H norm of that mean. Compactness on H below therefore supplies an operator
version and a precise quotient survivor, not a receiver estimate or an RH implication.
No change to the read-only README is made.

## Prior-work and novelty search

- Hybrid searches for raw arithmetic damping, bounded pronic transitions, compact pronic
  kernels, and quotients by constants found the finite kernel, c₀ centering, entrance tail,
  and existing pronic dual threshold, but no bounded/compact raw H lift.
- `PronicDualNormOfTheEntranceLaw.lean` and its separate card are pre-existing work: do not
  claim its threshold or reciprocal-observable survivor as new credit.
- The existing dilation Dirichlet-form/Hardy card concerns the prefix receiver and dilation
  block differences, not this raw mean-space transition. Its normalization remains distinct.
- Search found `RHTower.pmPowerDampedDivisorCoeff_nonneg` and `_le_one` in
  `PMPowerDampedMobiusDivisorHaar.lean`; their source proofs were inspected.
- The new package would count once: compact raw lift, quotient interpretation, and exact
  nonclosability witness belong together. Numerical constants and support lemmas do not count.

## Paper proof [PROVED HERE; Lean verification pending]

Put `F_η(m)=pmPowerDampedDivisorCoeff η m`, `U_η(N)=Σ_{m≤N} F_η(m)`, and
`w(n)=1/[n(n+1)]`. For η≥0 the corpus proves `0≤F_η≤1`, row positivity and unit mass,
the finite semigroup law, and P₀=Id. All indices below are positive.

### Weighted column bound

Split the literal kernel P=L+B, with

`L(n,k)=k^(1−η)/n · Σ_{m: km≤n<(k+1)m} F_η(m)`,

`B(n,k)=k/n · (k^(−η)−(k+1)^(−η)) U_η(floor(n/(k+1)))`.

Both terms are nonnegative. This is exactly the difference of the two divisor prefixes,
not a comparison with a substituted source. For L, Tonelli and its exact fibre give

`Σ_n w(n)L(n,k)
 = k^(1−η) Σ_m F_η(m) Σ_{n=km}^{(k+1)m−1} 1/[n²(n+1)]
 ≤ k^(−2−η) Σ_m F_η(m)/m²
 ≤ 2 k^(−2−η)
 ≤ 4 k^(−η) w(k)`.

There are m integers in the fibre, each n≥km, so its inner sum is at most
`m/(km)³=1/(k³m²)`. The elementary bound `Σ_{m≥1}m^(−2)≤2` follows from
`1/m²≤1/[m(m−1)]` for m≥2 and telescoping.

For B, the elementary derivative integral gives
`0≤k^(−η)−(k+1)^(−η)≤η k^(−η−1)` for η≥0. Also U_η(N)≤N. Hence B vanishes
for n≤k and satisfies `B(n,k)≤η k^(−η)/(k+1)` otherwise. Since
`Σ_{n≥k+1}w(n)=1/(k+1)`,

`Σ_n w(n)B(n,k)≤η k^(−η)/(k+1)²≤η k^(−η)w(k)`.

Together,

`Σ_n w(n)P_η(n,k)≤(4+η) k^(−η) w(k)`.

### Boundedness, compactness, and strong continuity

Jensen for each stochastic row followed by Tonelli yields
`‖P_η b‖_H²≤(4+η) Σ_k k^(−η)|b(k)|²w(k)≤(4+η)‖b‖_H²`.
Each output coordinate is a finite sum, so this defines the literal operator for every b∈H.
For Π_N, truncation to states k≤N,

`‖P_η(I−Π_N)‖²≤(4+η)(N+1)^(−η)`.

P_ηΠ_N has finite rank. Thus P_η is compact for η>0. No compactness is asserted at η=0.
The finite lower-triangular composition identity applies to each coordinate and proves the
operator semigroup law without an interchange of conditionally convergent sums.

For a coordinate vector e_k, each P_η(n,k) tends to δ_{nk} as η↓0: the kernel is a finite
sum of continuous real powers and P₀=Id. The entries lie in [0,1], so dominated convergence
against the summable weights w gives `P_η e_k→e_k` in H. The operator bound is locally
uniform for 0≤η≤1, and finite-support vectors are dense in H. Therefore P_η→Id strongly.
The semigroup law gives strong continuity at every nonnegative time.

### The positive quotient survivor

Constants lie in H with `‖1‖_H=1`, and P_η1=1. The first coordinate is fixed as well:
`(P_η b)(1)=b(1)`. Thus `H₀={b∈H:b(1)=0}` is invariant, is boundedly isomorphic to
H/modulo constants through `b↦b−b(1)1`, and carries the compact positive-time restriction
of P_η with identity at zero. It is a strongly continuous semigroup.

On its original domain the entrance-centered operator C_η=P_η−e_η(·)1 has exactly the
same quotient action. Equivalently `Q_η b=P_η b−b(1)1` is a bounded compact representative
on H for η>0, restricting to that semigroup on H₀. This uses a fixed finite-coordinate
centering, not an unbounded entrance evaluation.

### Exact centering obstruction and its witness

The existing entrance formula is
`e_η(k)=ρ_η k[k^(−1−η)−(k+1)^(−1−η)]`, with ρ_η>0. Integrating the derivative
on [k,k+1] bounds e_η(k) above and below by positive η-dependent multiples of k^(−1−η).
Hence `S_N=Σ_{k≤N}e_η(k)²/w(k)` diverges exactly when 0<η≤1/2; above half damping
its infinite limit is finite. This is the existing dual threshold, not a new claim of novelty.

For 0<η≤1/2 take the finite-support row
`b_N(k)=e_η(k)/(w(k)S_N)` for k≤N, zero otherwise. Then
`e_η(b_N)=1` and `‖b_N‖_H²=1/S_N→0`. The newly bounded raw P_η gives
`C_η b_N=P_η b_N−1→−1` in H. Thus the graph of entrance centering is not closable,
already on finite-support inputs. Above half damping e_η is a bounded H functional;
subtracting its rank-one operator from compact P_η gives a compact H extension of C_η.

The strongest positive survivor is the compact raw semigroup and its constant quotient,
not merely the negation of an entrance-centered lift. Its relationship to critical energy
retains the normalization guard above.

## Lean status and next obligations

No Lean implementation yet; not counted. Required exact outputs: weighted column bound,
literal bounded H operator, norm-convergent finite-column approximants, compactness,
strong continuity, quotient identification, and nonclosability witness. The spectrum draft's
stale dependency branch still prevents importing the actual transition in a new audit without
the previously requested artifact-regeneration override. Do not replace the literal transition
by a postulated bounded operator, count the known entrance threshold again, or conflate mean
and prefix Hilbert weights.

## Log

- 2026-10-22 — Corpus search, normalization check, exact fibre decomposition, and complete
  paper mechanism recorded. Lean audit and final novelty audit remain open.
