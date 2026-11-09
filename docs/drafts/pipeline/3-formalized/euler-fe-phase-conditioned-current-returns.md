# Prime-phase returns of the continued rough current

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Euler–FE transport and exact-event theory.

## Statement

Under `¬AAL`, one regular high line `1/2<σ<Re ρ<1` satisfies:
for every cutoff `Y`, finite `P⊆primesBelow Y`, prescribed unit phases `α_p`,
and `η,δ>0`, every sufficiently high dyadic window `[T,2T]` contains `t` with

`|p^(it)−α_p|<η` for every `p∈P`, and

`|ζ′/ζ(σ+it)+Σ_{p<Y}log p/(p^(σ+it)−1)|² < A_Y(σ)+δ`.

Here `A_Y(σ)` is the complete rough von Mangoldt square mass, tending to zero
as `Y→∞`. The same line and its zero-free height serve all choices; the
window threshold may depend on them. In particular, qualifying heights are
unbounded. There is no tail truncation or phase-return premise.

## Proof

Write `J_Y(t)=ζ′/ζ(σ+it)+Σ_{p<Y}log p/(p^(σ+it)−1)`.
Use the smooth box probe

`R_k(t)=Π_{p∈P}Σ_{j=0}^k α_p^(−j)p^(ijt)`.

For arbitrary finite exponent sets, unique factorization identifies each
prime monomial with a distinct smooth integer. The finite integer-frequency
mean-value theorem therefore gives the exact product coefficient energy on
escaping dyadic windows. Applied to this box, its mean square is
`D=(k+1)^|P|>0`.

Multiplication by `p^(it)−α_p` telescopes the corresponding factor to two
boundary monomials of unit coefficient norm. Their exponents `0` and `k+1`
are distinct. Thus the weighted squared phase-error mean is exactly
`2D/(k+1)`. The continued-current conditioned mean gives weighted rough
energy exactly `D A_Y(σ)` for each fixed probe.

Put `C=A_Y+δ`, `λ=C/η²>0`, and
`cost(t)=|J_Y(t)|²+λΣ_{p∈P}|p^(it)−α_p|²`. Choose `k` with
`2λ|P|/(k+1)<δ`. Then

`T⁻¹∫_T^(2T)|R_k|²(cost−C) → D(A_Y+2λ|P|/(k+1)−C)<0`.

The current is continuous above the regular height; clipping below it
justifies integration without changing high windows. If `cost≥C` everywhere
in a high window, integral monotonicity contradicts its negative weighted
mean. At the resulting point `cost<C`, nonnegativity gives `|J_Y|²<C` and
`λ|p^(it)−α_p|²<C=λη²` for every prescribed prime. These are the claimed
strict bounds.

The small-prime head includes primes outside `P`; their phases remain free.
Even controlling every prime below `Y` does not approximate a fixed low
continued profile: that finite Euler head itself changes with `Y`.
Thus the law supplies joint arithmetic returns, not exact zero transport.

## Formalization

The full conditioned current mean is formalized in
`../3-formalized/euler-fe-continued-conditioned-rough-mean.md`, including
the regular high line needed for integration.

`EulerFETransportTheory/TheContinuedCurrentReturnsWithItsPrimeHead.lean`:

- `tendsto_primePacketPolynomial_mean`.
- `tendsto_primePhaseBox_phase_error_mean`.
- `not_asymptoticAbscissaLaw_has_dyadic_primePhase_returns`.
- `not_asymptoticAbscissaLaw_has_joint_primePhase_returns`.

Direct `lake --old env lean` checking passes. All four transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
