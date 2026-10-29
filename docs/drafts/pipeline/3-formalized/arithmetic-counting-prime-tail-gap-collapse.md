# Joint prime flips above every fixed cutoff have vanishing greatest gaps

- **ID:** ACP-PRIME-TAIL-GAP-COLLAPSE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../3-formalized/arithmetic-counting-finite-prime-secular-gap.md
- **Sources:** exact finite-prime secular criterion and inclusion law; conductor energy bound; Cauchy condensation and harmonic divergence
- **Statement:** For every natural B, the greatest gaps of simultaneous flips at primes B<p<=Q tend to zero as Q tends to infinity. Arbitrarily far out, individually maximal prime flips can have arbitrarily small positive joint greatest gap.

## Exact endpoints

Put `F_(B,Q)={p prime:B<p<=Q}` and let delta_F be the attained greatest
finite-prime hyperplane gap. Then

`lim_(Q->infinity) delta_(F_(B,Q))=0`.

Every finite stage still satisfies delta_F>0. For every B and epsilon>0
there is a nonempty finite set F of primes, each greater than B and at
least eleven, such that every singleton has greatest gap 2 log 2 while
`0<delta_F<epsilon`.

The auxiliary arithmetic theorem is divergence of
`sum_n 1/(m_n log m_n)` for `m_n=M(n+2)+1` and every positive natural M.
It is classical series analysis; the new application is the joint gap
law of the actual prime matrices.

## Closed proof

### 1. A uniform counting supply of rough conductors

Fix B and put M=B!>0. Every m_n=M(n+2)+1 is at least two. If a prime
p<=B divided m_n, it would divide M and therefore also one, a contradiction.
Thus every prime divisor of m_n exceeds B. Once Q>=m_n all its prime
divisors belong to F_(B,Q), so m_n is a supported conductor. The map
n to m_n-2 is injective; subtracting two merely reindexes the positive
conductor tail beginning at conductor two.

### 2. Divergent reciprocal-logarithmic mass

The positive sequence f_M(n)=1/(m_n log m_n) is decreasing: both m_n
and log m_n increase. For q=2^k and A=3M+1,

`m_(2^k)<=A*2^k`,

`log m_(2^k)<=log A+k log 2<=(A+1)(k+1)`.

The first inequality uses 2^k>=1. The second uses log A<=A-1 and log 2<=1.
Consequently

`2^k f_M(2^k)>=1/(A(A+1)(k+1))`.

If f_M were summable, Cauchy condensation would make its condensed series
summable. Comparison and multiplication by the positive constant A(A+1)
would make the harmonic series summable, a contradiction. Nonnegativity
then makes the finite partial sums of f_M tend to positive infinity.

### 3. Each supported conductor pays this reciprocal mass

For m>=2 the supported normalized weight is
`w_F(m)=4^omega(m)/phi(m)>=1/m`, using phi(m)<=m and 4^omega(m)>=1.
The corpus theorem tameDifferent_le_log gives `D_m<=2 log m`; the first
excitation theorem gives `D_m>=2 log 2`. Hence, for 0<t<2 log 2,

`w_F(m)/(D_m-t)>=1/(2m log m)`.

All divisions have strictly positive denominators. This is a lower bound
on the actual counted secular summand, not a bound on a truncated substitute.

### 4. No fixed positive lower bound survives all prime cutoffs

Suppose delta_(F_(B,Q))>=epsilon>0 for every Q. Choose
`t=min(epsilon,2 log 2)/2`. The exact gap criterion gives

`sum_(m>=2) w_(F_(B,Q))(m)/(D_m-t)<=1/t`

for every Q. By step 2 choose an initial packet of m_n whose reciprocal-log
sum exceeds 2/t. Choose Q large enough to support the entire packet.
Step 3, injectivity of the conductor indices, nonnegativity and summability
bound half that packet sum by the full positive secular tail, hence by 1/t.
This contradicts the choice of packet. Therefore some finite cutoff has
gap less than epsilon.

### 5. Limit and individually maximal constituents

The prime sets increase with Q, so their greatest gaps decrease by the
proved inclusion law. They are nonnegative. The preceding arbitrarily
small value therefore gives convergence to zero.

For the final assertion use cutoff max(B,10) and target
min(epsilon,2 log 2). A set with gap below the ceiling cannot be empty:
the density bound for the empty set already equals the ceiling. Every
prime in the resulting nonempty set exceeds B and is at least eleven,
so the existing exact singleton theorem makes each individual greatest
gap maximal. The joint greatest gap remains positive and below epsilon.

## Quantifiers, scope and integrity

Each finite cutoff uses its own already proved exact secular criterion.
No integer-horizon limit is exchanged with the prime cutoff; no common
horizon bound is assumed. Pointwise convergence to a cofinite zero-gap sign
is not used to infer convergence of greatest gaps.

The proof supplies a qualitative limit. The sharper first energy moment
and proposed O_B((log Q)^(-3)) decay rate remain conjectures in
`../2-fully-proven/arithmetic-counting-finite-prime-energy-moment.md`.
Complete Weil positivity and the wider counting producer mechanisms remain
open. No numerical experiment or trusted computation is used.

## Formalization

`PrimeTailExhaustionHasVanishingGreatestGaps.lean` proves:

- `not_summable_progressionReciprocalLog`
- `tendsto_sum_progressionReciprocalLog_atTop`
- `exists_primeTailCutoff_gap_lt`
- `tendsto_primeTailGreatestGap_zero`
- `exists_maximal_prime_flips_with_small_joint_gap`

All five transitive axiom audits contain only `propext`, `Classical.choice`
and `Quot.sound`. The canonical installed-source check exited zero with no
diagnostics. Exact commands, source hash and actual axiom output are saved in
`arithmetic-counting-prime-tail-gap-collapse-audit.txt`. No olean was built:
no subsequent file yet imports this leaf. The umbrella imports the source.

- [x] Dependency-complete paper proof.
- [x] Five Lean endpoints and transitive axiom audit.
- [x] Canonical audit, umbrella wiring, durable evidence and cleanup.
