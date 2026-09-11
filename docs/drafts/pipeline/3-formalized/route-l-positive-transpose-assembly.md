# Route L: positive transposition escapes under coherent additive assembly

Status: formalized; full scratch Lean, targeted final build, all-theorem axiom audit and repository lint passed.
Date: 2026-09-11.

Module: `GaloisForLFunctions.RHTower.XiGammaSixWoldJordanTransposeRepair`.

## Target and exact source

One complete coherent repair of the genuine fixed-left normalized row cannot
remove its anchor mass while preserving nonnegative real edge parts. This
audit tests whether that retention survives finite additive assembly of
complete coherent packets. It uses the same literal Big-Witt row, not a
replacement averaging source.

Let `T` reverse the two distinct prime labels of each ordered edge. It is a
linear permutation of finite packets. For the original raw row `v_(a,n)`, put
`p=nthPrimeSubtype a`, and let `r_(a,n)` denote its existing trace normalization.
The repaired row is explicitly `g_(a,n)=T(r_(a,n))`.

## Exact formal statements

For every finite packet `f`:

- `T` preserves its algebraic one-leg trace and ambient admitted Hilbert norm.
- `f-T(f)` is exactly a finite sum of complete two-point coherent packets:
  `sum_(i in support f) R(conj(f(i))*1_(left(i)), {left(i),right(i)})`.

For the genuine normalized row at every finite stage:

- Every coefficient of `g_(a,n)` is a nonnegative real scalar.
- Its trace is one.
- Its anchor marginal at `p` is exactly zero.

As `n` grows:

- Its ambient limit is zero and its one-leg graph limit is the same nonzero
  singular vector as the original row.
- Its existing reciprocal energy tends to zero for every real `A`.
- Every positive bounded left-prime range loses its entire mass.
- The repair `r_(a,n)-g_(a,n)` is eventually unequal to any single complete
  coherent packet, allowing arbitrary profiles and finite sets.

The source energy mechanism is an exact positive quadratic identity:

`E_A(T(v_(a,n))) = A*p*||admission(v_(a,n))||^2`.

Consequently, with the original normalized row mass `M_n`,

`|E_A(g_(a,n))| <= |A|*p*||rawHorizon||^2/M_n -> 0`.

This uses the existing uniform raw-horizon norm bound and divergence of the
actual raw row mass. It introduces no numerical calculation, prime counting
asymptotic, or new summability assumption.

## Dependency-closed paper proof

The swap is an involution of ordered distinct-prime indices. Reindexing the
finite coefficient sum preserves trace, and reindexing the sum of squared
absolute coefficients preserves the admitted Hilbert norm. A complete coherent
packet on the two labels of one edge is exactly that edge minus its reverse,
with the conjugate scalar included in its profile. Summing these identities
over `support(f)` gives the exact additive decomposition.

Transposition preserves the original row's positive coefficients. Every
transposed edge has right label `p` and therefore left label different from
`p`; the anchor marginal vanishes. Trace preservation and norm preservation
transfer the original ambient and graph limits directly.

For each raw row coefficient `w_k=1/(p*q_k)`, the reversed reader contributes
`(A/q_k)*w_k=A*p*w_k^2`. Finite support identifies the admitted squared norm
with `sum_k w_k^2`. Summing the term identity proves the raw quadratic law.
Normalization divides it by the actual row mass. The existing uniform bound
on the raw norm gives the displayed vanishing majorant. The earlier positive
head-mass inequality, applied with `A=1`, proves escape from every bounded
left-prime range.

Finally, a single complete coherent representation of the repair would make
this positive repaired row satisfy the previous retention bound. For all
sufficiently large `n`, that bound makes its anchor marginal at least
`1-1/(p*M_n)>0`, contradicting the exact zero anchor marginal. Thus finite
additive assembly strictly leaves the one-complete-packet class in this source.

## Failed extension and positive survivor

The C11 retention law does not extend to arbitrary finite sums of complete
coherent packets with different finite sets. The positive survivor is the
explicit transposition law, its quadratic energy identity, all source limits,
and the eventual failure of joint complete coherence.

Local consistency of each summand does not establish joint consistency of the
aggregate. Positivity, trace normalization and the singular graph limit still
allow the prime marginal and fixed readout to escape under this enlargement.
This does not identify the original fixed physical marginal with its transposed
one, establish cyclic-to-physical agreement, force `A=0`, or prove RH.

The next candidate tests quantitative negative-mass costs for an approximately
positive but jointly complete coherent repair:
[active research card](../1-in-progress/route-l-source-selected-completion-attack.md).

## Verification

- `lake env lean /tmp/route_l_transpose_repair.lean` — passed.
- `lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanTransposeRepair` — passed.
- `lake env lean /tmp/route_l_transpose_repair_axioms.lean` — all 21 theorems use only `propext`, `Classical.choice` and `Quot.sound`.
- `scripts/formal_tools.py lint` — passed.
- Scoped whitespace checks passed. All owned Lean build/check processes completed.
- `RHTower.lean` import is wired; no full or umbrella build ran.
