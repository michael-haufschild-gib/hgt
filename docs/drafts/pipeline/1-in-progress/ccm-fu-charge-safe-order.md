# CCM-FU: exhaustive charge-safe order test

- Type: derived diagnostic for the unchanged full-source quadratic bound.
- Status: frozen screen and independent audit completed; all-cutoff source
  bound remains open. No numerical result is formalized as a theorem.
- Chain: actual divisor source → uniformly quadratic complete prime order →
  O(M) Abel bound → CCM-FU → RH. Frontier map read only.

## Exact question

The arity balance proves `sum J=D(P)-D_0+sum W`, with `W` the complete
copied-child square energy. Eight saved greedy histories had nonpositive
accumulated charge, but do not establish feasibility at other cutoffs.
Test whether some complete order satisfies both `Q(P)<=Q_0` and
`sum J<=0` at every prefix. This is a stronger derived condition, not RH
itself. Failure of one selected policy would not decide it.

## Source-pair reduction on paper

For original labels A and B, their coefficients interfere at P precisely
when `A symmetricDifference B` is contained in P. Consequently define
`K(T)=sum_(A triangle B=T) c_A c_B` and
`K_q(T)=sum_(A triangle B=T, q in A intersection B) c_A c_B`.
Then `Q(P)=sum_(T subset P)K(T)` and, for unprocessed q,
`W_q(P)=sum_(T subset P)K_q(T)`. Both are complete ordered pair sums.
Also `D(P)=sum_(q notin P)W_q(P)`: each retained square is counted once
per surviving prime. No sign is inferred from these identities.

For a fixed cutoff, retain the smallest accumulated W at each reachable
processed set P. Relax each unused-prime edge, accepting its successor
only if `Q<=Q_0` and `D+accumulated W<=D_0`. A larger accumulated W at
the same P cannot improve any continuation: subsequent edge costs and
state energies depend only on P. This dominance makes the dynamic program
exhaustive over all complete orders, without enumerating permutations.

## Completed results

Every cutoff from 2 through 48 admits a complete qualifying order in the
floating exhaustive screen. More strongly, at every tested cutoff every
subset with `Q(P)<=Q_0` is reachable with the additional prefix charge
constraint. Thus no tested below-ceiling state is separated from the
initial state by a necessary charge violation. This additional observation
is exploratory; it is not an all-cutoff or exact-arithmetic theorem.

At M=48 all 32,768 subsets were checked. Exactly 666 exceed the initial
raw-energy ceiling; all other 32,102 are reachable under both constraints.
The frozen independent audit checks the entire saved order at 80 digits:

`47,43,41,31,7,37,5,29,3,2,23,19,17,13,11`.

It has `Q_0=3.37779279505674529`, `D_0=3.94716608692011278`, final copied
cost `1.27400862737379798`, and final accumulated charge
`-2.67315745954631479`. The final head is `-0.91397916303658708`, whose
square is `0.83535791046506023`. Every prefix and every full cofactor charge
was independently reconstructed. Several raw-energy steps increase while
remaining below the initial ceiling; no stepwise-contraction claim is made.

Screen: four workers, 0.2180628404 seconds. Successful independent audit:
four workers, 0.0148053989 seconds. The first audit invocation stopped on
Python 3.8 lacking `int.bit_count`; replacing it with `bin(r).count('1')`
fixed compatibility without changing the protocol or selected witness.
All 99 remote script/result/array files were downloaded and SHA-256 checked.
The remote directory and owned processes were cleaned up.

The [full archive](../2-fully-proven/computations/ccm-fu-charge-safe-order-2026-09-08/README.md)
contains every state cost and predecessor, not only selected trajectories.

## What the proof attempt still lacks

The recurrence exhausts the finite ordering choice; it does not prove its
terminal state admissible at every cutoff. In particular, a theorem that
all below-ceiling states are reachable would still require an independent
proof that the complete signed head lies below that ceiling. Using its
admissibility as a premise would assume the desired arithmetic bound.

For a complete order, the copied-cost pair formula also identifies the
missing source information. A distinct original pair contributes once for
each common prime processed after all differing primes. Its diagonal
contribution is the initial arity cost. Hence total accumulated charge is
the ordered off-diagonal sum weighted by that common-prime count. Coprime
pairs have weight zero in every order, whereas all distinct pairs occur in
`S^2-Q_0`. An arithmetic comparison coupling these sectors, or a direct
signed-head estimate, is still required. This paper deduction uses the
literal finite pair expansion; no general sign follows from it.

The wide corpus search also found the already formal half-selection growth
obstruction: independent prime averaging cannot supply a uniform quadratic
ceiling. The Euler-deletion coprime-column theorems retain floor weights,
harmonic terms and later tails; none supplies their replacement by the
present Abel coefficients. No such transport is assumed. No new Lean
module or build was needed for this diagnostic; existing audits were not
repeated. The next task is analytic source cancellation, not a larger
confirmation screen or a new abstract reachability wrapper.

## Frozen experiment (executed unchanged)

- All integer cutoffs M=2 through 48, inclusive. No extension or new policy.
- Actual original source, using the unchanged earlier quotient-block source
  generator. Retain all squarefree indices and every prime below M.
- Complete pair kernels and subset zeta transforms; no random subsets,
  dropped cofactors, approximated pair counts or fitted weights.
- Four cutoff workers on supplied RunPod, one BLAS/OpenMP/MKL thread each.
  Internal deadline 90 seconds; outer timeout 100 seconds, no extension.
- Floating acceptance tolerance `1e-10 max(1,Q_0,D_0)`. Preserve minimum
  cost and predecessor at every reachable state, counts of rejected states,
  complete successful witnesses and full per-cutoff arrays.
- Validate every Q, D and unprocessed-prime W independently by literal
  fibre regrouping at every processed set in the screen.

The outcome is not predictable from the eight previous greedy paths or
the generic three-coordinate factor. A failing cutoff would eliminate
this proposed charge restriction at the numerical level, even if the
unrestricted raw-energy order remains possible. A pass proves neither
the all-cutoff condition nor the initial-logarithm or signed-head estimates.

## Frozen independent audit (executed unchanged)

Choose the smallest failing cutoff; if none fails, choose M=48. Reconstruct
coefficients from the original time sum at 80 digits using independent
trial factorization and the defining log-factorial/divisor-count defect.
On failure, repeat the complete dynamic program using literal fibre
regrouping and 80-digit arithmetic. On success, independently audit every
state and edge of the saved complete witness, including all arity charges
and the final signed head. No alternate witness may replace it after audit.
The same 90/100-second limits apply; preserve partial results if needed.

Download scripts, arrays, records and hashes into
`2-fully-proven/computations/ccm-fu-charge-safe-order-2026-09-08` and remove
owned remote files/processes. Floating data are not interval certificates
and supply no Lean premises.
