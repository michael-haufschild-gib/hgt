# CCM-FU: exhaustive charge-safe order test

- Type: derived diagnostic for the unchanged full-source quadratic bound.
- Status: protocol frozen before execution.
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

## Frozen experiment

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

## Frozen independent audit

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
