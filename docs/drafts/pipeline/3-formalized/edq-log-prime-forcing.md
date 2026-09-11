# EDQ compensated logarithmic renewal and compulsory forcing

Stage: 3-formalized. Unconditional source identities and size estimates;
no claim of external novelty. RH remains open.

The proof chain is Euler deletion → a cofinal subpower ceiling for the
complete signed physical source/current → off-line exclusion → RH.
This result corrects the prime-renewal equation used to attack that ceiling.

## Closed result

Let `b_q=bdGen(1/q)` in the existing physical carrier and
`H_m=sum_(d<=m) mu(d)/d`. Define the literal correction

```
B_N = sum_(q<=N) Lambda(q)*H_floor(N/q)*b_q.
```

There are positive constants c,C such that, eventually,
`c*N <= ||B_N||^2 <= C*N`. The logarithmic source satisfies exactly
`J_N=-A_N-B_N`, where A_N contains the compensated prime-dilation packets.
In particular, B_N cannot be discarded as a subpower energy error.

The positive survivor includes both bounds on the full physical norm,
the positive mean limit, and the exact renewal identity. No route is retired.
The [paper proof and transfer audit](../1-in-progress/edq-compensated-log-renewal.md)
retain the complete definitions, hypotheses tested, partial corpus searches,
and unrelated-paper applicability checks.

## Proof mechanism

The uniform bound `|H_m|<=2` and Chebyshev's bound control every absolute
coefficient prefix. Finite Abel summation then gives the square-root norm
upper bound. Signed hyperbola interchange and PNT give

```
N^(-1)*sum_(q<=N) Lambda(q)*H_floor(N/q)
  -> c2 = sum_(d>=1) mu(d)/d^2 >= 1/4.
```

Domination by a constant times `d^(-2)` justifies this limit. The reciprocal
coefficient mass is O(log N), so the literal cell mean divided by N tends
to `c2/2`. The existing physical-window inequality
`|mean|^3<=8*moment*energy`, with `moment=O(N^2)`, gives the lower bound.
Finite Mobius--Mangoldt convolution proves the complete renewal identity.
No numerical premise or numerical experiment is used.

## Lean and validation

Module: `GaloisForLFunctions.RHTower.EulerDeletionLogPrimeForcing`.
Namespace: `RHTower.DeletionLogPrimeForcing`.
The 471-line leaf contains five public definitions and seven public theorems:
`c2_lower`, `coeff_sum_eq_hyperbola`, `coeff_sum_limit`, `mean_limit`,
`norm_forcing_le`, `linear_energy_bounds`, and `compensated_renewal`.

The complete scratch proof passed `lake env lean` with no diagnostics.
The final targeted command
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionLogPrimeForcing`
passed; the new leaf built in 9.9 seconds. Lake replayed cached dependency
messages. No full or umbrella build was requested. The import is wired
once into `RHTower.lean`; generated indexes were refreshed once.
`scripts/formal_tools.py lint --check-generated` passed, with existing
large-file warnings. A separate `lake env lean` scratch audited exactly the
seven new public theorems: each depends only on `propext`, `Classical.choice`,
and `Quot.sound`. No added axiom or numerical certificate occurs.
All owned processes exited. Temporary proof, API-name, search, and axiom
files were removed. Scoped whitespace, documentation links, the unique
umbrella import, and the generated API entry were checked.

## Remaining obstacle

The joint signed residual still needs a cofinal subpower ceiling. Combining
the existing stretched source estimate with finite Abel summation gives,
on paper, `||A_N+B_N||/||B_N|| -> 0` and `||A_N||/||B_N|| -> 1`.
Those relative limits are not Lean theorems in this leaf and do not improve
the known power of N. Neither the present result nor that paper consequence
proves RH or falsifies it.
