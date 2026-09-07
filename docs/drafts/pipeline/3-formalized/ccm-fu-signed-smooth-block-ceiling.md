# CCM-FU: signed ceiling for complete smooth square blocks

- **Stage:** 3-formalized; exact-file proof checks passed, Lake packaging audit pending
- **Type:** [BRIDGE], unconditional signed source theorem
- **Parent:** [bounded quotient profiles](../1-in-progress/ccm-fu-bounded-quotient-profiles.md).
- **Goal:** Complete signed Abel bound and RH remain open.

## Closed source inequality

Write R(n) for the exact smooth divisor-hyperbola remainder and
`a=log(2*pi)/2-gamma-1/6`. For every s>=1, Lean proves

`sum_(n=s^2..(s+1)^2-1) R(n) <= (2s+1)*a`.

The signed comparison removes the existing additive upper error of 15
per complete block. The coefficient is optimal: a real C bounds every
complete block by `(2s+1)*C` if and only if `a<=C`. The converse follows
from the existing absolute block-mean error and unbounded block length.
Both assertions concern the literal smooth divisor source.

## Dependency-closed paper mechanism

Put c=s(s+1). Strengthen geometric harmonic centering to
`H_s-gamma-log(c)/2 >= 1/(6c)-1/(30c^2)`.
The difference of the correction between successive integers is compared
with `atanh(t)-t`, for t=1/(s+1). The derivative of
`atanh(t)-t-t^3/(3(1-t^2))+2t^5/(15(1-t^2)^2)` is
`8t^6/(15(1-t^2)^3)>=0`. The correction tends to zero, so telescoping
gives the stated harmonic inequality.

Pair terms at c-j and c+j. Exact Stirling upper bounds and

`(1+t)log(1+t)+(1-t)log(1-t) <= t^2+t^4/(6(1-t^2))`,
`log(1-t^2)<=-t^2`

give the paired quadratic term plus an explicit quartic remainder.
Use `j^4<=s^2*j^2`, `j<=s`, and the exact sum of j^2. Summing the
pairs and central term bounds the block excess above `(2s+1)*a` by

`(2s+1)*[-1/(4c)+(2c+1)/(30c^2)+1/(12s^2)+1/(36s(s+2))]`.

The bracket equals

`-[13(s-2)^3+107(s-2)^2+252(s-2)+138]/[180s^2(s+1)^2(s+2)]`,

so it is nonpositive for s>=2.
The first block reduces exactly to `log(12)-9+12*gamma`; existing
analytic logarithm, pi and Euler-constant bounds give its ceiling.
No numerical experiment or computed source value is needed.

## Remaining obligations

The complete-block sign alone does not bound a terminal partial block
or its varying square-root weights. Those must be retained in any
global unit-channel comparison. The target `K_p(N)<=2K_1(N)`, arbitrary
mixed-state successor selection, complete extension and RH remain open.
Do not promote an unweighted block sign into an Abel or RH bound.

## Lean surface and validation

`GaloisForLFunctions/RHTower/HarmonicGeometricSecondCorrection.lean` proves
`harmonic_mascheroni_geometric_lower_second` and
`log_symmetric_entropy_le_quartic`.

`GaloisForLFunctions/RHTower/DivisorSmoothSignedBlockCeiling.lean` proves
`sum_divisorHyperbolaSmooth_square_block_le_mean` and
`sum_divisorHyperbolaSmooth_square_block_ceiling_iff`.
All names are in namespace RHTower. The only theorem inputs are the
displayed index/domain parameters; no conjectural source estimate is assumed.

Complete scratch checks and exact-file `lake env lean` checks passed
without warnings. Only the two new leaf oleans were emitted. Both modules
are wired into RHTower.lean; no umbrella build ran. The four new public
theorems were axiom-audited once from an external scratch file and use only
`propext`, `Classical.choice`, and `Quot.sound`. No existing capstone was
re-audited. No numerical experiment or numerical premise was used.

The declaration index refreshed and `scripts/formal_tools.py lint` passed,
with existing large-file warnings. The initial lint failure on a concurrently
edited Montgomery module cleared after that module's owner wired its import.
All owned Lean/Lake process handles ended; five owned scratch/log files were
removed. Concurrent source edits and commits were preserved.

The targeted Lake packaging audit remains pending. The known prerequisite
rebuild path from the earlier Lake audit was not repeated. These successful
checks are exact-file proof checks, not a claimed passing Lake build.
This task kept the frontier map read-only.
