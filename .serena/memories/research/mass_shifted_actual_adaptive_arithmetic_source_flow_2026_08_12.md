# Mass-shifted actual adaptive arithmetic-source flow (2026-08-12)

Created `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow.lean`, wired into `RHTower.lean`, and documented as report equations (9.3.523)–(9.3.529).

## Main correction
`XiShiftedHardEdgeRadialSourceConnection` is a flat hard-edge gauge transport with selected hard-edge polynomial frozen. It is not derivative of actual moving arithmetic source: reciprocal chart and canonical inverse-Hankel admission also move.

For `K_ij=i+j+2`, `S_y(a,b)=sum K_ij a_i b_j s_K`, `J_y(a,b)=sum K_ij(K_ij+1)a_i b_j s_(K+1)`:
`S' = -J + S(da,b)+S(a,db)`.
Both `S` and `J` are proved equal to source-first moment polynomials; at square mass they are literal rational–Gamma minus von Mangoldt formations.

Canonical diagonal law on effective admission branch:
`(A_n^sharp)' = -J_n^sharp + 2 A_bil(V_n,P_n)`.
No Hankel positivity is assumed; only determinant nonzero is needed to differentiate inverse-Hankel admission. Unconditional capstone: determinant zero OR full literal flow.

## Three-connection split
Define radial raise `R_D=sum K a_i b_j s_(K+1)` and chart drift `C_D=sum K(D-K)a_i b_j s_(K+1)`. Proved `J=(D+1)R_D-C_D`, hence for `D=2n+2`:
`(A_n^sharp)'=-(2n+3)R + C + 2 A_bil(V_n,P_n)`.
This separates moment/radial, reciprocal-chart, and admission connections.

Exact monotonicity burden:
`deriv A_n^sharp <= 0 <-> 2 A_bil(V_n,P_n) <= J_n^sharp`, equivalently `C+connection <= (2n+3)R`.
Therefore endpoint-raised frozen radial positivity alone is not the actual source-flow sign theorem.

## Verification
Direct `lake env lean` passed. Targeted build passed `11757/11757`. Eight capstone axiom audits: only `propext`, `Classical.choice`, `Quot.sound`. Forbidden declaration scan and `git diff --check` clean. Repository-wide lint remains blocked by unrelated concurrent umbrella-reachability errors; target module is reachable and absent from lint errors.
