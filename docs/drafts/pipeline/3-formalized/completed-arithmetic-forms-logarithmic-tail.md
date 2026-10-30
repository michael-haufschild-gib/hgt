# Logarithmic rank boundary for the complete native tail

**ID:** completed-arithmetic-forms-logarithmic-tail  
**Stage:** Formalized in Lean 4  
**Type:** Native integration and exact reserve transport

Write $T_N(r)=H_N(k\mapsto\int_r^\infty m_k(s/2)\,ds)$ for the literal
complete native signed tail head. The exact quadratic-form integral and
integrability are formalized in `CompletedArithmeticForms/SeamCoercivity.lean`.

The quadratic source estimate has horizon
$$X_M=\max\bigl(0,\tfrac12\log(C_2/\pi)+\log(M+2)\bigr),
\qquad C_2=16+32D+2Ae^8.$$
Its complete-tail consequences are
$$r\ge2X_{N+1}\Longrightarrow T_N(r)\succ0,$$
$$2X_{N+1}\le r<t\Longrightarrow T_N(r)-T_N(t)\succ0.$$
The second statement follows from the exact mixed-form identity
$$v^{\mathsf T}(T_N(r)-T_N(t))v
=\int_{(r,t]}v^{\mathsf T}H_N(m(s/2))v\,ds.$$
Every nonzero direction is positive throughout the interval, which has positive measure.

At dimension $N+1$, complete Loewner order transports to the exact rank-$N$
Schur successor through `successorSchur_mono`. These consequences
concern the integrated source with its own inverse head, including every mixed entry.
They do not identify its inverse coupling with the pointwise native inverse coupling.

The remaining source interval between the proved seam neighborhood and this
logarithmic tail boundary requires a complete compensation estimate.

Lean: `CompletedArithmeticForms/TailRankHorizon.lean`, particularly
`nativeTailHead_posDef_of_quadratic_rank_horizon`,
`nativeTailHead_sub_quadratic_eq_integral`,
`nativeTailHead_sub_posDef_of_quadratic_rank_horizon`, and
`nativeTailSuccessor_antitone_of_quadratic_rank_horizon`.
All four capstones have only `propext`, `Classical.choice`, and `Quot.sound`.
