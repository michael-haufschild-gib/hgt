# ACS — Young projections of the arithmetic character at rank ≤ 4

- **ID:** acs-mixed-young-small-rank (review-0711 A29)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every multiplicative class function `χ_p(σ) = Π_{cycles, length k ≥ 2} p_{k−1}` and every shape `λ` with `|λ| ≤ 4`, the Young symmetrizer value `χ_p(c_T) = Σ_{p∈R_T}Σ_{q∈C_T} sgn(q)χ_p(pq)` equals `(n!/f^λ)·det(e_{λ'_r−r+c})`, a Toeplitz minor of `e_k = (1/k!)Σ_{S_k} sgn·χ_p` (dual Jacobi–Trudi). For the arithmetic endpoint character `e_k` are the exterior-series coefficients, so by PF₂₀₀ every Young projection — mixed shapes `(2,1)`, `(3,1)`, `(2,2)`, `(2,1,1)` and the row shapes — is nonnegative: the arithmetic cycle class function is positive definite on `S_2`, `S_3`, `S_4`.

## Proof
Both sides are polynomials in `p_1, p_2, p_3`. The signed cycle types of `R_T × C_T` and of `S_k`, `k ≤ 4`, are evaluated by the kernel (`decide`); the determinants are expanded (`det_fin_two/three`, first-row expansion for `4×4`); `ring` closes each identity. `e_k` of the arithmetic character equals `Re` of the `k`-th exterior coefficient by the corpus alternating identity, and `xiEndpointExteriorCoefficient_pfSeq_twoHundred` gives the sign.

Values: `(2,1)`: `1 − p_2 = 3(e_2 − e_3)`; `(3,1)`: `1 + 2p_1 − p_1² − 2p_3 = 8·det[[e_2,e_3,e_4],[1,1,e_2],[0,1,1]]`; `(2,2)`: `1 + 3p_1² − 4p_2 = 12(e_2² − e_3)`; `(2,1,1)`: `1 − 2p_1 − p_1² + 2p_3 = 8(e_3 − e_4)`.

## Lean
`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Representation/MixedYoungProjectionsAtSmallRank.lean`: `youngValue`, `eSeq`, `cycles_*` (kernel enumerations), `youngValue_21_eq`, `youngValue_31_eq`, `youngValue_22_eq`, `youngValue_211_eq`, `youngValue_2_eq`, `youngValue_3_eq`, `youngValue_4_eq`, `eSeq_xiEndpoint`, `youngValue_21_nonneg`, `youngValue_31_nonneg`, `youngValue_22_nonneg`, `youngValue_211_nonneg`, `youngValue_rows_nonneg`. Checked with `lake --old env lean`.

## Scope
Rank `≤ 4`. Extending to every rank `≤ 200` (where PF₂₀₀ applies) needs the Frobenius formula `χ_p(c_T) = (n!/f^λ)s_λ` and Jacobi–Trudi in general; neither is in Mathlib or the corpus. Positivity at all ranks is RH (B86).
