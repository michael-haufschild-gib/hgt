# Sharp exponent for neutral pairs remaining at a cutoff

- **Stage** 3-formalized
- **Question** Can the unsigned obstruction to one global matching be explained by its net Möbius imbalance?

Let \(P_F(X),N_F(X)\) count positive and negative unpaid squarefree vertices, and put \(C_F(X)=\min(P_F(X),N_F(X))\). At every cutoff \(U_F(X)=2C_F(X)+|M(X)|\). Thus \(C_F\) is exactly the number of additional opposite-sign pairs available if the arithmetic edge restriction is lifted on the unpaid population. The corpus bound \(|M(X)|\ll X^{7/8}\) and the proven unsigned power obstruction jointly imply that \(C_F(X)=O(X^t)\) holds exactly when \(t\ge1\), for every \(t>0\). Indeed a subunit bound would give the forbidden exponent \(\max(t,7/8)<1\) for \(U_F\). Both signs therefore attain their near-linear lower witnesses at the same cutoffs.

For a matching covering every squarefree nonunit, apart from the unit these neutral pairs consist entirely of oppositely oriented edges crossing the same sharp cutoff. Their signed difference is \(M(X)-1\).

One sublinearly short matching with density-zero unpaid set also bounds the fixed and crossing signed sums separately by every power above 20999/24000.

**Lean.** `neutral_unpaid_decomposition`, `neutral_unpaid_power_iff`, and `separate_signed_savings_on_one_short_involution` in [Neutral pairs among the unpaid vertices](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/NeutralPairsAmongTheUnpaidVertices.lean).
