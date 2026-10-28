# Certified arithmetic residual bounds

## Mathematical statement

On the actual complete source graph H, let K be the closed fixed-log-cell carrier,
P its bounded Weil projection, R=1-P, T_W the full graph Weil operator, and
J=Pi_K T_W its graph-orthogonal restriction to K. For every x in H and u in K,

W(x-u)=W(Rx)+W(Px-u),

||Px-u|| <= 2||J(x-u)||,

W(x-u)-2||J(x-u)||^2 <= W(Rx)
  <= W(x-u)-(1/2)||Px-u||^2.

Equality W(x-u)=W(Rx) holds exactly when u=Px. For any second source y and trial v,

|W(x-u,y-v)-W(Rx,Ry)| <= 2||J(x-u)|| ||J(y-v)||.

For bounded linear families F:E->H and U:E->K, define D=J(F-U). Every coefficient
vector c has nonnegative trial error at most 2||D||^2||c||^2, graph correction
error at most 2||D||||c||, and mixed error at (c,d) at most
2||D||^2||c||||d||. This is one simultaneous operator bound, independent of a
matrix-entry presentation.

## Dependency-closed proof

The imported arithmetic carrier estimate is ||p||^2 <= 2W(p) on K. Weil
orthogonality gives W(Px)=<Jx,Px>, so Cauchy--Schwarz gives
W(Px)<=2||Jx||^2 and ||Px||<=2||Jx||. Since P fixes K,
P(x-u)=Px-u and R(x-u)=Rx. The exact residual pairing identity therefore gives
the trial decomposition and both one-sided bounds. Coercivity makes equality
force Px-u=0.

For mixed errors, orthogonality rewrites W(Px,Py)=<Jx,Py>. Cauchy--Schwarz and
the projection norm bound give 2||Jx||||Jy||. Apply this to x-u and y-v. For a
whole family, the operator inequality ||Dc||<=||D||||c|| supplies the simultaneous
energy, graph and mixed estimates. No positivity of the complement is used.

## Lean declarations

Programme: `formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/`.

- `TheArithmeticSchurComplementHasCertifiedErrorBounds.lean`:
  `arithmetic_trial_energy_decomposition`, `arithmetic_trial_energy_bounds`,
  `arithmetic_trial_graph_error`, `arithmetic_trial_energy_eq_iff`,
  `arithmetic_trial_mixed_error`.
- `OneStationarityBudgetControlsTheWholeSourceFamily.lean`:
  `family_energy_error_le_opNorm`, `family_graph_error_le_opNorm`,
  `family_mixed_error_le_opNorm`.

Both modules pass individual Lean checks. Printed capstone dependencies contain
only `propext`, `Classical.choice`, `Quot.sound`.

## Scope and contribution

Finite-section minimization and index descent belong to ArithmeticIndexDescent.
The contribution here is a certified stationarity error bound on the actual
unbounded carrier, including mixed errors and one norm for a complete coefficient
family. These estimates retain the signed residual. They neither construct an
exhaustive family with small stationarity norm nor prove residual nonnegativity.

## Exact complement radical

The actual arithmetic complement is ker(P)=ker(J). For r in this complement,
r annihilates every complement vector under the full Weil form if and only if
T_W r=0. Every full-form null vector lies in the complement; projection leaves
it unpaid and the residual retains it. The actual independent theta null family
therefore remains in the residual.

Proof: ||Px||<=2||Jx|| gives one kernel inclusion, and the defining orthogonality
of P gives the other. If r annihilates the complement, it also annihilates K;
decompose every x as Px+Rx to conclude that r annihilates the entire graph.
Conversely a full-form radical vector annihilates each subspace. Linearity then
gives P(x+z)=Px and R(x+z)=Rx+z for every full-form null z.

Lean: `TheSignedComplementRetainsExactlyTheWeilRadical.lean`, declarations
`stationarity_eq_zero_iff_mem_complement`, `complement_radical_iff`,
`projection_add_radical`, `residual_add_radical`,
`exists_infinite_arithmeticWeilRadical`. Individual no-olean audit passes;
printed capstones use only `propext`, `Classical.choice`, `Quot.sound`.

The signed-source radical and the full Weil radical are distinct. The existing
CHMD quotient theory identifies the additional two-pole plane. The new result
concerns what the actual fixed-carrier projection retains, rather than a new
classification of the ambient radical.
