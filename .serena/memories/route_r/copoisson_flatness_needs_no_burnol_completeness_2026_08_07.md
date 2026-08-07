# Co-Poisson full-quotient flatness `(2)` is proved WITHOUT Burnol completeness

Supersedes `route_r/copoisson_completeness_needs_critical_line_evaluators_2026_08_07` and
`route_r/burnol_completeness_exact_target_2026_08_07` as the route for this card: those describe the
paper's proof of `(2)` and its (real) obstructions; the Lean proof does not use it.

**The mechanism.**  For `r ≥ 1` both normalized dilations lower the closed co-Poisson source space
one aperture step:

    U_r C_b ⊆ C_{r⁻¹ b},   U_r^* C_b ⊆ C_{r⁻¹ b}.

Reason: the co-Poisson sum intertwines with the seed dilation, `√ρ·P_g(ρ t) = P_h(t)` for
`h(u) = √ρ g(ρ u)`, and for `r⁻¹ ≤ ρ ≤ r` the dilated seed window `[b/ρ, 1/(ρ b)]` still lies inside
`[r⁻¹ b, (r⁻¹ b)⁻¹]`.  Formalized in
`formal/GaloisForLFunctions/RHTower/BurnolCoPoissonSourceDilation.lean`
(`evenDilation_mem_coPoissonSourceSpace`, `evenInverseDilation_mem_coPoissonSourceSpace`).

Hence for `x` in the quotient two apertures up, `U_r x` and `U_r^* x` are already orthogonal to
`C_{j+1}`, the source correction inside `E_{j+1} = Π_{j+1} − P_{j+1}` drops out of both composite
paths, and **both act on `Y_{j+2}` as the projection `E_j`** — strictly stronger than `(2)`.
`formal/GaloisForLFunctions/RHTower/GammaCoPoissonSoninQuadrantFlatness.lean`:
`coPoissonQuotientCommutator_eq_zero`, `coPoissonQuotient{Forward_inverse,Inverse_forward}_eq_projection`,
`coPoissonSourceErrorSyzygy` `(8)`, `coPoissonWordOp` + `coPoissonWordOp_congr_perm` (path
independence, proved by induction on `List.Perm`) + `norm_coPoissonWordOp_apply_le` `(13)`--`(14)`,
`coPoissonWordOp_ladderKernel` `(15)`, `coPoissonEndpointScalar_ratio` `(19)`--`(20)`.

Card `gamma-copoisson-sonin-full-quotient-flatness-syzygy` is now stage 3.

**Transferable lesson.**  When a paper proves an operator identity by density of a hard-to-construct
family, first ask whether the *subspace being projected away* is monotone under the operators in
play.  Here `C_b` grows as the aperture shrinks and both dilations shrink the aperture, which kills
the correction terms outright.  Burnol's completeness theorem was a sufficient but far from
necessary route.
