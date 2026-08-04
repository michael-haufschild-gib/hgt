# Route R selector-shape no-gos (2026-08-04)

Task: discharge residual hypotheses of
`formal/GaloisForLFunctions/RHTower/CCMRationalAdelicCompletedXiFixedCoronaPolarization.lean`
without weakening; RH forbidden as input. The file (after user cleanup) already proves:
`NormIdentity(p,rho) <-> DaggerIdentity(p,rho) <-> K_{p,rho}=0 <-> Re rho=1/2`, with
`K_{p,rho}=(2 Re rho-1) kappa_p`, `kappa_p in (0,1)` exact
(`PrimeDepthBVWoldReesCoronaContractionNoGo.lean`), and `forall rho` at any one prime `<-> RH`.
So unconditional discharge IS RH; the only admissible move is a noncircular source producer
(`FIXED_POLARIZATION_PRODUCTION` on card `cofinal-bockstein-polarized-adelic-stokes.md`).

Appended this session (all RH-token-free, unconditional, axioms only
propext/Classical.choice/Quot.sound):

- `completedXiSameFiberResolvedShear_eigenvector_iff`: the unipotent resolved shear `S_K`
  admits an invariant line through a coefficient-faithful vector iff `K=0` (eigenvalue forced
  to 1, then `K w_q v_0 = 0` with `|w_q|=1`).
- `CCMRationalAdelicPrimeXiInvariantFaithfulLine` + iffs to `K=0` and `Re=1/2`: the demanded
  selector's clauses (1) transport preservation + (2) jet faithfulness ALONE are pointwise the
  conclusion; clause (3) lift identification is redundant. Line/dagger-axis-shaped selectors
  are dead as producers — Clause 5 of `SOURCE_DAGGER_FIXED_POLARIZATION_CARTIER_DESCENT`
  cannot be weakened to line invariance.
- `completedXiFixedCorona_comparison_energyGap` / `_separates` /
  `ccmRationalAdelicPrimeXi_offLine_no_comparison_identifies`: for EVERY function `Phi`
  preserving the two fixed polarizations (no linearity/continuity), the energy gap transports
  as `K^2 |c|^2`; off line no comparison identifies resolved and physical landings.
  Transported-metric kill is the linear special case.

Route-test verdict (on card): the fixed-corona layer consumes only jet-nonvanishing +
clock/connection positivity — both divisor-insensitive — and every statement is natural in the
centered rate. No proof factoring through this interface can give `K=0`; the producer must
break rate-naturality (Weil-type positivity on the full test algebra, bilinear short-interval
control, or an independent singular all-prime boundary law). See
`mem:route-r/2026-08-04-fixed-ideal-gamma-cofinal-bockstein-frontier` and
`mem:route_r/completed_xi_fixed_corona_polarization_normal_form_2026_08_04`.

Verification: direct `lake env lean` pass; targeted `lake build` pass (11271 jobs); axiom
audit clean; RH appears in no new statement.
