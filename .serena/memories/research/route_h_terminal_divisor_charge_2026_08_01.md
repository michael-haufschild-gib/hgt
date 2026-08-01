# Route H terminal divisor-charge closure — 2026-08-01

Route H (Xi Taylor/theta core current) is retired as an independent RH mechanism. Its endpoint `XiCTaylorThetaTailCoreCurrentSublinearUpper D` was already Lean-equivalent to RH for every source-selected odd superaccurate schedule, so another sufficient estimate was not new progress.

New unconditional survivor:
- Let `x_n = Re(xiTaylorAnisotropicRightApprox sigma (n+1) - sigma)`.
- Every superaccurate finite Xi Taylor logarithmic derivative has exact horizontal charge tending to `(analyticOrderAt xi sigma).toNat`.
- Every source-selected odd superaccurate raw finite theta core has
  `x_n * J(U_n,z_n) / normSq(P_n(z_n)) -> (analyticOrderAt xi sigma).toNat`.
- At an Xi zero this is exact multiplicity tomography, stronger than the old coarse eventual `m/20` bound.
- A fixed centered meromorphic gauge of local order `ell` changes transferred charge to `m-ell`; exact screening iff `ell=m`. Analytic units preserve full charge.
- Deeper Haar/Prouhet refinement already conserves the same raw current. A non-normal moving gauge is not ruled out, but is a new route with separate source-selection obligations.

Lean modules:
- `formal/GaloisForLFunctions/RHTower/XiCTaylorAnisotropicGaugeCharge.lean`
- `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreDivisorChargeRigidity.lean`
Both imported by `formal/GaloisForLFunctions/RHTower.lean`.

Key theorem names:
- `anisotropicHorizontalResidue_tendsto`
- `xiCTaylor_logDeriv_anisotropicHorizontalCharge_tendsto`
- `xiCTaylor_meromorphicGaugeTransferCharge_tendsto`
- `xiCTaylor_meromorphicGaugeChargeScreenedAt_iff_order_eq`
- `tendsto_xiCTaylorThetaTailCoreCurrent_sub_taylorCurrent_horizontalCharge`
- `xiCTaylorThetaTailCore_anisotropicDivisorCharge_tendsto`
- `eventually_half_xiOrder_lt_xiCTaylorThetaTailCore_anisotropicDivisorCharge`

Verification:
- foreground `lake env lean` passed for each new file;
- final targeted `lake build GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreDivisorChargeRigidity` passed;
- axiom audit for representative theorems: exactly `[propext, Classical.choice, Quot.sound]`;
- new modules contain no sorry/admit/axiom/opaque/unsafe and are umbrella-reachable;
- repository lint remains red only for eight unrelated pre-existing/uncommitted unreachable modules.

Pipeline:
- formal survivor: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-h-finite-theta-core-divisor-charge-rigidity.md`
- retired parent/child: `docs/drafts/pipeline/5-failed/xi-taylor-oriented-finite-coefficient-sublinear-flux.md`, `docs/drafts/pipeline/5-failed/xi-taylor-theta-tail-core-density-current.md`
- Route H marked RETIRED in current frontier map.

External audit found no exact finite-core charge theorem or gauge classification; novelty remains explicitly UNVERIFIED. Planat 2026 reaches the same sign-indefinite off-diagonal theta-kernel wall but not this survivor.