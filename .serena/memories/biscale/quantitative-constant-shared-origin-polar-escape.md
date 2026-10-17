# Quantitative Bi-Scale constant: facts, failures, proof boundaries

Authoritative working ledger: `docs/reports/BiScaleUncertainty/WORKING-LEDGER.md`; paper proofs: `docs/reports/BiScaleUncertainty/quantitative-constant.md`; active card: `docs/drafts/pipeline/1-in-progress/bi-scale-quantitative-constant-2026-10-17.md`. User requires a factual working ledger, not a diary. Independent Bi-Scale research: no RH objective, no hgtl7 skill. Read the supplied brief and current field README before continuing.

## Certified reusable core

- `SharedOriginMultiCosetLeverage.lean`: exact block support R sqrt(W²+(sum block l2 norms)²), equality witness, rational penalty, literal dyadic grid. Sharp for sphere relaxation only. Concurrent researchers found same formula; shared bridge, not duplicate contribution.
- `DistantCopyPolarEnforcement.lean`: actual f(u)-exp(-T/2)f(u-T), local normalized correlations unchanged for T>D+A, exact polar cancellation, energy error K(f,D)exp(-T). `polar_log_grid_lower_bound_iff` equates polar/nonpolar finite-grid lower-bound sets for real compact C^r sources r>=2, including smooth. Unrestricted support, no source parity requirement.
- `FiniteMomentEnergyInvariance.lean`: uniform coefficient bound K(f,D)exp(-T/2), even for growing coefficients. Choosing a=exp(-beta*T) cancels any real exponential rate and preserves prior zero moments. `finite_moment_log_grid_lower_bound_iff` handles arbitrary finite lists, including zero/negative rates. Uses successive separations, not common T.
- `FiniteSourceEnergyScalarization.lean`: **new exact finite-vector reduction**. Separate f and translated g beyond Df+Dg+A. Both f+g_T and f-g_T have exactly local correlation hf+hg; their energies sum to2(Jf+Jg). One sign therefore costs <=Jf+Jg. Finite-list induction yields `exists_scalar_list_local_energy_le`: exact total correlation on |x|<=A and no greater energy. Individual components need NOT satisfy grid zeros; only their total must. `finite_source_log_grid_lower_bound_iff` and `polar_finite_source_log_grid_lower_bound_iff` equate all scalar/vector/polar finite-grid lower bounds. Weights absorbed by square roots. `convex_localSourceEnergyEpigraph` proves actual unit-mass scalar local-profile/energy epigraph convex BEFORE closure. No spectral factorization or tail estimate required. Support may enlarge, sources real C^r for r>=2, no parity condition.

Prior-work boundary: corpus already has `EvenSectorSmoothSourceScalarization.lean` and `EvenSectorWindowPurification.lean`, giving exact entire-profile scalarization within fixed support for smooth complex even pole-free mixtures. Read their statements. New direct real argument is different in domain/construction, weaker in global profile/support preservation. No claim scalarization is a wholly new general phenomenon.

## Verification

All four task leaves passed direct final `lake --old env lean -o ...`, exit0/no diagnostics. Separate scratch axiom audits:5 shared-origin endpoints,23 polar theorems,5 moment theorems,14 scalarization public theorems. Only propext/Classical.choice/Quot.sound. Smooth-order specializations pass, including moments[0,1/2,-1/2], scalar epigraph convexity, and polar/vector equivalence. Smooth order is coerced INNER top in WithTop ℕ∞, with WithTop.coe_le_coe.mpr le_top proving2<=smooth. All four imports wired. Index regeneration lists new results. Scoped whitespace and forbidden-source scans pass. All owned Lean processes exited.

Latest lint snapshot FAILED on four concurrent modules absent from umbrella: AbstractBiScaleSystemAndSchurKreinCoupling, CollarAllocationDuality, CosecantSecantDualDecomposition, DisjointCollarCliqueDivergenceAndTuransProblem. No task module error. Do not claim global green using previous passing snapshot or modify concurrent unfinished leaves. Existing large-file warnings also remain.

No numerical experiments, extra axioms, heartbeat changes, full/umbrella builds, commits. Scratch evidence archived under /tmp/biscale-quantitative-audit-20261017.

## Open obligations

1. Global sharp constants and100-contribution goal NOT complete. Three certified significant packages: polar enforcement; arbitrary finite moments; finite real vector scalarization/convexity. Do not count14 helper endpoints separately; no exhaustive external novelty verdict.
2. Full continuous real PD finite-energy cone polar invariance: triangular taper (error<=M_w/A) then GNS correction, PAPER only. Absolute hyperbolic integrability required in polar subclass. No arbitrary scalar-root theorem established.
3. Even-source symmetric3-copy correction, error K_D(2exp(-T)+exp(-2T)), PAPER only; does not identify even/unrestricted infima. Common-T finite polynomial estimate m K_D exp(-T/2) also PAPER only, though core finite-moment infimum theorem is certified differently.
4. Reflection-allocation L_N(beta) has paper exact overlap accounting and max_beta L_N>=max(folded,B_N). Formal integration/comparison pending. Adjacent `IntegratedOriginCollarLeverage.lean` already gives finite positive real coefficient bound for compact-continuous LogarithmicGridSource; inspected capstone, owner's ledger records audit. Reuse it; do not redo completed transport or equate differing partitions without proof.
5. Spectral sharp-constant route: finite cosine mixtures times a smooth compact correlation can be represented by cosine/sine-modulated real source components. Scalar admissibility for such FINITE vectors is now solved. Remaining tasks: actual modulation identities, broad-source energy limit, finite-moment optimization, closedness/attainment/strong duality. Convexity alone does not prove these. Full Bochner cone equivalence still unproved.

## Failures and guards

- Reusing origin weight in each coset double-counts. Joint block norm includes cross terms; optimal origin shares proportional to block norms.
- Positive uniform polar premium impossible in unrestricted-support finite-grid class. Positive survivor is explicit exact enforcement with exponential error.
- Coefficients need not decay; normalization controls growing negative-rate coefficients.
- Small cross-energy estimates unnecessary for finite rank removal: exact sign averaging dominates energy. General signed linear local correlation constraints are preserved.
- Do not add overlapping folded/coset certificates. Use max or prove allocation.
- Correct deformation (R-h)w+mu*h*c=Rw-h(w-mu*c). Extra mu*R*c wrong; crossover sign matters.
- C_N nondecreasing but uniformly bounded above by fixed narrow source of support diameter<log2; polar invariance transfers upper bound. No unbounded N-growth conjecture.
- Finite-grid arguments do not imply infinite-grid or common-support invariance. Sharp relaxation witnesses need not extend to admissible autocorrelations.

Tooling: Serena ignores Lean paths; use file reads. update_plan unavailable; card tracks plan. Name probes verified abs_add_le (not abs_add), HasCompactSupport.zero (not hasCompactSupport_zero), Prod.smul_fst (not Prod.fst_smul). Use serial own foreground Lean leaves. Deep search completed but semantic coverage unmeasured and some compiler snapshots stale; source-only hits need verification.