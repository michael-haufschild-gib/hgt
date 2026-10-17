# Quantitative Bi-Scale constant: facts, failures, proof boundaries

Authoritative ledger: `docs/reports/BiScaleUncertainty/WORKING-LEDGER.md`; proofs: `docs/reports/BiScaleUncertainty/quantitative-constant.md`; card: `docs/drafts/pipeline/1-in-progress/bi-scale-quantitative-constant-2026-10-17.md`. User requests a factual working ledger, not a diary. USER CLEARED ACTIVE GOAL: research stopped, not complete; these notes do not authorize resumption. Independent field, no RH objective, no hgtl7 skill. Read task brief and current field README if research resumes.

## Certified reusable core

All modules below live under `formal/GaloisForLFunctions/BiScaleUncertainty/`.
- `SharedOriginMultiCosetLeverage.lean`: exact shared-origin block support R sqrt(W²+(sum block l2 norms)²), equality witness, rational penalty, literal dyadic grid. Sharp sphere relaxation only. Concurrent discovery: shared bridge, not extra contribution.
- `DistantCopyPolarEnforcement.lean`: actual f(u)-exp(-T/2)f(u-T); exact local normalized preservation, polar cancellation, O(exp(-T)) energy error. `polar_log_grid_lower_bound_iff`: polar/nonpolar finite-grid infima agree for real compact C^r sources r>=2, including smooth, unrestricted support.
- `FiniteMomentEnergyInvariance.lean`: coefficient-uniform O(exp(-T/2)) error permits growing coefficients. Any finite list of real exponential source moments, including zero/negative rates, can vanish without changing finite-grid infimum. Successive separations; common-separation polynomial bound remains paper-only.
- `FiniteSourceEnergyScalarization.lean`: separate real sources beyond local window; both signs preserve summed local correlation and average energy equals component sum. Better sign gives exact scalar realization with no energy increase. Finite-list induction, scalar/vector/polar grid lower-bound equivalence, and convexity of actual unit-mass scalar local energy epigraph. Components need not separately satisfy grid zeros. Support may enlarge; no source parity assumption or arbitrary spectral factorization.
- `FiniteSpectralEnvelopeRealization.lean`: Ψ(ω)=∫(1-cos(ωx))w(x)dx=gammaBracket(ω)-gammaBracket(0). Cosine/sine-modulated real sources have summed correlation h_f(x)cos(ωx). Finite probability mixture μ has normalized VECTOR energy within E(f) of S(μ)=Σp Ψ(ω), uniformly in frequencies. Scalarization then polar enforcement preserves exact local data and the upper energy bound.
- `BroadSpectralCostRealization.lean`: compact C² f is globally Lipschitz, R-h_f(t)<=M|t|. First weight moment finite via xw(x)<=(2x+1)exp(-x/2). Dilation fδ(u)=f(δu) has hδ(x)=δ⁻¹h_f(δx), E(fδ)<=δ M M1/R. Actual ContDiffBump supplies nonzero smooth seed. Final `exists_smooth_polar_grid_source_lt_spectral_cost`: EVERY feasible finite spectral probability gives actual smooth compact polar scalar sources with exact log-grid zeros and E<S+ε for any ε>0. No envelope-energy or source-existence premise. `polar_grid_lower_bound_le_spectral_cost` gives C<=S for any valid smooth polar grid lower bound. ONLY upper realization direction, not full variational equivalence.

Prior boundaries: complex-even whole-profile/fixed-window scalarization already exists in `EvenSectorSmoothSourceScalarization.lean` and `EvenSectorWindowPurification.lean`; cosine/sine modulation already exists in `WeilWorkPBAPJointProfiles.lean`. New assertion is real-source domain, uniform archimedean energy control, exact grid polar realization, discharged envelope premise. No exhaustive external novelty claim.

## Verification

Six leaves passed direct `lake --old env lean -o ...`, exit0/no diagnostics, all wired into umbrella. Scratch axiom audits:5 shared-origin endpoints,23 polar,5 finite-moment,14 scalarization,13 spectral-envelope,11 broad-source theorems. Only propext/Classical.choice/Quot.sound. Explicit smooth specializations passed, including moments[0,1/2,-1/2], scalar convexity/vector equivalence, and N=2 one-frequency realization ω=π/(2log2). All owned processes exited. Index refreshed, all24 new spectral theorems indexed; scoped whitespace check passed. Latest lint FAILED on ONE concurrent missing umbrella import: `PhysicalCollarDualCertificate`, plus381 large-file warnings. No task-module error. Do not claim global green without fresh evidence. Scratch evidence archived in `/tmp/biscale-quantitative-audit-20261017/`.

No numerical experiments, added axioms, heartbeat changes, full/umbrella builds, commits. Smooth order is coerced INNER top in WithTop ℕ∞; `WithTop.coe_le_coe.mpr le_top` proves2<=smooth.

## Unfinished research

Four significant certified packages: polar enforcement; arbitrary finite exponential moments; finite real vector scalarization/convexity; finite spectral probability realization with no envelope premise. Two spectral leaves count as ONE package. Sharp constants and100-contribution objective unfinished; goal cleared by user.
- Reverse Fourier measure comparison and exact finite atomic moment reduction. `CHMDWindowFourierTail.lean` contains `levyForm_eq_fourier`; verify exact applicability. `HTGeometry/FiniteRealAtomicMeasure.lean` computes existing finite atomic integrals, not arbitrary-measure atomization. Deep search partial/source-only; no exact atomization theorem located. Attainment/closure/duality unproved.
- Full continuous real PD cone polar infimum invariance via triangular taper + GNS correction PAPER only; absolute hyperbolic integrability required in polar subclass.
- Even-source symmetric three-copy enforcement PAPER only; does not identify even/unrestricted infima.
- Reflection allocation L_N(β) dominates max(folded,B_N) on paper. Formal integration/comparison pending. Adjacent `IntegratedOriginCollarLeverage.lean` gives finite positive coefficient; do not identify differing partitions without proof.
- O(δ²) broad-source derivative estimate paper-only; O(δ) construction is Lean-certified.

## Failures and guards

- Origin weights cannot be spent per coset; joint block norm includes cross terms. Folded/coset bounds require max or proved overlap allocation.
- Uniform positive polar premium impossible on unrestricted-support finite-grid domain; survivor is explicit exact enforcement with exponentially small cost.
- Translate coefficients need not decay; coefficient normalization handles negative rates.
- Exact sign averaging removes finite rank without estimating small cross energies.
- Two-sided spectral error applies ONLY to vector construction; scalar selection retains upper bound. Reverse comparison needs separate proof.
- Convex epigraph does not imply closedness, exact atomization, attainment, strong duality, or full Bochner-cone equivalence.
- Correct deformation (R-h)w+μhc=Rw-h(w-μc); extra μRc is wrong. Crossover sign matters.
- C_N nondecreasing but uniformly bounded above by fixed narrow source (diameter<log2) and polar infimum invariance; unbounded N-growth impossible here.
- Finite-grid/unrestricted-support arguments do not prove infinite-grid or common-support versions; relaxation equality witnesses may not be autocorrelations.

Tooling: Serena ignores Lean paths; use file reads. update_plan unavailable; card tracks plan. Verified names abs_add_le, HasCompactSupport.zero, Prod.smul_fst, global integrableOn_exp_mul_Ioi. Literal Finset.Icc2 2 in scratch requires `(2:ℕ)` annotation to avoid real-index inference. Missing cached objects may need serial leaf rebuilds; observed cache-loss cause unknown. Own foreground Lean processes serial; no full builds.