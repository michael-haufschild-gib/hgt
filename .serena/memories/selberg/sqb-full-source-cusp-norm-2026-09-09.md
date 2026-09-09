# SQB full-source cusp norm — 2026-09-09

Active unbudgeted RH goal remains ACTIVE and RH UNPROVED. Frontier map READ ONLY. No owned processes or uncollected handles remain. No subagents, no numerical computation, no commits. Previous state: `mem:selberg/sqb-quarter-shift-source-equation-2026-09-09`.

## Exact new result

`formal/GaloisForLFunctions/RHTower/SelbergScatteringCuspNorm.lean`, 209 lines, namespace `RHTower.SelbergScatteringHeightConjugation`, 10 public declarations, 6 private helpers. Imports QuarterShiftSource, Mathlib Integral.Prod, ImproperIntegrals.

For every actual multiplicity-marked Xi copy q, rho=(q.1:ℂ), u=physicalAngularParameter q=(rho−1)/2, and every real a:

integral over x∈(−1/2,1/2], y>2 of y^(2a)||E_u(x,y)||² dx dy/y² is finite iff 2a+1<Re rho.

E is the original COMPLETE scalar field with every signed Fourier mode. Its nonzero Weyl coefficient Lambda(rho−1) follows from physicalScalar_cutoff_calibration, not a premise. The full weighted tail is uniformly bounded on the entire cusp rectangle for every power; its lifted square is dominated by C² y^-2. MemLp addition/subtraction then transfers integrability exactly to the principal term, whose squared lift is ||Lambda(rho−1)||² y^(2a−Re rho). The unit-width product measure reduces to the sharp power integral. Endpoint diverges.

Definitions: cuspMeasure = (volume restrict Ioc(-.5,.5)).prod(volume restrict Ioi2); cuspLift a f xy = (xy.2:ℂ)^(a−1)*f![x,y]. This includes sqrt of native hyperbolic density. cuspLift_norm_sq explicitly identifies the native density.

Public theorems: cuspLift_tail_memLp (all complex u, real a); cuspLift_xi_memLp_iff; cuspLift_norm_sq; scalarSource_cusp_norm_iff; scalarSource_native_cusp_not_integrable; quarterShiftSource_weighted_cusp_norm_iff (density y^b||v||²/y² finite iff b+.5<Re rho); quarterShiftSource_cusp_norm_iff (unweighted v finite iff .5<Re rho); quarterShiftSource_compensated_cusp_not_integrable (unique invariant b=.5 diverges for every Xi). Two public definitions make 10 total.

Scope: actual two-dimensional cusp norm classification, NOT modular descent, full operator-domain admission or occurrence for entireOperator. Critical quarter field is at divergent endpoint; cusp packet construction elsewhere still valid. Restoring the invariant power density restores the original divergent norm. Other source maps remain unexcluded; independent full-Xi occurrence remains the core.

## Validation

Scratch /tmp/sqb7_norm.lean passed via lake env lean. Source added and imported exactly once after QuarterShiftSource in RHTower.lean. lake --no-build build target preflight named only SelbergScatteringCuspNorm. Final lake build GaloisForLFunctions.RHTower.SelbergScatteringCuspNorm passed 7.6s; parsed all Built lines confirming ONLY named module built. Log /tmp/sqb7_build.log; preflight /tmp/sqb7_build_preflight.log. No new module warnings. All 10 #print axioms reports standard propext, Classical.choice, Quot.sound; /tmp/sqb7_axioms.lean/.log. Export names /tmp/sqb7_exports.json. Corpus index refreshed; /tmp/sqb7_index_audit.json has all 10 public plus 6 private. Own forbidden-token scan and whitespace/diff checks passed.

GLOBAL LINT DID NOT PASS: /tmp/sqb7_lint.log contains only two errors: HTGeometry.FokasLenellsContourFifth and HTGeometry.FokasLenellsContourMoment unreachable from their umbrella. These unrelated files were not edited; both missing imports reconfirmed after lint. Do not claim global lint passed or modify peer work without scope. All compiler/process handles collected (last build51974, axiom16146, index44964, lint8915 completed), ps showed no owned sqb7 Lean/Lake processes.

## Docs and broad search

Paper promoted to docs/drafts/pipeline/3-formalized/sqb-full-source-cusp-norm.md (in-progress copy deleted). Full paper argument, exact statements, scope, all audit results including unrelated global lint errors. Narrow failed mechanism card 5-failed/sqb-literal-quarter-height-multiplier.md updated with this positive norm survivor. Existing universal-law-field/STATUS.md symmetry-and-norm paragraph updated: compensate symmetry and audit full measure and endpoint; integrable remainder cannot alter leading-term admission. FRONTIER MAP NOT EDITED.

Broad OR, no per-module caps, no AND-only restriction: /tmp/sqb7_transform_broad.json 658 declarations/121 modules (Sonine, fractional integral, Bessel order, theta lift, Rankin Selberg, Hecke correspondence); /tmp/sqb7_wave_broad.json 1858/413 (monodromy,wave kernel,functional calculus,complexification,Poisson transform); /tmp/sqb7_automorphic_broad.json 473/117 (automorphic multiplier,Eisenstein power,truncated Eisenstein,mean removal,cusp regularization,periodization); /tmp/sqb7_norm_broad.json 416/252 (cusp integrable,power density,weighted square,Eisenstein norm,cusp admission,square integrable). Counts are metadata coverage, not claim every proof was read.

Inspected cuspHeightPower_periodize_completed: full admitted height orbit sum recovers original E field in Re P.s>1; no spectral shift. Inspected BesselOrder results concern difference equation in order, not a spatial transmutation. HB physical radial monodromy metadata does not establish spatial automorphic source transform. Actual norm proof uses GlobalAngularForcing.weighted_tail_bounded and physical constant-term calibration. Peer HB native cutoff orbit Mellin work remains disjoint; memory read earlier `hawking_bm_native_cutoff_orbit_mellin_2026_09_09`.

Next work must pursue a real full-source occurrence producer, preserving original complex parameter and modular/domain data; do not relabel this cusp admission result as RH. Continue broad corpus queries and inspect actual proof bodies. One foreground compiler; lake env lean scratch; only named module final audits, preflight first, never full umbrella builds.