# WP02 cycle31 — exact weighted fibre recovery COMPLETE (2026-10-08)

Goal ACTIVE/unlimited: apply hgtl7 each turn; solve universal WP02 docs/reports/weil-work/02-exposing-ray.md and Lean RH receiver. No subagents. No numerical experiments, full/umbrella builds, heartbeat overrides, commits/push. One own foreground Lean process at a time; final lake --old env lean leaf. Main WP02 NOT solved. Previous cycle PROGRESS.

## New knowledge/capstone
For every 0<=beta<1/2, every finite nonnegative actual compact complex C2 full-source mixture has arbitrarily accurate actual finite nonnegative polar recovery in weight1+log(2+|tau|)^beta, preserving raw atom at EVERY integer n>=2 including entire zero tail. Both poles on EVERY row. Literal negative Fejer density has exact-null weighted recovery. No growth, RH, positivity or recovery premise added.
Public capstones namespace RHTower.ExposingRayTransfer.SublogFibre:
closure_polarFibre_eq_fullFibre, exists_exact_fibre_recovery, exists_raw_fibre_recovery, exists_fejer_null_recovery; polarFibre_nonempty.
Definitions density hbeta hbetahalf, fullFibre, polarFibre; existing PolarSource and fejerFullSource reused.

## Three new owned leaves27–29 (all in formal/GaloisForLFunctions/RHTower/)
WeilWorkExposingRaySublogScales.lean225lines:
exists_two_scale_small_mass (sublog affine harmonic envelope),
exists_two_scale_small_mass_of_power (power theta<1),
exists_small_two_scales_of_polar_log_bound (ACTUAL separator derives bounds).
Square-block sequence w_j=a_(j+1)+sum_{j²<m<=(j+1)²}a_m/sqrt(j+1).
Its partial mass >=B(N)+B(N²)/sqrtN; shifted harmonic <=H(N)+H(N²).
Existing WeilSingularArithmetic.exists_small_sqrt_mass_of_sublog_envelope gives arbitrarily late N with B(N)/sqrtN+B(N²)/N arbitrarily small. Both windows SAME N.

WeilWorkExposingRaySublogTransfer.lean361lines:
exists_farTest_arithmetic_approx and polarLogSpectralBound_iff_fullLogSpectralBound.
For source aperturea, X=logN-2a. Actual correlation expansion has shifts0,+/-X,+/-2X.
Normerror <= Cf*(sech²(X/2)+B(N)/sqrtN+B(N²)/N).
Actual separator small scales + weighted far-source convergence give extension to ALL full sources. No assumed coefficient envelope.

WeilWorkExposingRaySublogFibreDensity.lean321lines:
Exact finite positive fibre separation, signed coordinate resonators, augmented artificial row, algebraic cone duality, new separator extension. Weighted densities in ordinary L1 encode weighted norm. All raw atoms retained; no energy/aperture/profile/row-count bound.

## Audits
Every final saved leaf command lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<name>.olean GaloisForLFunctions/RHTower/<name>.lean exits0, NO diagnostics.
Combined imported #print axioms of all10 new public theorems exits0; exactly propext/Classical.choice/Quot.sound. Printed closure/raw/Fejer theorem types checked, no research hypothesis.
All29 own prefix-matching leaves wired exactly once in RHTower.lean; no umbrella build.
Global guarded formal lint exits1 on6 unrelated reachability findings:
RHTower.WeilWorkPBAPJointSourceBudget;
HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra.
No WP02 finding. Scoped tracked and all3 new-file whitespace clean. No heartbeat hacks.
ALL own process handles terminal. All11 owned /tmp/wp02-cycle31-* files removed after receipts. Sources/caches retained. No live own process.

## Research/audit
Direct deep search square block partition simultaneous good scales sublogarithmic harmonic envelope --budget-seconds120 --json exit0, partialfalse,68820indexed; all20 candidatelemmas+20 sourcearguments+ingredientset inspected. Compiler stale/pending, semantic unavailable/backgroundrefresh incomplete; no absence claim.
Primary external arxiv1405.6516 Bondarenko–Heap–Seip original2014/revised2015 coefficient Hardy bounds ancestry; no exact weighted source-fibre novelty certificate. Cambridge page failed, no contents inferred.
Verdict BRIDGE; external scientific novelty unestablished. Five anti-theatre+four anti-laziness answers posted in chat.
Current paper SUBHALF-LOG-FIBRE-PROOF fully formalized. RESULT/PROOF/EVIDENCE/SUBLOG-FIBRE-CONJECTURE and working pipeline card updated.

## Big picture / next cycle
Half exponent is LIMIT OF THIS PROOF, not proved sharp. Original 0<beta<1 conjecture OPEN; gamma E-escape vs bounded E-recovery OPEN; universal vanishing-mass-defect producer and WP02 OPEN. Weighted beta<1/2 convergence gives neither bounded gamma energy nor uniform integrability.
Next fresh corpus research should attack signed cancellation / critical logarithmic energy and test removal of absolute-envelope loss; do not repeat completed separation formalization or add assumed-growth receiver. Critical gamma weight has log growth. At beta1 exact Fejer recovery would force negative null-polar energy, opposing WP02 multiplier0, but no such recovery/negative family proved. Keep main full nonzero-ray quantifiers.
Read relevant docs/memories on next turn, mission statement, hgtl7 every turn.
Lean namespace traps: unqualified sum_range_succ shadows Finset; qualify. RHTower add_le_add_left/right have unexpected conventions; use add_le_add h le_rfl or le_rfl h. Root tendsto_rpow_neg_atTop, not Real. Finite Icc/Ioc need Finset qualification with Set open. Absolute bars need space before multiplication.
Serena manual already read cycle31; next init avoid dumping 117k memory inventory from initial_instructions. Serena symbol index doesn't cover ignored Lean, documented rg/newfile fallback. update_plan/multi_tool_use.parallel unavailable; card plan+Promise.allSettled used.
