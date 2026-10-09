# All locally nilpotent motions of the ordered discriminant complement: COMPLETE batch

Goal remains active/unbudgeted, all live routes and route candidates, no Weil priority, no cards. Prior turn classified progress and previous four hashes checked before work. Upstream HEAD rechecked fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, unchanged. Source Lean results treated as proven. No agents spawned.

Completed 4 NEW modules + 1 existing leaf extended, 22 NEW theorems /28 new public declarations. All 31 current public declarations across five affected leaves audited via /tmp #print axioms, only propext/Classical.choice/Quot.sound. All final plain `lake --old env lean <leaf>` checks empty. Exact path+canonical-or-local-name searchback passes, all owned leaves wired exactly once, fresh .lake objects, no source-tree objects, six scratch helpers removed. No full/umbrella builds, no heartbeat hikes, no mathematical computations. All owned processes terminal: audit session71520 exit0, finalizer17356 exit0. Retained /tmp/paper-all-lnd-axioms.lean.

Authoritative tracker tmp/hgt-openai-math/stable-coordinate-native-port.json latest_verified_batch=discriminant-all-lnd-audits.json. Manifest=discriminant-all-lnd-manifest.json, old baseline=discriminant-all-lnd-baseline.json, proof-audit/searchback-audit/index/lint/leaf/axiom logs same prefix. Candidate discriminant_all_lnd_candidate complete, all batch plan steps complete. Cumulative551 owned leaves /4566 public math results. StableCoordinate117 source+108 application=225 modules /2401 public declarations historically audited. 81 unaffected stored source hashes revalidated unchanged, 1 changed historical leaf fully reaudited; completed_modules now86 hashed rows +139 older legitimate no-sha rows.

New code under formal/GaloisForLFunctions/HTGeometry:
1. PaperLocallyNilpotentMultipliers.lean (4theorems):
- paperLND_fixed_of_dvd_apply: for LND D on char0 domain, a|D(a) forces D(a)=0. Uses proven source exists_last_nonzero_iterate + derivation_iterate_top_mul, not an assumed extra premise.
- paperLND_invariant_smul_iterate: when D(q)=0, (qD)^m(a)=q^m D^m(a).
- paperLND_invariant_smul: invariant multiples preserve LND.
- paperLND_smul_iff D hD q: IsLocallyNilpotent(q•D) iff D(q)=0. NO SLICE NEEDED. Initially included slice parameter; Lean exposed it as unused, removed. General criterion over arbitrary commutative characteristic-zero domains, not only fields.
2. PaperDiscriminantRootUnits.lean (9public:2instances2defs5thms):
- public IsDomain and CharZero instances for PaperRootDiscriminantOpen K n (fieldK /char0K).
- paperDiscriminantRoot i :=algebraMap root X_i; paperDiscriminantTranslation K n :=previous common unit velocity field.
- ordered root differences are units (difference divides V, V divides V², IsLocalization.Away.isUnit_of_dvd).
- derivations of localized ring determined by root values (MvPolynomial.derivation_ext on compAlgebraMap + private K-linear localization ext proof).
- common translation maps every root to1 and is LND (all prerequisites paid).
- ANY LND of localized ring has same value on every root, by source factorial closure killing units. Includes denominator-bearing coefficients, no assumption of extension from downstairs.
3. PaperDiscriminantAllDerivations.lean (7theorems):
- empty-root algebra has only zero relative derivation (even withoutCharZero).
- LND(q•commonTranslation) iff translation(q)=0 for all n.
- paperDiscriminantLND_classification n D for Fin(n+1): LND D iff there exists UNIQUE q with δ(q)=0 and D=q•δ. q=D(firstroot). Derivation ext gives multiple; generic multiplier criterion proves invariance.
- Every pair of LNDs commute (Function.Commute), sums are LND, all nonzero LNDs have exact same kernel asδ.
- paperDiscriminantLND_universal_invariants_iff: fixed by EVERY LND iff fixed byδ. This is exact common-invariant statement, no unknown conditions.
4. PaperDiscriminantTranslationSlice.lean (7public:2defs5thms):
- paperDiscriminantTranslationConstants K n is SubalgebraK actualS, kernelδ, built from native rational derivationKernel via restrictScalarsℚ while retainingK.
- every root difference belongs to constants.
- paperDiscriminantTranslationSlice K n :Polynomial(constants K(n+1)) ≃ₐ[K] S. Native LocallyNilpotentDerivationSlice.bijective_aeval_of_locallyNilpotent applies becauseδ(firstroot)=1 andδLND already proved. PolynomialX→firstroot, Ccoeff→originalcoeff; every localized expression has UNIQUE polynomial expansion in firstroot over constants.
- To avoid200k elaboration timeout, specialize via PRIVATE generic fieldKernel/fieldSliceEquiv over abstractB (all instance work cached before applying complex localized type), no heartbeat changes.
Existing modified leaf PaperDiscriminantConstantDirections.lean: exposed existing PRIVATE difference_dvd_vandermonde via public paperVariableDifference_dvd_vandermonde. Added one theorem, reused by root-units proof. No existing public theorem type/body changed. Old discriminant-clock-manifest.json hash for this leaf is now intentionally superseded by latest manifest. Revalidate LATEST manifest, not old batch manifest! Previous ClockClassification/Rigidity source unchanged; importing their existing objects against enlarged Directions module checked successfully.

Novelty: BRIDGE from proven source top-iterate/factorial-closure proofs into native discriminant localization + vector fields + native slice theorem. Exact all-derivation classification and invariant geometry; no claim of new general LND theorem or RH closure.

Search evidence: discriminant-all-lnd-search.json deep partialFalse complete inventory70057; compiler coverage predominantly source_only/pending/stale, claims checked in Lean. Useful native hit LocallyNilpotentDerivationSlice.lean; sourcehits FactorialClosure, UnivariateLND, LocalizationLND, source equivalence LNDAction. Native exhaustive rg found no prior divisible-derivative rigidity/multiplier criterion. Related PaperComplexDerivationSlice.lean already has C-specific scalar-preserving slice; reused pattern with private arbitrary-field bridge.

Mathlib API probes verified in this toolchain: Derivation.smul_apply/leibniz_pow/compAlgebraMap/restrictScalars, IsLocalization.Away.isUnit_of_dvd, IsLocalization.isDomain_of_le_nonZeroDivisors/surj/map_units, Units.mul_right_inj, Algebra.charZero_of_charZero, Nat.choose_pos, add_smul, Polynomial.aeval_X/aeval_C, AlgEquiv.ofBijective. aeval_C takes root-coordinate argument THEN coefficient (`Polynomial.aeval_C root a`). Native Q-algebra/tower instances on S infer correctly. New empty-root theorem needs `omit [CharZero K]` to remove lint.

Latest global lint13 FOREIGN unwired leaves, none owned: RHTower.ModularLambdaWindingLog; Sieve.UnitBlockFrequencyBounds, UnitBlockFrequencyComparison, UnitBlockFrequencyDecay, UnitBlockPoissonKernel, UnitBlockPoissonSummation, UnitBlockReflection, UnitBlockReflectionDualBlocks, UnitBlockReflectionMoment; HTGeometry.IntervalIntegralHolderSwap, MonotonePhaseFirstDerivativeTest, QKrawtchoukCompanionTriangular, SmoothPlateau. Busy shared tree; do not change them. Index refreshed9changed files (including concurrent foreign work).

Next steps (NOT yet begun/proven): continue all-route Lean searches; apply generic invariant-multiplier iff to additional actual native LND clocks. For this geometry use proven source LND/additive-coaction correspondence to classify all algebraic additive actions as common translations with invariant speed; pay derivative/exponential coefficient identification. Further concrete refinement: identify constants with algebra generated by root differences and inverted discriminant, building explicit root/difference chart infrastructure if needed. Intrinsic polynomial chart and all-LND classification are already complete; avoid duplicate wrappers. Recheck upstream HEAD at next sweep.