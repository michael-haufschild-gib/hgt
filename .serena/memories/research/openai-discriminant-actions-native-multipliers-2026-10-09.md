# Complete batch: all discriminant additive actions + native clock multiplier boundaries

Active unbudgeted goal remains ACTIVE, scope ALL live routes/candidates, NO Weil priority, no cards, direct Lean corpus search. No agents spawned. Previous turn classified progress and its five latest-manifest hashes checked before work. Upstream HEAD rechecked fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, unchanged; source Lean theorems treated as PROVEN.

NEW authoritative batch: tmp/hgt-openai-math/discriminant-actions-audits.json, manifest/proof-audit/searchback-audit and leaf/axiom/index/lint logs same discriminant-actions prefix. stable-coordinate-native-port.json latest_verified_batch=discriminant-actions-audits.json; candidate discriminant_actions_candidate complete; all batch plan steps complete. 4new modules,26theorems,29public declarations. All four final plain `lake --old env lean <leaf>` checks empty, all29 standard axioms only (propext/Classical.choice/Quot.sound), exact path+name searchback, all owned imports exactly once, fresh .lake objects and no source-tree objects. No full/umbrella builds, no heartbeat increases, no mathematical computations. All owned handles terminal (audit14681 exit0, finalizer62281 exit0). Removed2API+2Python scratch helpers; retained /tmp/paper-discriminant-actions-axioms.lean.

Cumulative555owned leaves /4592public mathresults. StableCoordinate117source+112applications=229modules /2430historically audited public declarations. 86prior stored source hashes freshly revalidated unchanged; latest completed_modules now90hashed+139legacy unhashed rows. Never assume all historical rows have sha256. New modules only; no historical Lean leaf edited this batch.

Ledger CHANGED during work. Refreshed ALL39 headings plus Needs and E/Lean-evidence fields directly from explicitly authorized docs/reports/rh-current-frontier-map.md (386lines), no referenced cards opened. Still16live+23candidate routes. Latest read/audited hash f45a56364d27f4df067500d7277050cfb80e639d02439fd089bc98225a21ad67. Candidate MSC now explicitly requires nondiagonal/nonpower transport mixing Dirichlet coefficients across n; real-rooted polynomial and transcendental LP z-multiplier obstructions referenced via Lean. Other refreshed core needs retained in ledger; no claim this algebraic batch closes an arithmetic RH input.

Four new leaves under formal/GaloisForLFunctions/HTGeometry:
1 PaperDiscriminantAdditiveActions.lean (3defs5thms):
- paperDiscriminantAdditiveAction q for q:paperDiscriminantTranslationConstants K n integrates q•δ by source exponentialAction; local nilpotence paid by previous multiplier iff.
- derivative=qδ; exact root coaction C(root_i)+C(q)*X, alln.
- paperDiscriminantActionSpeed rho :translationConstants K(n+1), underlying element=rho.derivation(firstroot). Invariance follows from complete prior LND classification.
- complete derivation equals recovered speed timesδ; rho equals action(speed rho); speed(actionq)=q.
- paperDiscriminantAdditiveActionEquiv K n: invariant coefficient algebra ≃ ALL PolynomialAdditiveAction K orderedDiscriminantOpen K(n+1). No unproved action/derivative hypotheses.
2 PaperDiscriminantActionGeometry.lean (9thms):
- paperDiscriminantRoot_algHom_ext for maps to ANY semiring K-algebra; root values determine full localization hom. Uses IsLocalization.algHom_ext +MvPolynomial.algHom_ext; noCharZero needed.
- Every arbitrary action has exact linear root formula with recovered speed.
- fixed iff speed=0 OR δ(element)=0. Every action fixes entire invariant coefficient algebra; universal invariants of ALL actions exactly translation kernel.
- each scalar specialization maps root_i→root_i+q*algebraMap(t), fixes invariant coefficients; ALL scalar specializations of ALL actions commute, using root algHom ext. These specialize maps have source-proven specializeEquiv inverses.
- empty-root algebra: every polynomial additive action trivial.
3 PaperNativeClockMultipliers.lean (7thms):
- exact LND(q•D) iffDq=0 for all native constant vector fields (any variable type), actual paperStabilizedClock, literal polynomial-extension clock, and every intrinsic fibre clock t:Complex,i:Fin3.
- stabilized clock weighted by its own distinguished stabilize f is NOT LND, since clock(stabilize f)=1.
- common multiplier q preserves ALL3 intrinsic fibre clocks iff q is complex scalar, using paid native common-kernel theorem.
- coordinate multiplier j on clock i is LND IFF i≠j, uniformly everyfibre: cross-coordinate shears survive; same-coordinate Euler weights fail.
- local domain/CharZero fibre instances paid by proven exactFiberEquiv; no extra hypotheses.
4 PaperSplitPolynomialClockMultipliers.lean (5thms):
- weighted piPolyDeriv iteration evaluated at component equals iterate of weighted polyDeriv on that component, over ANY commutative coefficient ring.
- for characteristic-zero fieldK, LND(q•piPolyDeriv K n) iff∀i,(qi).derivative=0 iff∀i,qi=C((qi).coeff0).
- arbitrary independent scalar component speeds yieldLND; coefficientX on each component is NOT LND for any nonemptyproduct.
- Includes emptyproduct. Crucially ambient product ring may have zero divisors; necessity reduced to each domain component (test LND on constant polynomial-valued function, project iterate), sufficiency uses invariant multiplier lemma requiring NOdomain. Uses actual native AffineLineEtaleLocallyNilpotent.piPolyDeriv, not a replacement operator.

Novelty BRIDGE: proven source coaction/exponential +top-iterate mechanisms meet native geometry/fibre/stabilized/split polynomial clocks. No claim of new general coaction/LND theory or RH closure.

Searches: discriminant-actions-search.json deep partialFalse, completeinventory70074, source compiler mostlypending/stale; all used claims checked in Lean. discriminant-actions-native-clocks-search.json lexical exact locallyNilpotent excludingPaperStableCoordinate, total20/eligible20 inspected allLean hits. Source CoactionAction.lean (NOT nonexistent CoactionSpecialization.lean) contains specialize, specializeEquiv, invariant_iff_derivation_eq_zero and toAlgHom_eq_of_derivation_eq. Also read native AffineLineEtaleLocallyNilpotent and PolynomialEtaleLocallyNilpotentDomain interfaces; actual finite-etale lift extension remains next work, not claimed done. Those OLD files already have heartbeat options; none introduced or modified, all new leaves checked at defaults.

Lean lessons:
- For source action coefficients, FIRST rw[exponentialAction_toAlgHom], THEN extcoeff/simp. simp[exponentialAction] unfolds ofCoeffLaw and hides the projection, leaving coeff goals.
- Concrete speed nilpotence initially200k timeout; fixed by explicit `(K := K)` and `(q : PaperRootDiscriminantOpen K n)` in paperDiscriminantTranslation_smul_locallyNilpotent_iff. No heartbeat increase.
- q.property has rational restrictScalars derivative syntax; use a separate typed private speed_constant :δ(q)=0 for rw; direct exact q.property works by defeq, rewriting with raw q.property does not matchδ.
- Do not `rw[paperDiscriminantZero_derivation_eq_zero]` with unspecifiedD; pattern is metavariable. Use explicitρ.derivation or source action_eq_C_of_derivation_eq_zero.
- Polynomial.eval_C has implicitargs, exact Polynomial.eval_C works. Polynomial.aeval_C (priorbatch) takes root then coefficient.
- Weighted product iterate proof: inductionm generalizingf; rw[iterate_succ_apply,ih,iterate_succ_apply];rfl.
- Negative polynomialX speed proof `simp at he` avoids unnecessarySimpa warning.
New Mathlib probes passed: coeff_mul_X, iterate_derivative_eq_zero, eq_C_of_derivative_eq_zero, Function.Injective.isDomain, MvPolynomial.algHom_ext, IsLocalization.algHom_ext, Polynomial.eval_add/mul/C/X.

Latest global lint15FOREIGN unwired leaves, noownedfailures: RHTower.Sieve.MatomakiTeravainenReflectionArithmetic; UnitBlockFrequencyBounds, FrequencyComparison, FrequencyDecay, PoissonKernel, PoissonSummation, Reflection, ReflectionDualBlocks, ReflectionFourthMoment, ReflectionMoment (allUnitBlock prefix); HTGeometry.IntervalIntegralHolderSwap, MonotonePhaseFirstDerivativeTest, QKrawtchoukCompanionTriangular, QuantileRearrangementEnergy, SmoothPlateau. Busy sharedtree; do not modify foreignwork. Index refreshed6changedfiles.

Next goal work recorded (NOT yet proved):
- Recheckupstream; broaden source-mechanism searches to native Euler/grading derivations and coefficient-mixing transports relevant to refreshed HF/EWJ/MSC and others. Establish actual Lean interfaces before claiming route relevance; derive positive invariant classifications with obstructions.
- Extend finite-product multiplier iff to native finite-etale derivative lifts using existing splitting+liftuniqueness; build missing explicit transport identity (do NOT assume total algebra domain).
- Exact arbitrary-speed criterion for native localized fibre clocks: pay denominator and zero-speed/degenerate localization boundaries.
- Concrete discriminant translation constants presentation by root differences +inverse discriminant still interesting/pending; intrinsic chart and ALLadditive-action classification complete, avoid redundant wrappers.