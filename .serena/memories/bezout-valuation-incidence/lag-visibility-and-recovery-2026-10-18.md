# Contribution011 — exact arithmetic visibility and recovery

Completed after the user cleared the 250-contribution goal and explicitly asked to finish work already started. Stop this research run; do not resume the old goal without a new request.

Four verified field leaves: RamanujanLagCoefficientAndTotientQuotient (124 lines,7 named,5 public), ValuationVisibilityClockAndRamanujanSupport (128,9,8), TrueTranslationPredictionAndExactCompression (222,13,11), ArithmeticLagSchedulesAndSharpRecoveryHorizon (217,14,14). Total691 lines,43 named declarations,38 public declarations.

Exact actual factorial-cycle pairing at lag h: sum_q R(q,h)Y_b(q)Y_c(q). R is the Möbius inverse of gcd CRT compatibility. Normalized multiplier lambda(q,h)=mu(q/gcd(q,h))/phi(q/gcd(q,h)), including zero cases. The existing finite inverse gives K_h c, the actual squared-error minimizer: Err_h(c,b)=Err_h(c,K_h c)+Q(b-K_h c). Every minimizer agrees on active coefficients; K_1 equals the existing coprimality predictor there.

Visibility clock D(q)=q/rad(q), factorization v_p(D)=v_p(q)-1. lambda(q,h) != 0 iff q!=0 and D(q)|h. First positive visible lag D(q); p^(a+1) has clock p^a. Finite schedule H gives equal observations iff Y agrees on every mode covered by some lag divisible by D(q). Equivalent to equality of selected predictors. Complete recovery iff every active mode is covered; missed modes have concrete invisible unit-coordinate inverse witnesses. Consecutive lags1..T recover iff max_(q<=N)D(q)<=T; single h recovers iff lcm_(q<=N)D(q)|h. One-step prediction and every positive iterate erase exactly inactive/nonsquarefree pure modes; true shifts reveal an active erased mode at multiples of D(q). No full semigroup classification. Recovery concerns source coefficients; optimal shifted-signal error can remain positive. No noise or conditioning bound.

All four original sources separately checked with lake --old env lean and empty diagnostics, one owned Lean process at a time. All38 public declarations (including defs) audited with only propext, Classical.choice, Quot.sound. All43 named index entries and38 cache/API rows checked, all4 imports unique, artifacts installed atomically. Initial global lint passed; final lint after a concurrent leaf appeared exited1 only for foreign unwired ShiftedExponentAsymptoticDensityAndActiveMartingaleRate.381 foreign large-file warnings, no owned/proof-debt finding.40 field leaves at final inventory.

Guarded cleanup removed all33 owned temporary paths, including scratch bytecode; all jobs terminal. Source/artifact/axiom-log hashes checked before/after. README read-only; concurrent growth to429 lines preserved. No commit/push, external search, numerical experiment, hgtl7, RH focus, full build or heartbeat changes.

Card: docs/drafts/pipeline/3-formalized/bvi-arithmetic-visibility-and-translation-memory-2026-10-18.md
Ledger: logs/bvi-root-2026-10-18-knowledge.md
Raw axioms: logs/bvi-root-2026-10-18-lag-visibility-axioms.txt
Full commands, hashes, audit and cleanup manifest: logs/bvi-root-2026-10-18-lag-visibility-audit.json

Count once as contribution011; classical Ramanujan formulas and the finite inverse are supporting infrastructure, not separate contributions.