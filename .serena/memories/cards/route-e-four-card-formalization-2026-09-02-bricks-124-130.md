# Route E four-card formalization, 2026-09-02, bricks 124–130

New unconditional, axiom-clean leaves, all imported by `GaloisForLFunctions.RHTower` and targeted-built only:

- `Sieve/KloostermanProductFrequencySliceBound.lean`: arbitrary noncoprime product-period frequency slices, injective/nonzero, harmonic chord sums, terminal/stored correlation bounds. Build 13484/13484; 16 public theorems.
- `Sieve/KloostermanProductHarmonicQuadratic.lean`: signed modulus/source aggregation through terminal/stored Gram and quadratic/off-diagonal. Build 13485/13485; 6 public theorems.
- `Sieve/GrowingReciprocalMarkerSubpowerSchedule.lean`: exact h,w,H schedule; equations (1),(2), H=X^(1/2+o(1)). Build 2009/2009; 7 public theorems.
- `Sieve/CoprimeSquareRootLogLogSchedule.lean`: exact h=(log log(3x))^(1+eta); h/loglog→∞, h→∞, h/x→0, eventual 10≤h≤x, log h/log x→0, square-root window log exponent 1/2. Build 2009/2009; 6 public theorems.
- `Sieve/GrowingReciprocalMarkerBlockCount.lean`: exact Nat floor K=floor((log h-w)/log2)-4, K→∞, K/log h→1/log2. Build 2010/2010; 3 public theorems.
- `Sieve/GrowingReciprocalMarkerMenonRate.lean`: exact equation (17) schedule-rate arithmetic; both logX-normalized Menon RHS envelopes tend 0. Build 2011/2011; 4 public theorems.
- `RHTower/CofactorAmplifiedScaleSeparation.lean`: exact T=U^(2eta), large-prime scale quotient U^(1/2-3eta)/(logU)^(a/2), divergence for eta<1/6, eventual support separation with any positive constant. Build 2009/2009; 3 public theorems.

All new theorem axiom audits returned only `[propext, Classical.choice, Quot.sound]`. Direct `lake env lean` checks passed. `scripts/formal_tools.py lint` has only pre-existing unrelated umbrella-reachability errors; new leaves are wired. Task scratch files removed/no `/tmp/hgt_*` remain. No task-owned Lean process remains; observed unrelated PIDs for `/tmp/hgt_native_countermodels.lean`, `/tmp/haar_proto.lean`, `ScratchApartment.lean` and did not touch.

Cards remain Stage 2 honestly:
- cofactor + forbidden-support: shared hard core is collective spectral cancellation at MT paper ranges, Lemma 3.5(ii), amplification, Theorem 1.2.
- coprime square-root: exact general-h representation theorem still needs all-interval short-interval input/physical multiplicity; fixed subpower replacements and schedule are done.
- growing marker: schedule, block count, and equation (17) arithmetic done; missing quantitative Menon–Halasz mean-square theorem and moving-scale normalization into (15).

Progress notes appended at EOF of relevant cards and MT programme. Do not move any card yet or introduce hypotheses.