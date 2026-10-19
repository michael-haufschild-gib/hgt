Active unbounded 100-contribution BVI goal from /Users/michael/.codex/attachments/1779f711-01d4-4e0f-a4c6-c5d914630176/pasted-text-1.txt; accepted 0/100. Latest user asks to use actual corpus search and avoid missing existing work. No hgtl7, no subagents, README read-only, no experiments/certificates, no added axioms, public capstones data/admissible subtypes only. One owned Lean/build command at a time; targeted dependencies with --old, original-source audits lake env lean, no umbrella/full builds. Session init/manual/memories/README complete earlier; docs/architecture.md and docs/testing.md absent. update_plan unavailable; cards track work.

Mission: exact finite-horizon divisor correlations that retain arithmetic structure without full-period averaging.

CURRENT OWNED LEAN RUN: session 31943, lake env lean --setup /tmp/bvi100-two-prime-stable.setup.json /tmp/bvi100-two-prime-pair-bound.lean. Collect before another Lean/build or editing this file. Previous run29399 PASSED the raw finite squarefree-pair bound with no diagnostics. The draft now imports MobiusMagnitudePatternDensity and adds public moebiusFirstBandAdjacentOneCount_le(t L) and moebiusFirstBandAdjacentOneDensity_le (density of the band1 (1,1) pattern ≤7/18). These additions are unverified. Setup map adds JointCongruenceClass, JointCongruence, ShiftedCongruenceCount hardlinks, with unique scratch module name BVI100TwoPrimePairBound. All older Lean/lint sessions closed. New corpus search /tmp/bvi100-two-prime-native-gradient-research.json has just been launched; collect its exec session from latest tool output. Paper card now includes finite native target E_N(M)≥2*W_N−7N/9−18 for N≥1,M≥2N (W_N squarefree count in (N,2N]); restrict to interior first-octave edges, endpoint cost≤2, pair bound cost≤16. This avoids identifying the full Euler product; native proof and duplicate audit still pending.

COMPLETE NEW LEAF:
formal/GaloisForLFunctions/BezoutValuationIncidence/CofinalMobiusMagnitudeObservablesAndGradient.lean, 141 lines, 5 public declarations. Original-source check clean, all 5 #print axioms standard propext/Classical.choice/Quot.sound, wired immediately after CofinalMobiusJointMagnitudeLaw.lean. Actual lexical index readback all 7 names/docstrings reviewed (5 public+2 private). Logs /tmp/bvi100-joint-magnitude-observables-{canonical,axioms,lint}.*, index /tmp/bvi100-joint-magnitude-observables-index-readback.json. Completed /tmp/bvi100-joint-magnitude-observables.lean and -axioms.lean removed.
Public:
- cofinalMobiusMagnitudeObservableMass(K:ℕ+)(t:Icc 0 1)(h:Fin m→ℕ)(Φ:(Fin m→ℝ)→ℝ): sum over a:Fin m→Fin(K+2) of Φ(realcast a)*cofinalMobiusJointMagnitudeMass K t h(realcast a).
- tendsto_moebiusMagnitudeObservableMean: literal sum Φ(abs source(n+h_i)) over n≤floor((K+t)N), divided by N, tends to that mass. No continuity/boundedness assumptions; eventual finite alphabet.
- cofinalMobiusMagnitudeGradientMass: above with m=2,h_i=i,Φ=(x1-x0)^2.
- tendsto_moebiusMagnitudeGradientMean: literal adjacent squared absolute-value differences/N tends to gradientmass.
- eventually_moebiusGradientMean_ge_magnitudeMass(K)(t)(ε:Ioi0): eventually gradientmass−ε≤literal signed-source gradient energy/N.
Private source_magnitude_finite bounds magnitudes by Fin(K+1) for n≤(K+1)N; shifted_source_magnitude_finite uses N≥sum h_i to get Fin(K+2).
Optimization removed redundant eventually N≥1 in final comparison. Main finite-count equality closes with simp only[...] then congr 4; extra ext/simp gives No goals.

Earlier COMPLETE chain (details in prior memories):
MobiusMagnitudePeriodicApproximation.lean 279 lines/7 public; exact rough factor, local period j!*primorial R², source-band identity, joint disagreement count.
MobiusMagnitudePatternDensity.lean 330 lines/13 public; fixed-band frequencies, |density-localdensity|≤m/R, local convergence, finite support and total mass1; reuses searched SelbergCompactTestApproximation.exists_limit_of_eventual_approximation.
CofinalMobiusJointMagnitudeLaw.lean 364 lines/11 public; boundaryerror≤1+sum h_i, fractional band transport, affine raw mass Σ_{j<K}density_j+t*density_K, literal full-horizon joint frequencies, support and normalization.
All original-source/public-axiom audited, wired/indexed.

GLOBAL LINT latest: exit1, exactly 3 OTHER-OWNER umbrella gaps, 381 size warnings:
BiScaleUncertainty.SieveLinearVisibility
BiScaleUncertainty.SievePrimePowerVisibility
TransHorizonIncidenceMechanics.FermiBooleanPrimeCube.
Previous FermiDyadicAntichainCoordinates gap cleared. Do not alter unrelated leaves or claim global lint pass.

DEPENDENCY BUILD CONCURRENCY ISSUE AND TEMP INPUT SNAPSHOT:
Other owner runs lake build arithmetic-positivity-theory.FactorialCriticalPrimeContinuousKernel (PID30596 observed), replacing shared .olean files while checks load them. Do not stop or modify others' processes.
Own targeted builds:
- lake --old build ...SelbergGcdLogLocalIdentity passed
- lake --old build ...CofinalMobiusJointMagnitudeLaw restored multiple missing objects but failed because concurrently missing SelbergGcdLogAsymptotic; removed owned periodic .olean
- targeted --old build WeilWorkSingularArithmeticSummatory, Sieve.TwistedSelbergCoefficient, Sieve.LinearMollifierGcdForms passed. More live files changed during these runs.
Restored periodic module via clean original-source lake env lean --setup /tmp/bvi100-periodic-stable.setup.json -o/-i canonicalfile. That passed; then observable original source and axiom audits passed with corresponding stable setup maps.
Appending LEAN_PATH fallback DOES NOT WORK: Lean.Util.Path.findWithExt chooses first package directory, not first existing module file. Confirmed against installed source.
Working stabilization: hardlink cached Galois dependency inputs under /tmp/bvi100-artifact-snapshot and rewrite only Galois paths in compiler importArts setup map. Other libraries/options/source unchanged. 9398 base artifacts plus four joint-chain extras and new observable leaf.
Active helpers:
 /tmp/bvi100-snapshot-dependencies.py (reads periodic setup importArts, hardlinks live missing snapshot modules; use python3 scripts/run_guarded.py --timeout120 -- python3 ...).
 /tmp/bvi100-periodic-stable.setup.json
 /tmp/bvi100-observables-stable.setup.json
 /tmp/bvi100-observables-axioms-stable.setup.json
All point to hardlinks, not symlinks. Original periodic setup is formal/.lake/build/ir/.../MobiusMagnitudePeriodicApproximation.setup.json with 18205 recorded imports.
For scratch importing native modules, copy stable setup and give unique name (avoid same module name as imported leaf); add any new imports to importArts using their frozen .olean paths. For new original-source module use exact module name. Additional dependency graph from .ilean directImports rows [name,bool,bool,bool]. No heartbeat/recursion changes.
Snapshot is still retained for active next native proof because shared build continues; remove it and owned setup/helper files once no longer needed. Never delete shared .olean files. Restored owned periodic object now exists again.
Logs /tmp/bvi100-magnitude-periodic-restore.*, /tmp/bvi100-joint-magnitude-{missing-dependencies,observables-dependencies}.*.

ACTIVE CARD:
docs/drafts/pipeline/1-in-progress/bvi-joint-magnitude-law-2026-10-19.md (~400+lines), updated main type THEOREM(Lean); formalization gate checked; explicit coercivity/Euler/support/novelty remain open. Programme row updated. No accepted contribution.
Smaller explicit gradient target now recorded with complete paper argument:
C=consecutive squarefree pair density (exists from band1 pattern law), D=6/pi².
A squarefree adjacent pair avoids 0,-1 modulo4 and9, so CRT gives C≤(1−2/4)(1−2/9)=7/18.
Thus magnitude difference mean 2(D−C)≥2D−7/9>2D/3 (π<22/7 implies D>7/12).
At horizon2N band1 source is −μ; initial/endpoint exceptions bounded. Gives eventual signed-gradient energy≥(2D−7/9−ε)N, uniformly every longer horizon by nonnegative summands.
Renormalized defect consequence ONLY at fixed finite horizon ratios, where existing endpoint error/N vanishes; do not claim endpoint control for arbitrary superlinear horizons.
This weaker target avoids full Euler products/AP density and already improves old odd-squarefree bound. Generic CRT estimate not novelty credit.
Original 5D/6 target via C/D≤(2/3)*(7/8)=7/12 still unproved Lean; exact Euler/support characterization also open (classical Mirsky basis).

CURRENT TWO-PRIME SCRATCH:
 /tmp/bvi100-two-prime-pair-bound.lean (~122 lines), imports JointCongruenceClass and Mathlib.Data.Nat.Squarefree. No numerical enumeration.
Public scratch theorem squarefreeSuccessorCount_twoPrime_le(t L:ℕ):
 (# {n∈Ioc t(t+L)|Squarefree n∧Squarefree(n+1)}:ℝ)≤(7/18)*L+8.
Uses indicator expansion 1−A−B−C−D+AC+AD+BC+BD for divisibility4/9 at n,n+1.
Four negative congruence counts and four positive intersections each have error<1, from existing abs_card_filter_dvd_add_shift_sub_lt, exists_joint_solution, abs_card_joint_sub_lt.
All substantive proof parts passed previous elaboration; only current fixes await check.
Nat.dvd_add_iff_left has orientation k∣n → (k∣m ↔ k∣m+n); use .mpr on n+1 after commutation to deduce q∣1.
Nat.card_Ioc, NOT Finset.card_Ioc.
Use algebraic four_coprime_nine from Nat.coprime_two_left.mpr ⟨1,rfl⟩ and Nat.Coprime.pow 2 2 (no need norm_num gcd plugin).
Last linarith only selects four lower bounds +four upper bounds.
Next: once raw bound verified, add native band1 density cap C≤7/18 and gradient consumer, then original-source/axiom/wiring/index/lint/cleanup. Do not promote/count generic finite sieve bound alone as novel.
Useful inspected Mathlib: ArithmeticFunction.abs_moebius: |μ n|=if Squarefree n then1else0; Nat.squarefree_iff_prime_squarefree has p*p, not p^2. Nat.coprime_two_left in Data/Nat/Prime/Basic.lean. Existing tendsto_const_div_atTop_nhds_zero_nat; le_of_tendsto_of_tendsto in Topology/Order/OrderClosed.lean.

SEARCH AUDIT COMPLETED THIS CONTINUATION:
All 252 UNIQUE lexical squarefree residue names/docs reviewed, pages0,20,...240 saved /tmp/bvi100-squarefree-residue-lexical-*.json. These were names/docs, NOT full proof audits. Most unrelated analytic residues/gauges; relevant PMRamanujanBandResidue gives coprime squarefree weight mean, not single residue AP mean.
Each following hybrid file: all20 candidate+20 source statement records reviewed, partial=false, semantic coverage not_measured, background indexer refresh; no absence/priority claim:
 /tmp/bvi100-squarefree-residue-mean-research.json
 /tmp/bvi100-moving-shift-hull-research.json
 /tmp/bvi100-squarefree-uniform-shift-research.json
 /tmp/bvi100-squarefree-pair-local-upper-research.json
Lexical profinite limit returned2 unrelated names/docs both reviewed, /tmp/bvi100-profinite-limit-inventory.json.
ShiftedCongruenceCount.lean full short source read this continuation; JointCongruenceClass exact public signatures inspected (full file read earlier).
A broad rg -A8 on enormous EulerDeletionTruncatedDivisorPairCorrelation output truncated; DO NOT claim full file reviewed.
Primary web new: https://arxiv.org/pdf/1212.3150 Reuss Pairs of k-free Numbers, consecutive square-full Numbers, intro/Theorems2–3 read. Explicitly notes Heath-Brown pair method uniform h≪x; generic moving-shift squarefree laws cannot count as new. Not all28pages read. AMS Mirsky PDF returned403; not used as content evidence.
Earlier K-P/Lemanczyk/Weiss arxiv1406.3745 classical Mirsky cylinders/full support and Cellarosi–Sinai baseline in card remain.
