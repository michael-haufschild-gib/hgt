# EDQ full mixed current Gram — verified

Goal ACTIVE: unconditional closed Lean proof/falsification of RH by Euler deletion → exact complex zero balance → signed arithmetic separation → off-line zero exclusion → RH. RH remains open. No route retired. Previous turn was verified progress (completed horizontal contact), revalidated from current source/frontier/STATUS at turn start. This turn establishes full finite mixed-current orientation with an explicit finite prefix certificate. No external blocker; do not mark goal complete/blocked.

## New leaf and exact results
formal/GaloisForLFunctions/RHTower/EulerDeletionMixedCurrentGram.lean, 407 lines.
Namespace RHTower.DeletionMixedCurrent. 18 public theorems, 3 defs, 6 private helpers.
Imports ONLY EulerDeletionReflectedCurrentEnergy; existing dependencies cached.

S:Finset Nat, c:Nat→Complex. Nontrivial index p>0 means actual modulus p+1.
mixedPath S c s n = sum p∈S c_p*eulerDeletionWeightedJump p s n.
quadraticCurrent S c s = sum p∈S sum q∈S c_p*star(c_q)*variationCurrent p q s (partner s).
mixedEnergy S c s n = (weight s(n+1)-weight s n)*norm(endpoint(mixedPath S c s)(n+1))².
ALL off-diagonal currents retained; no arbitrary Gram substitute.

Public:
- mixedPath_partner: common real reflection weight acts on the whole complex superposition.
- mixed_chronological_tendsto: in open strip the actual mixed chronological difference converges to -quadraticCurrent, before zero specialization.
- mixed_endpoint_bound at actual rho: norm mixed prefix ≤ [sum normc_p*A_p(rho)]*(N+1)^(-Re rho).
- mixed_energy_tendsto: at every actual zero, full COMPLEX current equals the limit of cast real energy partial sums. Both endpoints and amplified endpoint vanish; amplified endpoint ≤ combined A²/(N+1).
- hasSum_mixedEnergy: genuinely summable signed real series at every actual zero.
- quadraticCurrent_eq_energy: exact full complex quadraticCurrent = cast real tsum mixedEnergy at actual zero. Thus no imaginary quadratic response survives.
- deletion_coefficients_independent_initial S c hS M hM hz: indices 0<p≤M, coefficient relations at positions n=0..M force all c_p=0.
- deletion_coefficients_independent: same from all coefficient positions.
- exists_nonzero_mixed_prefix_initial: for nonzero vector supported on 0<p≤M, every COMPLEX source parameter s has some n≤M with endpoint mixed(n+1)≠0. No zero premise, no height premise.
- exists_nonzero_mixed_prefix: unbounded witness wrapper, chooses M=S.sup id.
- mixed_energy_initial_pos/neg: the first M+1 mixedEnergy terms already have strictly signed finite sum at EVERY source parameter on respective side, for every nonzero finite vector.
- mixed_energy_prefix_le_current/current_le_mixed_energy_prefix: every finite Gram prefix bounds the full current at actual zero, correct side orientation.
- quadraticCurrent_re_pos/neg: strict sign at every actual right/left zero for every nonzero finite complex vector.
- quadraticCurrent_of_re_half: full current vanishes on the critical line BEFORE any zero premise.
- quadraticCurrent_eq_zero_iff (line382): at actual rho, Q=0 iff Re rho=1/2 OR all c_p=0 on S.

This does NOT assert existence of off-line zeros. It does NOT prove universal Q or diagonal J vanishing. Finite-vector cancellation cannot supply a null direction at a hypothetical off-line zero, but an independent source law forcing vanishing would still be an RH proof. No route retired on this conditional classification.

## Paper proof
Finite bilinearity expands C(mixed,mixedPartner) as complete sum cp*starcq*Cpq.
Apply existing weighted_cross_identity to actual mixed path (same weight all channels).
At actual zeros each constituent endpoint tends0, combined tail bound makes wN*norm mixedEndpoint²→0. Full quadratic current becomes real signed energy. One-sign terms give HasSum.
Coefficient independence: at integer1 all nontrivial coefficients=1, so sumc=0. Strong induction on channel p, evaluate at integerp+1; proper divisor indices are smaller and their coefficients already vanish, leaving -(p+1)c_p=0. Only coefficient positions0..M needed for indices≤M.
Successive prefix differences and nonzero Mellin kernel transfer this to finite prefix detection (lengths1..M+1).
Every weight increment strictly positive right, negative left; detected prefix makes finite Gram sum strict. HasSum transports finite inequality to complete current; nullspace classification follows.

## Verification COMPLETE — do not repeat
API scratch /tmp/edq_mixed_api.lean verified tools, final API session62060 exit0.
Final scratch /tmp/edq_mixed.lean session17079 exit0, EMPTY diagnostics.
Copied exact scratch, added single import after EulerDeletionReflectedCurrentEnergy in RHTower.lean.
Final foreground LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionMixedCurrentGram session99637 exit0. ONLY new leaf Built (7.1s); graph12965 cached/replayed jobs.
New-only axiom audit /tmp/edq_mixed_axioms.lean session17012 exit0: all21public declarations depend ONLY propext, Classical.choice, Quot.sound. Closure covers6private helpers. No added axioms, admissions, unsafe/native_decide, numerical premises or external computation certificates.
Lint ONCE session78686 exit1: sole UNRELATED unwired module GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactSourceEleven. No error in new leaf. Other work untouched; do not claim global lint pass.
Search-index ONCE exit0:4changed0removed,32942files401925declarations3945gaps. Exact no-refresh capstone query returns new line382.
Scoped whitespace/local links, exact source equality, one umbrella import, forbidden-declaration scan, owned-process checks passed.
Removed all3 owned scratch .lean files; no owned Lean/Lake process left.
Logs retained /tmp/edq_mixed.{api,check,build,axioms,lint,index}.log.
No full/umbrella build, no commit/push, no subagents, no old axiom rechecks.

## Docs
Positive card docs/drafts/pipeline/3-formalized/edq-mixed-current-gram.md (moved from1-in-progress).
Contains dependency-closed paper proof, explicit finite detection strengthening, exact formal certificate, precise unrelated lint limitation, cleanup.
Current frontier: added mixed-current paragraph after diagonal-current energy; updated EDQ established/remaining columns. Current-state only.
STATUS: MUST-RETAIN-THE-FULL-QUADRATIC-FORM, route-independent compact requirement. Also restored blank between preceding owned multiplicity/interior-sign entries.
No failed-route card: this is an exact definite response, not an unconditional falsification of a prospective independent source law.

## Corpus inspected
EulerDeletionReflectedCurrentEnergy full; ReflectedChronologicalCurrent1–150; CompletedChronology1–125; HolomorphicChronology281–349; HorizontalContact139–244.
EulerDeletionDirichletGram1–250: ordinary Dirichlet Gram law and centering, different source from prefix current.
CoprimeBlockCarryTransgression blockDeletionCoefficient exact definition.
EulerDeletionQuasiShuffleConvergence coefficient and partialSum definitions.
Broad no-refresh searches mixed energy/current/reflection/polarization, coefficient independence, prefix Gram and bounded prefix detection. Some broad searches returned unrelated theta/Weil kernel forms; not substituted.
No need to redo old derivations.

## Lean/API lessons
tendsto_finsetSum is current spelling; tendsto_finset_sum deprecated.
Complex.cpow_ne_zero DOES NOT EXIST; use Complex.cpow_ne_zero_iff (x≠0 OR y=0).
star over Finset sum: first rewrite Complex.star_def, then map_sum/map_mul. Expanding products of two sums with mul_sum first orders outer q before p; in cross_mix swap RHS p,q once, then commute N with both finite sums.
For cross at partner, make separate hrev:=cross_mix S c(partner s)N; simp only[partner_partner]at hrev; do not rewrite ←partner_partner globally (causes triple partners).
Complex cast in lambda must have full inner parentheses: fun N => (((sum...):Real):Complex). Otherwise parser casts the function.
Always space ≤ s and ≤ mixedEnergy: adjacent ≤s/≤m can invoke graph/matroid notation and create absurd Graph.re errors.
Use Finset.le_sup (f:=id) hp explicitly; elaboration cannot infer f from p≤S.sup id.
Use push Not; push_neg deprecated.
To simp branch-dependent identities then ring only remaining goals without no-go errors/linter: by_cases; all_goals simp [...]; all_goals ring.
In reflection complex-ext equality, norm_num[partner,hs] closes numeric real-part goal.
Finite sum positivity Finset.sum_pos' hnonneg ⟨index,mem,positive⟩; Summable.sum_le_tsum finset (fun n notmem=>nonneg).
Cast real tsum convergence via Complex.continuous_ofReal.tendsto.comp hasSum.tendsto_sum_nat; no HasSum.hasSum field.

## Remaining direction
The scalar diagonal current J already strictly orients horizontal displacement at actual zeros and J_1 universal vanishing is exactly RH. This turn shows all finite complex mixed directions are definite with finite detection; it does not supply an independent annihilation law. Completed halves have a modulus-independent horizontal pair, and odd critical multiplicity forces cofinal negative source neighborhoods, so blanket interior positivity remains unavailable. A further comparison must retain the actual asymmetric response/full completion phase or use a genuinely additional source constraint, not merely choose coefficients to cancel this finite Gram form.