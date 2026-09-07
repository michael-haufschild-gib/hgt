# EDQ completed horizontal contact — verified

Goal remains ACTIVE: unconditional closed Lean RH proof/falsification through Euler deletion → exact complex zero balance → signed arithmetic separation → off-line zero exclusion → RH. RH not proved/falsified. This turn rules out only blanket interior positivity and retains a stronger positive contact classification. No mathematical difficulty should be reported as an external blocker.

## New verified leaf
formal/GaloisForLFunctions/RHTower/EulerDeletionHorizontalContact.lean, 244 lines.
Namespace RHTower.DeletionHorizontalContact. Eight public theorems, one definition, nine private helpers.
Imports EulerDeletionHolomorphicChronology, RiemannGaussian.FiniteToEntireRealApproximation, ArithmeticJointJetExclusion.

A_p(s)=DeletionHolomorphicChronology.completedSplit p s; p>0 means actual modulus p+1.
horizontalPair p rho d=Re A_p(rho+d)+Re A_p(rho-d).
horizontalPair_eq_xi_sq: critical center Re rho=1/2 and 0<d<1/2 give exact pair=Re(genuine RiemannGaussian.riemannXi(rho+d)^2).
horizontalPair_channel_independent: exact finite pair is identical for all nontrivial moduli.
exists_horizontal_contact (actual NontrivialZetaZero rho, critical): exists ONE B>0, forall p>0, pair/d^(2*m) tends as real d↓0 to (-1)^m*B, where m is full analyticZetaZeroMultiplicity rho.
odd_contact_negative/even_contact_positive: exists ONE B>0 and ONE epsilon>0 for ALL p>0; for 0<d<epsilon, odd gives pair ≤ -B*d^(2*m)/2, even gives pair ≥ B*d^(2*m)/2.
exists_high_simple_center T: actual multiplicity-one critical zero above every real T, from old unconditional cofinal simple-critical census.
exists_high_negative_source p>0 T: some source s in open strip above T with Re s≠1/2 and Re A_p(s)<0.
not_eventually_nonnegative_completedSplit p>0: negation of exists height above which Re A_p is nonnegative everywhere in strip.
Negative source points are NOT asserted to be off-line zeta zeros. The negative SIDE may depend on p: do not claim a common negative point for all moduli. The PAIR, contact magnitude and sign neighborhood are common.

Proof: analytic factorization Xi(z)=(z-rho)^m*g(z), analytic g, c=g(rho)≠0. FE/conjugation and ±d force star c=(-1)^m*c; Re(c²)=(-1)^m*norm(c)^2. Squared quotient converges. Choose p=1 sign neighborhood then shrink below 1/2 and transfer via exact finite pair identity. No infinite-family limit interchange.

## Verification (complete, no reruns needed)
API scratch /tmp/edq_contact_api.lean passed session15580.
Final scratch /tmp/edq_contact.lean passed session29101, exit0 emptydiagnostics.
Installed exact scratch and single import after EulerDeletionHolomorphicChronology in RHTower.lean.
Final foreground LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionHorizontalContact session37859 exit0; ONLY new leaf Built, 6.8s; graph13660 jobs cached/replayed.
New-only axiom audit session49704 exit0; all9 public declarations only propext, Classical.choice, Quot.sound.
Repository lint ONCE session73144 exit1: seven UNRELATED unwired modules MobiusDivisorTwoChannelPrimeBlocks, ThetaCuspEvenFourEffectiveErrors, ThetaCuspEvenFourEffectiveReserve, ThetaCuspEvenFourEffectiveSchur, ThetaCuspEvenFourExplicitTail, FirstAtomEvenTailReserve, HankelFourPerturbation. No errors in new leaf. Other work areas left untouched. Do not claim global lint pass.
Search-index ONCE exit0, 11changed 0removed,32939files401892declarations3945gaps. Exact --no-refresh capstone lookup returns new theorem line237.
Scoped whitespace/local links, single import, exact checked-source equality, forbidden-declaration scan passed.
All owned Lean/Lake processes gone. Three owned /tmp Lean files removed. Logs retained /tmp/edq_contact.{api,check,build,axioms,lint,index}.log.
No umbrella/fullbuild, no commit/push, no subagents, no old-axiom rechecks.

## Documentation
Positive card moved to docs/drafts/pipeline/3-formalized/edq-completed-horizontal-contact.md, paper + exact formal certificate + precise global lint limitation.
Failed shortcut card docs/drafts/pipeline/5-failed/edq-completed-global-accretivity.md. Scope blanket global/eventual high-strip nonnegativity only; strongest nontrivial positive survivor exact contact uniform across moduli, paper and Lean closed. EDQ not retired.
Current frontier paragraph, EDQ row and terminal shortcut row updated.
STATUS appended route-independent MUST-PRESERVE-MULTIPLICITY-IN-HORIZONTAL-SIGNS.
Old holomorphic boundary identity and current-vanishing gap remain valid; no location exclusion follows from the contact sign alone.

## Lessons
Always fully qualify RiemannGaussian.riemannXi in this import context: RHTower has another riemannXi. Initial scratch caught accidental mixing; final uses genuine Xi everywhere.
Avoid simp only [neg_pow]: it recursively rewrites (-1)^m; use rw [neg_pow] once then ring.
Rewrite normSq before pow_two simplification.
Complex.ofNat_re/im names absent; norm_num handles numerals.
Tendsto shift needs explicit type/target before mono_left nhdsWithin_le_nhds.
quotient congr' often requires explicit change eliminating Function.comp.
Odd1 witness explicit ⟨0, by norm_num⟩; no decide in final.
Root-relative docs edit must use root cwd, Lean cwd formal. Keep edits and dependent launches separate and verify failures before launching.
Use rg --glob '*.lean' to avoid giant .ilean output. Locate filenames before reads.
No need to repeat any completed audits. Next work must find a source comparison compatible with negative odd-critical neighborhoods and still constrain actual zero locations or force universal J=0.