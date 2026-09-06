# Compatible attenuation curvature checkpoint — 2026-09-06

## Active goal and honest boundary
The unbounded RH architecture goal remains ACTIVE. No qualifying radically new architecture, no zero-forced curvature identity, and no RH proof have been verified. Do not mark the goal complete or blocked because this auxiliary loop finished. Every new turn must start in chat with the full proposed proof chain, proved/missing links, and how the new work advances it. Current proposed chain: literal deletion source -> infinite joint object -> additional identity forced by an actual zeta zero -> off-line exclusion -> RH. The last two arrows are missing; convergence alone is not a selector. This turn eliminated a repair; it did not close those arrows.

User excludes Suzuki/Hedenmalm/Weil positivity/Connes/Burnol/Hilbert–Pólya, all spectral, Gamma, and other usual/relabelled RH cores. Earlier exclusions include Möbius, Bessel/Hankel, theta/Xi, resolvent, recurrence. Corpus-native search plus rg actual bodies is mandatory. Never infer novelty from absent hits. No subagents were used. No mathematical computations were run this turn.

## Completed exact theorem
New production: formal/GaloisForLFunctions/RHTower/EulerDeletionCompatibleCurvature.lean (352 lines), namespace RHTower.DeletionCompatibleCurvature, wired immediately after EulerDeletionPrimeAttenuation in RHTower.lean.

For positive contractive completely multiplicative b, define L_d=d/b(d), A_d(n)=1-L_d[d|n], W_alpha(n)=b(n)^2*n^(-alpha), Z=sum W. Actual curvature coefficient is A_p*A_q^2+A_pq*A_r^2-A_q*A_r^2-A_p*A_qr^2. It was defined from these four channels, not from its claimed answer.

Lean proves:
- coefficient_mul, coefficient_sq; curvatureCoefficient_linear = (L_q-1)*(A_pq-A_q+L_r*(A_qr-A_pqr)).
- summable_massWeight for alpha>1 by domination; mass_pos from b(1)=1.
- tsum_divisibilityWeight by actual injective n->d*n reindexing: sum_[d|n] W=b(d)^2*d^-alpha*Z.
- tsum_coefficient_mass = Z*(1-d*b(d)*d^-alpha); no nonzero-b(d) premise needed in this lemma.
- summable_curvature_mass.
- curvature_eq = Z*(q*b(q)*q^-alpha)*(1-p*b(p)*p^-alpha)*(q/b(q)-1)*(1-r^(2-alpha)).
- curvature_neg for 1<alpha<2; curvature_zero_at_two; curvature_pos for alpha>2; curvature_eq_zero_iff alpha=2. Labels >1 pairwise coprime. General theorems explicitly state their elementary data conditions, with no RH premise.
- normalized_curvature_invariant: if b(p)=b(q)=1, curvature/Z is EXACTLY original deletionFactorizationGradeCurvature/deletionDirichletMass. Other weights, including r, may change arbitrarily within class.
- fifth_attenuation_normalized_curvature: entire b(n)=c^v_5(n), 0<c<=1 family has unchanged normalized 2,3,5 curvature after compatible repair.
- premise-free fifth_attenuation_curvature_boundary fixes c=1/5: multiplier25, curvature negative at3/2, zeroat2, positiveat3.

Key survivor: (r/b(r))*(r*b(r)*r^-alpha)=r^(2-alpha). The reciprocal normalization cancels the attempted attenuation. This is an exact invariant and full sign boundary, closing the attempted compatible repair. Alpha=2 means Re(s)=1 in alpha=2Re(s), NOT RH critical line. No theorem says arbitrary CM b retains original ordinary convergence domain; earlier one-prime admission theorem only supplies that specified family/label repair.

## Validation completed; no owned live processes
Scratch directory /tmp/hgt-compatible-curvature-Pe4gsu.
Names.lean passed handle68414 after fixing generic universe inference by specializing Summable.of_nonneg_of_le to Nat and div_pos to Real. All names used by final proof checked against current toolchain.
Audit.lean includes final body plus eight #print axioms, passed handle67006. All eight report only propext, Classical.choice, Quot.sound. Audits: curvatureCoefficient_linear, tsum_divisibilityWeight, summable_curvature_mass, curvature_eq, curvature_eq_zero_iff, normalized_curvature_invariant, fifth_attenuation_normalized_curvature, fixed capstone.
Production byte-matches Compatible.lean and audited body. Narrow final lake build GaloisForLFunctions.RHTower.EulerDeletionCompatibleCurvature passed handle44049 (leaf4s; only inherited PolydiscWeierstrass warning). No full/umbrella build ran.
Repository-wide python3 scripts/formal_tools.py lint PASSED handle5036. Output /tmp/hgt-compatible-curvature-Pe4gsu/lint.log. Earlier concurrent OneDimBrascampLieb and QuarticJensenDispersionTransfer reachability errors were cleared by other work; historical certificate docs now note subsequent lint success. Do not rerun unchanged checks.
No prohibited source constructs; new relative links resolve; scoped git diff --check passes. All owned Lean/build/lint handles finished. Process check found no real owned jobs. No SSH/Runpod jobs this turn. Preserve unrelated concurrent edits, particularly HTGeometry/chronological and excluded RH source files.

## Documents completed
- docs/drafts/pipeline/2-fully-proven/euler-deletion-compatible-curvature.md: full dependency-closed paper proof, normalized invariant, source-admission boundary, literature scope. Original in-progress card moved here.
- 3-formalized/euler-deletion-compatible-curvature.md: exact theorem and validation certificate.
- 5-failed/euler-deletion-compatible-attenuation-repair.md: exact no-go + strongest positive survivor closed in Lean.
- STATUS.md MUST-ATT2: normalization can cancel apparent reduction in inputs; recompute full observable. Self-contained high-level guidance.
- rh-corpus-architecture-audit-2026-09-05.md Open obligations and rh-current-frontier-map.md EDQ row updated.
- prior prime-attenuation-shortcut failed card links follow-up; prior paired-prime and prime-attenuation certificates record subsequent global lint PASS.

## Corpus/literature audit this turn
Started from actual EulerDeletionFactorizationGraded, FactorizationCurvature, FullEnergyFactorization and PrimeAttenuation, paired search+rg. Queries: weighted multiplicative mass; curvature normalization multiplicative; deletion gauge; divisibility weighted multiplicative. No located generalization is NOT novelty evidence.
Primary source opened: Cranston–Peltzer, On Properties of the Riemann Zeta Distribution, https://escholarship.org/content/qt4kv3q5r6/supp/r-zeta_072721.pdf. Section3 equations5–9 give classical divisibility mass and coprime independence. Extension to arbitrary summable completely multiplicative weight is same elementary reindexing. Do NOT promote this auxiliary identity as a novel RH architecture. Search exact Euler deletion curvature attenuation did not establish global absence.
Follow-up search zero endpoint transport: PerfectReturnPathRigidity is explicitly spectral (tridiagonal eigenvectors); excluded, not adopted. InvolutiveProjectiveWedgeTransportLaw is elementary exterior algebra and its zero theorem assumes FactorsThrough / InvariantUnder; no producer for needed quotient. chronological annihilator search no hits. rg EulerDeletionMixedWordBoundary and ChronologicalScheduleBoundary reconfirms zero closure gives carry limits and retained collision charges, not their annihilation.

## Next work
Need return to actual zero-forced identity / new admissible architecture, not another claim that convergence or smaller coefficients selects zeros. Current loop is fully closed with positive survivor. No pending code fix or computation. Earlier checkpoint: `mem:rh/prime-attenuation-admission-2026-09-06`; paired-prime and joint product memories remain relevant. The ONLY prior Runpod computation is documented in paired-prime memory and computations/deletion-multiplicativity-tangent, completed with no active process; never use its outputs as Lean certificates.
