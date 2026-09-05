# Nonlinear visible/feedback audit
Goal active; RH and bounded C_N(r) returns unproved. No new theorem/mechanism this turn. Mathematical outcome is a stricter, verified account of existing source laws; do not present as an RH advance.

STATUS edits: F86 compressed losslessly and extended with the exact Deninger connection on its actual domain; added F86a visible-addition/indefinite-incidence/zero-jet facts; corrected covariance MUST-202 from sufficient implication to unconditional Lean equivalence. Document 4993 lines at end; unrelated concurrent F658/CANNOT-294/MUST-204 and duplicate old ids preserved. git diff --check passed.

Verified exact core:
- `VisibleCoprimeMobiusLaplaceAddition`: Phi(x)=sum mu(n)e^-nx obeys sum_(gcd(a,b)=1)Phi(ax)Phi(by)=Phi(x+y), x,y>0, with absolute convergence. All 525 lines read across chunks.
- `VisibleCoprimeZetaZeroJet`: primitive Mellin symbol zeta(s)zeta(t) invZeta(s+t). Mixed m,m jet at rho,conj rho is |zeta^(m)(rho)|² invZeta(2 Re rho); exact Xi multiplicity m, reciprocal filled by0 at1. Real sign = sign(2 Re rho-1), vanishes iff critical. FULL file read.
- `MobiusCoprimeInertiaUnbounded` full read: arbitrary negative inertia (one per prime is enough). Related coprime factorization and signature=Mertens are ALREADY Lean, not new hypotheses to conjecture.
- `DeningerMobiusConnection` FULL read: Lambda*mu=-(mu log), and sum Lambda(m) f_h(mx)=-sum mu(n)log n H_h(nx) for h in DeningerExpSchwartz, x>0. Do NOT claim its exact theorem already covers H=e^-x without checking domain; that log-pull seed is not Schwartz at minus infinity.
- `MobiusMertensFiniteSectionEnergy` 1-140 and490-EOF read: `mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_iff_riemannHypothesis` is now unconditional. Littlewood converse really imported/discharged. Earlier summaries calling this converse missing are stale. `MobiusCoprimeSignatureRH` full confirms unconditional signature iff RH.

Verification `/tmp/hgt_nonlinear_source_frontier_audit.lean`, `lake env lean` cwd formal, session61514 EXIT0. Six #check/#print axioms targets: visible addition, mixed jet formula, mixed jet iff, unbounded negative inertia, Deninger connection, covariance returns iff. Only propext/Classical.choice/Quot.sound. All imports cached. No Lean edits/new leaves, no builds, all owned processes terminal.

Failed candidate chain:
1. Stack genuinely nonlinear visible-addition constraints on escape profiles. Mellin kernel already cancels zeta factors; mixed jets classify orientation but no vanishing producer. Raw pairing is indefinite. Higher-arity/moment rhetoric cannot assume positivity.
2. Recast mu-log identity as additive-versus-dilation feedback. The arithmetic source connection already exists; no dissipativity or uniform energy estimate established. A Frullani/log-derivative restatement would be a bridge, not a new mechanism. No non-patched survivor was extracted beyond existing exact classifiers. NO NEW POSITIVE SALVAGE FOUND.
Private speculative ideas NOT proved/adopted: finite logarithmic divisor generator conjugate to log(n) diagonal, nonaccretivity in Gamma metric; thermal Laplace kernel infinite negative inertia; normalized escape compactness. Do not treat these as new facts; corpus and hostile audit required if revisited.

Other direct reads: MobiusCoprimeProductSignExtraction full (Boolean splitting preserves mu coefficient); VisibleCoprimeMellinSymbol symbol surface only; MobiusBoundaryOppositeSignTransport1-260 (already sign-reversing prime replacements and friable gap n<=y^4 dist, transport is consumer); MobiusLogDivisorParaproduct full.

External: user arXiv2609.03539 is plasma KP/Hirota paper, perturbative governing equations and bilinear solution methods (HTML2609.03539v1 checked targeted); arXiv2609.04037 is disordered XXZ time-crystal simulation paper, finite sizes/times and QFI diagnostics, not a uniform arithmetic theorem (HTML2609.04037v1 targeted). No new arithmetic map found. Searches polluted with unverified RH proof claims; none accepted. Existing source identities are not evidence of novelty; no literature-priority claim made.

Working constraints: only direct Lean/corpus, no cards; skill read fully; no computations; one foreground Lean process; scratch checking, missing needed oleans only, no umbrella/full builds; apply_patch edits; preserve other agents; goal cannot be marked complete.