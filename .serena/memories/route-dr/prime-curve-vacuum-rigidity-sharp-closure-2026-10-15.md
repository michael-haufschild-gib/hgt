# DR actual-prime-curve vacuum rigidity: closed

Goal remains active: unconditional fully formalized RH through DR actual Kummer-root topology and a zero-free half-strip. Read `/Users/michael/.codex/attachments/eed7f621-2c9d-4192-b680-7007faf58bcf/pasted-text-1.txt` at the start of each goal turn. Apply hgtl7. No external literature searches, numerical experiments, or old research Markdown reads. Current Lean, own current cards/log are allowed. No full or umbrella builds; one owned foreground Lean at a time, cwd formal, `lake --old env lean`. Do not pivot because an obstacle is unsolved.

Closed the precise smooth-vacuum candidate, including its strongest positive survivor. The card and original coefficient dependency are now archived at:
- docs/drafts/pipeline/5-failed/route-dr-prime-curve-vacuum-regularity-2026-10-15.md
- docs/drafts/pipeline/5-failed/route-dr-prime-curve-vacuum-coefficient-work-2026-10-15.lean
Own live log: docs/drafts/pipeline/1-in-progress/route-dr-corpus-loop-2026-10-15.md (large; read relevant tail only).

Exact theorem: H=ell²(real primes), v(sigma)_p=p^-sigma, sigma>1/2. If a C^k germ G near 0, k>=1, matches log|zeta(sigma)| on the actual curve for sufficiently large real sigma, then DG(0)[e_p]=1 for all p<=2^k and ||DG(0)||>=sqrt(pi(2^k)). The explicit finite-C^k model attains this bound. No single C-infinity germ matches the actual Euler curve. No arbitrary finite-packet agreement is assumed.

Production modules, all in namespace RHTower.PrimeCurveModel except noted helpers:
1. PrimeCurveFiniteSmoothModels.lean (previous turn, 578 lines): actual curve, summable zero-extended tail, explicit finiteSmoothModel, genuine Euler identity, C^k existence.
2. PrimeCurveFiniteSmoothJets.lean (new, 198 lines): cutoffReader/vector, model derivative, exact norm, norm_lowerBound_of_prime_coordinates, no_bounded_all_prime_reader, exists_finiteSmoothGerm_with_derivative. The latter uses order k+1.
3. PrimeCurveTaylorControl.lean (new, 332 lines): generic radial Taylor in RHTower.PrimeCurveTaylor; farPrimeCurve, primeTruncation, error o(N^-sigma), strict-derivative transfer, truncated_radial_taylor_isLittleO for N<2^(k+1).
4. PrimeCurveVacuumRigidity.lean (new, 431 lines): coefficient separation helpers in RHTower.PrimeCurveCoefficient; finite multilinear expansion over prime words, prime-degree-one isolation, sharp actual-curve derivative extraction. Main declarations: prime_fderiv_zero_of_vanishing_curve_sharp, prime_fderiv_eq_one_of_euler_curve, norm_fderiv_lowerBound_of_euler_curve, no_smooth_euler_curve_germ (line 418).
All new modules imported in RHTower.lean after Models at lines 19107-19109.

Proof mechanism: Taylor remainder O(||x||^k); prime-curve truncation at N has omitted norm <=(N+1)^(1-sigma)||v(1)||, hence o(N^-sigma). C^1 strict derivative transfers curve vanishing to truncations. Finite Taylor polynomial expands into a finite genuine Dirichlet series. Prime frequency only has degree one. k>=2 uses p<2^k; k=1,p=2 uses Frechet little-o directly. Subtract explicit model, then use Hilbert/Riesz impossibility of a bounded all-prime reader.

Validation: direct production Lean checks all exit 0, silent. Needed oleans built individually for Models, Jets, Control, Rigidity. Final scratch #print axioms for positive model, Taylor transfer, sharp vanishing, norm lower bound, and smooth no-go: only propext/Classical.choice/Quot.sound. Formal lint exit 0 with repository large-file warnings; index exit 0. Final cached lexical search finds all three new main declarations. No full build. Temporary scratch/search/log files were prepared for exact owned-path cleanup; final log records cleanup status.

Paper Kummer corollary, not separately packaged in Lean: a smooth complex R with R(0)!=0 and R(v(sigma))^d=zeta(sigma) yields forbidden smooth G=d log|R| on a smaller neighborhood. Do not claim a Lean theorem for that complex-valued conversion.

FALSE for this smooth vacuum producer; sharp finite-order survivor fully formalized. Scientific novelty/significance beyond standard Taylor/Dirichlet/primality/Hilbert arguments remains unestablished. No RH certificate or zero-free half-strip gained. Only this producer class is retired, not DR. Next unresolved work: actual arithmetic attachment of Kummer roots retaining the singular first trace, without hiding continuation or zero exclusion in premises. Complete proof goal remains active; no external blocker. No subagents authorized. Enum paths before reads; do not guess names. Use plain `rm --` only on exact owned scratch paths, no wildcards/shared process cleanup.