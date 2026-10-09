# Literal Möbius-divisor Abel moment: one-sided barrier audit

Status: corpus and paper audit in progress; no new theorem claimed.

## Objective

Return to the actual signed RH-bearing source, rather than further consequences of normalized smoothing. Let R(M)=mobiusDivisorSquareRootAbelMoment M. Existing Lean proves RH iff one constant bounds |R(M)/M| for all M>=2, and also RH iff subpower bounds hold for this absolute normalized moment.

Candidate reduction: prove RH equivalent to an eventual uniform lower bound on R(M)/M, and likewise to an eventual uniform upper bound. Under false RH this would force both signs to be cofinally unbounded. A genuine arithmetic barrier on either side would then suffice; no such barrier has been proved here.

## Source-access restriction

Read research only as Lean corpus results returned by scripts/formal_tools.py research. No web, Markdown, direct source, or memory reads. No numerical experiments. Compile scratch and final Lean leaves directly; print axioms only in scratch.

## Current exact evidence

- CCMFUSuzukiMobiusDivisorAbelProducer defines primeFreeDivisorDefect N as sum log(m) minus the divisor summatory function plus 2*gamma*N. It has unconditional bound |defect N|<=24*sqrt N.
- The exact floor Möbius inversion recovers psiDefect from this divisor defect.
- R(M) is the sum over 1<=k<M of (sqrt(k+1)-sqrt(k)) times that signed Möbius recovery.
- R(M)=coherentSelbergSquareRootAbelMoment M +2*gamma*(sqrt M-1).
- riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded and riemannHypothesis_iff_mobiusDivisorSquareRootAbelSubpower already exist. Re-proving either is not progress toward the missing estimate.
- CoupledFloorMobiusAffineRieszHandoff already supplies a positive cofinal schedule with pointwise error <1/(N+1). Changing that schedule does not establish the actual normalized bound.
- CCMRectangularTwoSidedOscillation proves cofinal positive and negative power oscillation for xiRectangularWeilLogCoefficient when RH fails. This is a different kernel. No direct one-sided literal-moment result was found in the targeted MobiusDivisor search.

## Paper mechanism to audit

1. Transfer a one-sided bound on R(M)/M to the critical Mellin-Chebyshev resolvent on integer logarithmic samples, preserving the explicit Euler and polar-lattice edges.
2. Use an unconditional within-cell error bound to obtain a one-sided bound on the continuous positive logarithmic ray.
3. Add a constant (or negate then add a constant) to make this source nonnegative. Its Laplace transform differs from the known continued resolvent by a rational term with its only added real pole at zero.
4. Apply a proved Landau continuation principle for nonnegative Laplace sources. Real-axis regularity at every positive argument must force convergence for all positive Laplace parameters.
5. Exclude each strict-right zeta zero using its nonzero resolvent residue. Do not assume RH, absolute boundedness, or the desired continuation domain in this step.
6. Reverse implication follows from the already-proved absolute-bound criterion. Absorb any finite prefix to pass between eventual and global barriers.

Steps 2--5 require exact corpus hypotheses and a dependency-closed paper proof before formalization. Existing rectangular oscillation cannot be substituted for the literal source without a proved transfer.

## Work plan

1. Inspect the applicable Landau engine and source-power proof through Lean search.
2. Complete or reject the source-faithful one-sided paper reduction.
3. If complete and absent from the corpus, formalize the exact result, compile leaves, audit axioms, wire imports, lint, and record remaining arithmetic input.

RH remains unresolved. No external novelty claim.

## Positive inverse paper audit (2026-10-09)
For a continuous real source f, base b, and I_b f(t)=integral_b^t f, put R_a f(t)=exp(-a*t) I_b(exp(a*u)f(u))(t). Then R_a'=f-a R_a and R_a(b)=0. FTC gives a I_b R_a=I_b f-R_a. Define Kf=f+(1/2)R_(1/2)f-2R_1 f. Consequently I_b Kf=-R_(1/2)f+2R_1 f and I_b^2 Kf=2R_(1/2)f-2R_1 f. Thus f=Kf+(3/2)I_b Kf+(1/2)I_b^2 Kf. All inverse coefficients are positive. A one-sided constant bound B on Kf gives the same-sided bound B*(1+(3/2)(t-b)+(1/4)(t-b)^2) on f for t>=b.

The corpus raw Suzuki Green identity has G(t)=-(1/2)K(suzukiPsi)(t)+D(t), where b=unitRieszSuzukiBase and D(t)=(-f(b)/2+slope(b))*exp((b-t)/2)+(f(b)-slope(b))*exp(b-t). This boundary is uniformly bounded on t>=b. Hence a one-sided global Green bound gives a one-sided quadratic screw bound. No RH premise has been discharged yet.

Next: formalize the exact positive inverse and its order consequence; verify the existing screw subexponential endpoint; resolve the literal Abel log-lattice to real-aperture transfer. Never replace the last step by treating log naturals as dense.

## Lean progress: Green upper-barrier equivalence
Scratch compilation passed for the exact exponential-resolvent inverse, positivity of the inverse, upper/lower quadratic transfer, boundary retention, and RH iff the real-aperture Suzuki Green source is bounded above for t>=unitRieszSuzukiBase. Added leaf formal/GaloisForLFunctions/RHTower/CCMUnitRieszSuzukiGreenPositiveInverse.lean; final leaf compile and axiom audit pending.

The source target is still unresolved. Corpus search exposed an exact cell formula F(log X)=(N/X)F(log N)+T/X with |T|<= (log 4+5)X for N<=X<=N+1. Thus a one-sided nonnegative constant bound on sampled F transfers one-sidedly; no convex interpolation is required. Remaining link is the real-aperture equality F(t)/2=G(t)+polarCorrection(t)-archCorrection(t). The corpus currently supplied only the integer-logarithmic version. This must be proved, not inferred from samples. RH remains unresolved.

## Final leaf verification (2026-10-09)
Direct leaf audit `lake --old env lean GaloisForLFunctions/RHTower/CCMUnitRieszSuzukiGreenPositiveInverse.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCMUnitRieszSuzukiGreenPositiveInverse.olean` passed with no output/warnings. The module is wired into RHTower.lean. Corpus search refreshed and finds the unconditional equivalence at line 310; its metadata remains source_only, so direct compiler output is the verification evidence. All 23 public theorem axiom audits are currently running in the owned scratch process.

Global formal lint exited 1 with 12 unrelated umbrella reachability errors: ChronologicalBudgetGapLaw, PaleyWienerPoissonMajorant, ThetaCuspRatioKineticLeading.JetHeads, ThetaCuspRatioKineticLeading.KineticCoefficients, ThetaCuspRatioKineticLeading.MinorLeading, ThetaCuspRatioKineticLeading.ReflectionHeads, ThetaCuspRatioSourceConjugation; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No unrelated files changed. Scoped diff check produced no whitespace errors, including the new untracked leaf.

## Audit complete
All 23 public theorem axiom audits passed with exactly [propext, Classical.choice, Quot.sound]; no added axioms or sorryAx. Axiom scratch exited 0. Both owned scratch Lean files were removed. Final leaf has 23 theorems and the unconditional equivalence `riemannHypothesis_iff_unitRieszSuzukiGreen_boundedAbove`. This is progress toward reducing the signed premise, not an RH proof. The card remains in progress because the literal Mobius Abel receiver transfer and the actual one-sided bound are unproved.

## Next increment: real-aperture source identity
Previous turn classified as progress: positive Green inverse and one-sided Green RH criterion compiled and all 23 axiom audits passed. This increment targets the exact identity F(t)/2=G(t)+polarCorrection(t)-archCorrection(t) for every t>=base, then the literal one-sided Abel receiver. Planned paper mechanism: integrate the finite Chebyshev step sum at X=exp(t), obtaining integral_0^X psi(y)y^(-1/2)dy=2*sqrt(X)*sum_{k<=X}Lambda(k)-2*sum_{k<=X}Lambda(k)*sqrt(k). Match each reporter atom exactly and retain both completed-source corrections. No conclusion from log-natural samples alone.

## Real-aperture identity closed
Added formal/GaloisForLFunctions/RHTower/CCMUnitRieszSuzukiRealAperture.lean. Direct final leaf compilation passed without output, producing its olean. It evaluates the finite Chebyshev layer integral at every real X>0, identifies each reporter atom exactly, proves F(H)/2=G(H)+polarCorrection(H)-archCorrection(H) for H>=base, and derives RH iff the critical resolvent has a global upper bound. No extra hypotheses enter the equivalence.

Next scratch formalizes the signed cell estimate |F(log X)-(N/X)F(log N)|<=log 4+5, keeping the nonnegative attenuation coefficient, then RH iff the literal normalized Mobius Abel moment is eventually bounded above. On paper the finite prefix is absorbed by the sum of absolute values of its entries. Scratch currently checking; no endpoint verification claim yet.

## Dependency recovery and next signed mechanism
Receiver scratch initially stopped before elaboration because SuzukiSmallApertureGroundEnergy.olean was missing. Corpus search confirmed the source path formal/GaloisForLFunctions/RHTower/SuzukiSmallApertureGroundEnergy.lean. An owned direct leaf build is running; no source edits to that dependency.

Fresh corpus evidence for subsequent premise discharge: CCMFUSuzukiMobiusDivisorDilationChannels has R(M)=sum_{q=1}^{M-1} primeFreeDivisorDefect(q)*mobiusClippedAbelKernel(M,q), and an exact integration-by-parts form using primeFreeDivisorIncrement(n)*mobiusDilationRieszTail(M,n). The clipped kernel includes its terminal correction and zero extension. The proposed one-sided receiver would require only an upper bound on this signed correlation; no bound or sign theorem for individual channels was found or asserted.

Dependency recovery: SuzukiSmallApertureGroundEnergy compiled successfully. Import loading then found missing SuzukiLimitingLogGroundIdentification.olean; corpus-confirmed source was compiled successfully too. Neither dependency source was edited. Receiver scratch /tmp/hgt_mobius_abel_one_sided.lean restarted only after each failed import process exited; current owned receiver session is 21552. Real-aperture leaf is already wired, with final compile passed; combined axiom audit remains pending.

## Literal upper receiver formalized
Both new leaves passed final direct compilation without warnings: CCMUnitRieszSuzukiRealAperture and CCMFUSuzukiMobiusDivisorOneSided. Both are wired into RHTower.lean. The second proves RH iff there exist B and M0 with R(M)/M<=B for every M>=max(2,M0). Thus a one-sided eventual upper bound suffices for the exact original arithmetic source. Boundary constants, the positive N/X attenuation, and the finite prefix are all explicit. Below log 2, the exact finite prime sum is zero, so the resolvent is nonpositive; this also strengthened the interpolation lemma to all real t without a t>=0 premise.

Dependency recovery completed: two existing missing objects were compiled by direct leaf commands; a third reported missing object was available by the next retry. The guarded recovery helper then exposed ordinary proof elaboration errors, which were fixed. No dependency sources were modified.

Final combined axiom audit of all 18 public theorems is now running. Both new leaves and the tracked scoped changes have no whitespace diagnostics. RH itself is unresolved, and the lower-bound version from the original card remains unproved. Next substantive task is discharge of the one-sided upper bound, using source-preserving signed correlation/history identities; avoid another purely equivalent reformulation unless it removes an actual proof burden.

## Increment complete: verified upper-barrier receiver
All 18 public theorem axiom audits passed with exactly [propext, Classical.choice, Quot.sound]. Both new leaves passed direct final compilation without warnings and are wired. Endpoint: CCMFUSuzukiMobiusDivisorOneSided.lean:226, `riemannHypothesis_iff_mobiusDivisorSquareRootAbel_eventually_boundedAbove`. Real-aperture source identity: CCMUnitRieszSuzukiRealAperture.lean:223. Corpus index refreshed; search finds both statements. All owned Lean/Python scratch files removed and all owned commands are terminal.

Current formal lint exits 1 with six unrelated HTGeometry umbrella omissions: ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, CosineAlgebraicComponents. No errors concern the new leaves.

RH remains unresolved. The upper receiver is now fully formalized; the actual eventual arithmetic upper bound is open. The original lower-receiver variant is also open. Next goal turn should prioritize a substantive one-sided estimate on the literal divisor-defect/clipped-kernel correlation or observer-history formula, rather than more equivalent predicates. Corpus searches expose the observer clock and second-derivative bounds but did not yet supply their defining bodies; do not assume a curvature sign before reading those definitions through the corpus search tool.

## Next increment: signed observer-history estimate
Previous goal turn classified as progress: exact real-aperture transfer and eventual one-sided literal Abel receiver are formalized and audited. This increment will inspect the observer clock and source-history definitions through Lean corpus search, test whether the curvature has a definite sign, and then investigate whether actual source history satisfies a useful one-sided bound. No curvature or history sign is assumed before the definition audit. Priority is a substantive estimate, not another equivalent RH predicate.

## Clock cancellation: dependency-closed paper candidate
Corpus definitions now read: c(x)=x(x+1)(sqrt(x+1)-sqrt(x)), with the explicit product-rule second derivative in observerJetClockRealSecondDeriv. Put a=sqrt(x), b=sqrt(x+1), x>0. Algebra gives c''(x)=3*(3*a*b-(2*x+1))/(4*a*b*(a+b)). For x>=1, a*b>x, hence numerator positive. Also a*b<=x+1/2, giving c''(x)<=3/(8*sqrt(x)). The upper constant replaces the existing absolute 13/(4*sqrt(x)) estimate, but the essential advance is the sign. Apply the same two mean-value steps as the existing second-difference proof to get 0<observerJetCurvature(completedRieszHarmonicClockRatio,j)<=3/(8*sqrt(j+1)). Then negative source histories contribute nonpositively to the exact Abel moment.

Next: formalize this exact cancellation and signed curvature; inspect actual completedPrimePolarGammaHarmonicCharge and residual-history definitions before asserting any history estimate. No source-history sign or upper bound is assumed.

## Actual source definition and boundary discharge
Read through deep Lean search: q(k)=completedPrimePolarGammaHarmonicCharge(k)=(psiRemainder(k+1)+2*gamma)*(1/(k+1)-1/(k+2)). This is a Chebyshev-prefix charge, not a von-Mangoldt atom. The corpus proves q is absolutely summable and has total sum zero. Generic residual history is the second prefix sum after removing mass and drift at indices 0 and 1; SuzukiObserverJetLinearActionClassification already identifies it with the exact finite tail sum.

On paper, C=sum |q(k)| gives |mass_N|<=C and |drift_N|<=N*C. Thus the two boundary terms are unconditionally O(M). The substantive remaining candidate is O(M) control of sum_{j<M-3} max(history(M,j),0)/sqrt(j+1). Positive clock curvature would remove all negative histories from the required upper estimate. Do not replace q by prime atoms or invoke an unrelated Mertens moment.

### Positive observer curvature: verified iteration, 2026-10-09

Formalised `formal/GaloisForLFunctions/RHTower/SuzukiObserverJetPositiveCurvature.lean` and wired its theorem-area import. For every observer index j, the completed Riesz clock curvature is strictly positive and at most 3/(8 sqrt(j+1)). With W+(M) the sum of the positive parts of residual history divided by sqrt(j+1), absolute summability of the actual completed charge gives an unconditional constant B >= 0 such that R(M) <= B M + (3/8) W+(M) for all M >= 3. This discharges the mass and drift boundary estimate and removes negative history from the remaining upper estimate.

All 11 public theorems passed direct leaf compilation and the scratch axiom audit; only propext, Classical.choice and Quot.sound occur. Final leaf command: `lake --old env lean GaloisForLFunctions/RHTower/SuzukiObserverJetPositiveCurvature.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SuzukiObserverJetPositiveCurvature.olean`. Scoped whitespace checks produced no diagnostics. Corpus search refreshed and found the conditional RH endpoint at line 246. Search reported no partial result, but semantic coverage unavailable and an older coverage snapshot; direct Lean compilation is the verification evidence.

The global lint gate remains failing on seven unrelated umbrella reachability errors: RHTower.XiRealRootedApproxEigenLimitRH, RHTower.XiRealRootedEigenGaussianGrowthRH, and HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No edits made to those files.

Remaining substantive target: prove W+(M) <= C M for the actual arithmetic history, or find a sharper signed estimate that reaches the already proved eventual one-sided Abel upper receiver. The conditional endpoint does not prove this growth premise. RH remains unresolved. Classification: progress (curvature sign, improved curvature constant and unconditional boundary-premise discharge).

### Boundary asymptotics and energy audit: next iteration

Existing observer-history upper bounds found by corpus search require an RH-equivalent completed-source prefix bound. They cannot be used as unconditional producers. Audit the actual graph-energy weight before claiming it reaches the linear history scale.

Parallel paper target (single-agent work): strengthen the already proved linear boundary bound to boundary/M -> 0. For the absolutely summable completed charge q, write drift/M as the sum of q(k) times the truncated coefficient k/M. Each fixed coefficient tends to zero and is bounded by one; summability therefore gives dominated convergence. The mass is uniformly bounded, so mass/M -> 0. This removes boundary contributions entirely from normalized asymptotic upper growth. It leaves the positive-history arithmetic estimate unresolved.

Energy audit result: `completedRieszGraphIncrement_eq` identifies the graph increment as the square-root-mesh source edge divided by k+1. `summable_sq_completedRieszGraphIncrement` controls the squares of these divided edges. Recovering R(M) multiplies each graph increment by k+1; direct Cauchy-Schwarz introduces sqrt(sum_{n<M} n^2), of order M^(3/2). This calculation does not establish the required O(M) upper bound. It is a limitation of that estimate, not a no-go theorem for all uses of the energy.

A stronger and cleaner paper proof of the boundary limit uses only convergence of the partial charge, not absolute summability: D_N = (N+1) P_N - sum_{k<=N} P_k. Thus D_N/(N+1) is P_N minus its Cesaro mean and tends to zero. The literal completed charge has P_N -> 0, so its mass itself tends to zero and its normalized drift tends to zero. The normalized Abel moment and the normalized signed curvature-history sum therefore differ by a quantity tending to zero. Scratch proof written; compilation pending.

### Boundary asymptotics verified, 2026-10-09

Added `formal/GaloisForLFunctions/RHTower/SuzukiObserverJetBoundaryAsymptotics.lean` and wired the theorem-area import. Six public theorems prove the exact drift/Cesaro identity, normalized drift decay for any convergent partial-charge sequence, completed mass -> 0, completed drift/M -> 0, completed boundary/M -> 0, and the normalized Abel-minus-signed-curvature-history limit zero.

Final direct leaf command passed without diagnostics: `lake --old env lean GaloisForLFunctions/RHTower/SuzukiObserverJetBoundaryAsymptotics.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SuzukiObserverJetBoundaryAsymptotics.olean`. Scratch `#print axioms` audit passed for all six theorems; dependencies only propext, Classical.choice, Quot.sound. Scoped whitespace checks produced no diagnostics. Refreshed corpus search found the final asymptotic identity at line 110; no partial result, with semantic-coverage and stale coverage-snapshot warnings. Direct compilation supplies the verification evidence.

Current global lint failed on eight unrelated unreachable modules: RHTower.PaperCircleHeatInformation, RHTower.PaperHeatSelectionInformation; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, PaperFourierLLogL.Compress.Phase. These differ from the previous snapshot because the shared worktree is changing. No edits made to those modules.

Classification: progress, with unconditional boundary strengthening from O(M) to o(M). The arithmetic signed-history upper bound, or the sufficient positive-history O(M) bound, remains unproved. RH is neither proved nor falsified. Next substantive target remains control of history over indices growing with aperture; first check the Lean corpus for any existing localization/escape result before adding such a theorem.

### Growing terminal history region: paper target, 2026-10-09

Target a genuine unconditional arithmetic region, rather than another reformulation of the full open bound. Let A bound (k+1)|q(k)| for the actual completed charge; the elementary linear Chebyshev remainder estimate supplies such A. Define terminal positive action by summing max(history(M,j),0)/sqrt(j+1) over j in Ico(M-3-L,M-3). Assume 2*(L+2) <= M.

Paper estimate: every included j has 2*(j+1) >= M. Its tail-history formula has at most L+1 terms, each nonnegative weight at most L and each |q(k)| <= 2A/M. For L>=1 this gives |history(M,j)| <= 4A L^2/M. Also 1/sqrt(j+1) <= 2/sqrt M. There are L indices. Hence terminal positive action <= 8A L^3/(M sqrt M); L=0 is immediate. In particular the terminal region contributes O(M) whenever L^3 <= M^2 sqrt M, allowing widths of order M^(5/6). The larger interior history region remains open. Search prior corpus for existing terminal-region results, then formalise this exact finite estimate before claiming the region discharged.

Terminal-region dependencies checked through Lean search: the public `RHTower.abs_psiRemainder_le` supplies |psiRemainder(n)| <= 8n. Thus A = 8 + |2 gamma| gives |q(k)| <= A/(k+1). `observerJetResidual_history_eq_tail` supplies the exact finite residual-history kernel. No terminal cubic estimate appeared in the scoped search; coverage was partial on the exploratory query, so no exhaustive novelty claim is made.

The exact survivor to formalise is a finite bound with no RH premise: T(M,L) <= 8 A L^3/(M sqrt M) under 2(L+2)<=M. Under L^3<=M^2 sqrt M this is <=8AM. The full positive-history action splits exactly into its interior prefix and T(M,L). Therefore the open sufficient premise can discard this terminal region: for any schedule satisfying these width inequalities eventually, an O(M) bound for the interior prefix implies RH. The interior bound itself remains open. This is an arithmetic premise discharge, not a proof of RH.

The first scratch pass compiled the unconditional reciprocal-charge, pointwise terminal-history, and cubic terminal-action estimates. Added paper/Lean consequences: the linear terminal bound under the cubic width condition; the explicit growing family M=N^6, L=N^5 for N>=3 (sqrt(N^6)=N^3 and L^3=M^2 sqrt M); the exact interior/terminal split; and the conditional RH endpoint assuming only the interior positive-action bound for a width schedule. This second scratch pass is pending. The explicit sixth/fifth family records an actual growing region, not only a conditional width parameter.

### Growing terminal region verified, 2026-10-09

Added and wired `formal/GaloisForLFunctions/RHTower/SuzukiObserverJetTerminalLayer.lean`. Eight public theorems establish the actual arithmetic charge bound, terminal history bound, cubic terminal positive-action bound, linear consequence, explicit M=N^6/L=N^5 family, exact interior/terminal split, and the conditional RH endpoint using only the remaining interior premise. The constant is A=8+|2 gamma|; T(M,L)<=8 A L^3/(M sqrt M) under 2(L+2)<=M, and T(M,L)<=8AM when L^3<=M^2 sqrt M.

Final direct compile passed without diagnostics: `lake --old env lean GaloisForLFunctions/RHTower/SuzukiObserverJetTerminalLayer.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SuzukiObserverJetTerminalLayer.olean`. All eight scratch axiom audits passed with only propext, Classical.choice and Quot.sound. Scoped whitespace checks had no diagnostics. Refreshed corpus search found the cubic bound at line 117, linear bound at 161, explicit family at 180, and conditional RH endpoint at 211. Search was partial with stale-snapshot and unavailable-semantic-coverage warnings; direct Lean compilation is authoritative.

Global lint currently reports twelve unrelated unreachable modules: RHTower.CanonicalProductE1SecondDerivative; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, PaperFourierLLogL.Compress.Params, PaperFourierLLogL.Compress.Schedule, PaperFourierLLogL.Compress.Theorem, PaperFourierLLogL.Thermal.History, PaperFourierLLogL.Thermal.Piece, PaperFourierLLogL.Thermal.Spatial. No edits made to these modules.

Classification: progress, unconditional control of a growing arithmetic terminal region. RH remains unresolved. The open sufficient estimate is now the interior positive-history prefix O(M) for a permitted width schedule. Any attempt to cover the interior by repeating terminal estimates must retain the affine bridge between different cutoffs; the global boundary o(M) theorem does not automatically control those moving-clock bridge terms. All owned processes terminal; scratch files cleaned after audit.

### Interior propagation audit and fourth-power sampling target

Direct repetition of terminal-history estimates retains a cutoff-dependent affine bridge: history_M(j)-history_K(j)=(drift_M-drift_K)-(j+1)(mass_M-mass_K). Dropping or absolutely summing that bridge is not justified by the boundary/M -> 0 theorem. No unconditional interval-sign control appeared in the current Lean search.

Paper direction: use one-sided semiconvex interpolation, which is invariant under affine additions. A real sequence with second difference >= -K on [a,b] stays below its endpoint maximum plus K(b-a)^2/8; prove this by adding a quadratic barrier and the discrete convex maximum principle. For the actual Abel moment R, its first difference is (sqrt(n+1)-sqrt n)*(psiRemainder(n)+2 gamma). Nonnegativity of von Mangoldt, the elementary |psiRemainder(n)|<=8n bound, and decay of consecutive square-root steps should give second difference >= -C/sqrt n. On the aperture interval [n^4,(n+1)^4], gap is O(n^3), so the upper interpolation error is O(n^4), exactly the required linear aperture scale. Target: a verified one-sided fourth-power sampling criterion for the literal R, after checking prior Lean corpus and establishing all arithmetic curvature ingredients. The sampled arithmetic upper bound itself remains open.

Fourth-power paper proof completed. Use the existing exact half-order step gap and its monotonicity at the square base d=n^2, avoiding new differential calculus. With A=8+|2 gamma| and C=4A+1, the actual Riesz moment satisfies Delta^2 R(k)>=-C/n^2 for n^4<=k<=(n+1)^4. The proof retains the positive von-Mangoldt term; it only bounds the negative polar/clock terms. The discrete semiconvex maximum principle then gives R(M)<=max(R(n^4),R((n+1)^4))+(225/8) C M whenever n^4<=M<=(n+1)^4 and n>=1, since the gap is <=15n^3. Thus eventual upper boundedness of R(n^4)/n^4 is equivalent to RH via the existing eventual one-sided receiver. Negative sampled bounds are safely enlarged to max(B,0) when comparing aperture scales. Every positive aperture has a fourth-power bracket, proved by natural-number induction. Full scratch proof is being compiled; sampled arithmetic bound remains unproved.

### Fourth-power sampling verified, 2026-10-09

Added and wired `formal/GaloisForLFunctions/RHTower/MobiusRieszQuarticSampling.lean`. Seven public theorems prove the discrete convex maximum principle, sharp quadratic-barrier interpolation, existence of fourth-power brackets, the nonnegative source curvature constant, the actual arithmetic block curvature lower bound, unconditional interpolation between fourth-power endpoints, and the exact eventual fourth-power upper-bound equivalence with RH.

The endpoint at line 242 states: RH iff there exist B and N0 such that R(n^4)/n^4 <= B for every n >= max(2,N0). The unconditional gap estimate is at line 195; the arithmetic second-difference estimate is at line 108. The sampled upper bound itself remains open. This discharges all between-sample apertures rather than assuming a dense upper estimate.

Final direct leaf command passed without diagnostics: `lake --old env lean GaloisForLFunctions/RHTower/MobiusRieszQuarticSampling.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/MobiusRieszQuarticSampling.olean`. Scratch axiom audit passed all seven public theorems, with only propext, Classical.choice and Quot.sound. Scoped whitespace checks had no diagnostics. A temporary elaboration timeout was resolved by explicit reassociation of natural-number arguments before applying the arithmetic theorem; no heartbeat limit was changed. Refreshed corpus search found the new declarations, with partial results and unavailable semantic coverage; direct compilation supplies verification evidence.

Current global lint fails on seven unrelated unreachable modules: RHTower.StretchedBoseDefect, RHTower.WeilLogShiftDiagonalMoment; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No edits made to these modules. All owned processes terminal and scratch files removed after audit.

Classification: progress, unconditional arithmetic curvature and gap control reduce the required one-sided bound to fourth-power samples. RH remains unresolved. Next substantive target is the actual signed upper estimate at n^4, potentially using the perfect-square endpoint in the square-root source/divisor formulas; first search the existing Lean corpus for those special-aperture identities and bounds. Do not treat the proved equivalence as a proof of its sampled premise.

### Sampled-source producer audit

Previous turn classified as progress: unconditional fourth-power gap interpolation is verified. Current corpus search surfaced `RieszFunctionQuarterPowerOmega.exists_abs_rieszSeries_le_rpow`, apparently an unconditional quarter-power decay bound. Inspection of Lean source in `RieszFunctionExponentLaw` shows `rieszFunction x = x * rieszSeries x`; the displayed x^(-1/4) series bound therefore gives only x^(3/4) growth for the arithmetic function. It does not meet the RH-critical x^(1/4+epsilon) target. Do not treat this helper as a missing RH producer.

### Square-block source quadrature: paper target

At square endpoints, the square-root clock has unit mass on each block [s^2,(s+1)^2). Let E(k)=psiRemainder(k)+2 gamma and S(N)=sum_{1<=s<N} E(s^2). Positivity of von Mangoldt implies E(k)+k is nondecreasing. Hence every complete block response lies between E(s^2)-(2s+1) and E((s+1)^2)+(2s+1). Summing blocks gives S(N)-(N^2-1) <= R(N^2) <= S(N)+E(N^2)-E(1)+(N^2-1). The existing elementary bound |E(k)|<=A k, A=8+|2 gamma|, then yields |R(N^2)-S(N)| <= (2A+1)N^2 for N>=1.

This is an unconditional signed quadrature estimate, with the Gamma term retained inside the completed source. If formalised, it removes the varying square-root weights from the fourth-power sampling premise: the open upper estimate becomes S(n^2)/n^4 bounded above. Search prior Lean corpus before adding code. The ordinary square-sampled arithmetic sum remains unbounded by any currently established argument; do not mistake the bounded quadrature error for that missing bound.

### Square-block source quadrature: verified 2026-10-09

Added formal/GaloisForLFunctions/RHTower/MobiusRieszSquareSourceQuadrature.lean and wired its umbrella import. Reads used only Lean-corpus research output; no Markdown, memories, direct source inspection, or web.

Let R(M) be mobiusDivisorSquareRootAbelMoment M and S(N) be the sum over 1 <= s < N of psiRemainder(s^2) + 2*EulerGamma. Square-root clock mass on each [s^2,(s+1)^2) is exactly one. The corpus theorem psiRemainder_sub_ge bounds each weighted block between its endpoint source values, with error at most 2s+1. Telescoping gives:

- S(N) - (N^2-1) <= R(N^2).
- R(N^2) <= S(N) + psiRemainder(N^2) - psiRemainder(1) + (N^2-1).
- Since psiRemainder(1) = -1 and |psiRemainder(k)| <= 8k, |R(N^2)-S(N)| <= 9N^2. This improves the initially proposed constant and removes EulerGamma from the quadrature constant.

Six public theorems proved: block bounds; cumulative quadrature bounds; absolute 9N^2 quadrature bound; completed square-sample RH criterion at square cutoffs; uncompleted remainder criterion at square cutoffs; all-cutoffs criterion. Final endpoint:

RH iff there exists B such that, for every N >= 2,
sum_{1 <= s < N} (psi(s^2)-s^2) <= B*N^2.

The sparse criterion needs this normalized sum only at N=n^2 for all sufficiently large n. The EulerGamma completion is a lower-order finite-sum correction.

Verification: direct final leaf command lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/MobiusRieszSquareSourceQuadrature.olean GaloisForLFunctions/RHTower/MobiusRieszSquareSourceQuadrature.lean exited 0, no diagnostics. All six public theorems audited with #print axioms in /tmp: only propext, Classical.choice, Quot.sound. Scoped whitespace checks emitted no diagnostics. All three owned scratch Lean files removed after compilation/audit.

Global formal lint exited 1 for nine unrelated unreachable modules: RHTower.PaperCirclePhaseCancellation, RHTower.SincSeparatorMellin, RHTower.StretchedBoseDefect, HTGeometry.ApertureConeCalculus, HTGeometry.ApertureConeWinding, HTGeometry.ApertureLogTranslation, HTGeometry.ApertureOpenHistoryIdeal, HTGeometry.BoundaryCoronaCStarAlgebra, HTGeometry.ComplexRateGammaIntegral. No lint diagnostic concerned this module.

Remaining task: prove the one-sided quadratic upper bound for the unweighted square-source sum, or find another unconditional route. The quadrature theorem does not supply this arithmetic cancellation. RH remains unresolved; goal stays active. Corpus searches for a suitable signed Chebyshev square-sum producer returned no applicable theorem within reported partial coverage. Do not infer exhaustive absence from those searches.

### Selberg-input audit after square-source reduction: paper target

Lean-corpus search found PMSelbergPowerInputBoundary and PMSelbergSublinearPowerBoundary. Their positive power models satisfy the same coarse first and second Selberg inequalities. A uniquely tuned positive amplitude even makes the first Selberg response o(N). These are not the actual Chebyshev remainder; their purpose is to test which stated premises can force the new square-source bound.

Candidate exact boundary: for exponent sigma > 0 and amplitude c > 0, the square sum of pmScaledPowerRemainder sigma c has a uniform quadratic upper bound iff sigma <= 1/2. The value at source index 1 contributes only -(1+c). Otherwise each sample is c*s^(2*sigma). For sigma <= 1/2, bound s^(2*sigma) <= s. For sigma > 1/2, the block n <= s < 2n gives a lower bound n*n^(2*sigma), so a quadratic prefix bound would bound n^(2*sigma-1), impossible.

Intended obstruction: the existing tuned sigma=3/4 model has an o(N) Selberg response and both coarse Selberg inequalities, yet fails the exact square-source quadratic upper-bound target. Positive survivor: the sharp half-power classification above, not just a negative example. This rules out discharge from these abstract Selberg inputs alone; it does not refute RH or retire arithmetic-specific identities. Formal verification pending.

### Selberg-input square-source obstruction: verified 2026-10-09

Formalized the paper target in PMSelbergSquareSampleBoundary.lean and wired the module. Exact classification: for sigma > 0 and c > 0, the square-source sum of pmScaledPowerRemainder sigma c has a uniform quadratic upper bound iff sigma <= 1/2. The dyadic lower bound and exact finite correction are public theorems.

Combined the classification with the corpus's tuned sigma=3/4 model. The resulting counterexample simultaneously has positive amplitude below one, an o(N) first Selberg response, both coarse Selberg inequalities with the arithmetic constants, and no quadratic square-source upper bound. This rules out only deduction from these abstract inputs; the model is not psiRemainder.

No-go closure and positive survivor recorded in docs/drafts/pipeline/5-failed/selberg-inputs-square-source-bound-2026-10-09.md. Paper proof dependency-closed; all six public theorems compiled in the final leaf and passed #print axioms with only the standard three axioms. Whitespace checks clean. Global lint currently reports ten unrelated unreachable modules; exact list on failed-route card. All owned scratch Lean files removed.

A follow-up corpus search for exact Selberg/floor identities returned existing coarse estimates and the already-known weighted Abel identities, with partial coverage. No additional arithmetic cancellation producer was established. Do not revisit the discarded coarse-input deduction as though its premises sufficed. The arithmetic square-source upper bound and RH remain unresolved; goal stays active.

### Arithmetic square-residue decomposition: paper target

Second-grade asymptotic audit: CCMFUSuzukiSecondGradeAsymptotic normalizes by sum (k+1)*(sqrt(k+2)-sqrt(k+1)), not by the critical linear aperture. Its o(1) limit does not discharge the first-grade square-source upper bound.

New source-faithful target uses the corpus theorem sum_moebius_log_mul_floor. Set Q(N)=sum_{s<N}s^2 and V(N,d)=sum_{s<N}(s^2 mod d). Then, with a(d)=mu(d)*log(d)/d and A=N^2,

sum_{1<=s<N} psiRemainder(s^2) = sum_{d<=A} a(d)*V(N,d) - (1+sum_{d<=A}a(d))*Q(N).

Each quadratic residue row is periodic modulo d, giving
V(N,d)=floor(N/d)*V(d,d)+V(N mod d,d).
The incomplete-period component from d<=D obeys the unconditional bound
|sum_{d<=D} a(d)*V(N mod d,d)| <= D^2*log D, for D>=1.
Thus that component is already within the critical budget whenever D^2*log D <= C*N^2. The complete-period contribution, the complementary large-modulus contribution, and the scalar counterterm must remain jointly signed; no separate bound for them is claimed. Formalization pending.

### Arithmetic square-residue decomposition: verified 2026-10-09

Added formal/GaloisForLFunctions/RHTower/MobiusSquareResidueDecomposition.lean and wired the umbrella import. The exact arithmetic decomposition and period split from the paper target are proved. Seven public theorems:

- quadraticResiduePrefix_period_decomposition
- quadraticResiduePrefix_nonneg_le
- quadraticResiduePrefix_remainder_le
- abs_logMobiusQuadraticRemainderAction_le
- abs_logMobiusQuadraticRemainderAction_le_aperture_sq
- psiRemainder_squareSum_eq_quadraticResidues
- psiRemainder_squareSum_eq_periods_add_remainders

The actual square-source sum equals its signed complete-period sum plus logMobiusQuadraticRemainderAction N (N^2), minus the exact scalar counterterm. For 1 <= D and D^3 <= N^2, the incomplete-period contribution from moduli d <= D has absolute value at most N^2. This controls only incomplete periods, not the entire small-modulus contribution. Complete periods, larger moduli, and the scalar counterterm still require joint cancellation.

Verification: final direct leaf compilation with lake --old env lean and explicit .olean output exited 0 without diagnostics. Every public theorem passed a /tmp #print axioms audit with only propext, Classical.choice, Quot.sound. Scoped whitespace checks emitted no diagnostics. All three owned scratch files removed after verification.

Current global formal lint exits 1 for ten unrelated unreachable modules: RHTower.CCMGroundEnergyZeroSumBound, RHTower.CanonicalProductE1RealLineBounds, RHTower.PaperCircleFrequencyDensity, RHTower.PaperCircleFrequencyGeometry, HTGeometry.ApertureConeCalculus, HTGeometry.ApertureConeWinding, HTGeometry.ApertureLogTranslation, HTGeometry.ApertureOpenHistoryIdeal, HTGeometry.BoundaryCoronaCStarAlgebra, HTGeometry.PaperFourierThermalMetric. No diagnostic concerns this module.

Next candidate, not proved: use quadratic Gauss estimates to improve residue-prefix bounds and extend the controlled modulus range. Corpus search found GaloisForLFunctions.RHTower.HalfWeight.gaussQ_sq in QuadraticGaussSumFourthPower, with primitive coprime coefficient and general positive modulus, plus prime Gauss signs in QuadraticGaussSumSign. Search did not establish an applicable incomplete-prefix discrepancy bound; coverage was partial and semantic coverage unavailable. A full estimate must account for non-coprime Fourier frequencies and complete-period bias before claiming any gain. Do not silently assume residues are uniformly distributed.

RH remains unresolved; main goal remains active. All research reads stayed within Lean-corpus search output. No numerical experiments.

### Gauss completion ingredient: paper target

Corpus audit found exact primitive complete Gauss norms in QuadraticGaussSumFourthPower. No applicable incomplete quadratic-prefix estimate was returned in the searched coverage. The completion step requires a linear twist and cannot drop non-coprime frequencies.

Target: for q > 0 and a,b in ZMod q, let G(a,b)=sum_x stdAddChar(a*x^2+b*x) and K(a)={h:2*a*h=0}. Translation x=y+h and additive-character orthogonality give the exact identity
G(a,b)*conj(G(a,b)) = q*sum_{h in K(a)} stdAddChar(a*h^2+b*h).
Consequently norm(G(a,b))^2 <= q*card(K(a)). When 2*a is a unit, K(a)={0}, so norm(G(a,b))^2=q exactly, uniformly in the linear twist. This preserves the nonprimitive kernel rather than applying a coprime norm formula outside its hypotheses. The incomplete-prefix bound still needs Fourier completion and arithmetic control of the kernel cardinality.

### 2026-10-09 — Arbitrary-modulus quadratic Gauss completion verified

Paper proof and Lean proof are closed for the following ingredient, with every
positive modulus and no coprimality assumption. Write G(a,b) for the complete
quadratic Gauss sum and K(a) for the kernel of multiplication by 2a. Translation
by a difference variable and additive-character orthogonality give the exact
identity G(a,b) conjugate(G(a,b)) = q times the character sum over K(a).
The kernel has cardinality gcd(q, (2a).val), by a bijection with multiples of
q / gcd(q, (2a).val) in (0,q]. Therefore

    norm(G(a,b))^2 <= q * gcd(q, (2a).val).

Finite Fourier inversion gives exact weighted and interval completion. The
geometric-series identity bounds each nonzero interval coefficient by the
minimum of its length and 2 / norm(1 - stdAddChar(-b)). The existing corpus
lemma RootOfUnityCompletion.sum_two_div_norm_exp_sub_one_le supplies the full
nonzero-residue reciprocal-chord bound, with no unit restriction. Consequently

    norm(sum_{n < N} stdAddChar(a * n^2))
      <= sqrt(q * gcd(q, (2a).val)) * (2 + log q),  N <= q.

Formalized in:
- formal/GaloisForLFunctions/RHTower/SquareResidueQuadraticCompletion.lean
- formal/GaloisForLFunctions/RHTower/SquareResidueQuadraticInterval.lean

Both final leaves compiled directly with lake --old env lean, exit 0 and no
diagnostics. Both are imported by RHTower.lean. All 26 public theorems were
audited with #print axioms in a scratch file: only propext, Classical.choice,
and Quot.sound. Scoped whitespace checks were clean. Global formal lint exited
1 solely for six unrelated unreachable modules: StretchedBoseNonDensity,
ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
ApertureOpenHistoryIdeal, and BoundaryCoronaCStarAlgebra.

Remaining: apply the Gauss bound to the least-residue observable in
quadraticResiduePrefix, retaining its zero-frequency mean, the complete-period
bias, and gcd-weighted nonzero frequencies. Then bound the actual signed
logarithmic Mobius action jointly with the remaining moduli and scalar
counterterm. The new complex exponential-sum estimate does not itself bound
that real residue action. RH remains unresolved; the goal remains active.

### 2026-10-09 — Centered small-modulus action: paper target

The actual least-residue Fourier identity is now proved in
MobiusSquareResidueFourier.lean. Its zero coefficient is q(q-1)/2; every
nonzero coefficient satisfies (stdAddChar(-a)-1) F(a)=q. The Gauss bound
therefore controls the centered real prefix V(N,q)-N(q-1)/2, including
complete-period bias through the exact period decomposition.

The next paper argument is dependency-closed. Bound gcd(q,2k) by 2 gcd(q,k),
use the root-of-unity chord bound, and pair k with q-k. This bounds the
centered prefix by (floor(N/q)+1) q^2 (2+log q) times
sum_{1<=k<=q} sqrt(gcd(q,k)/q)/k. Cauchy--Schwarz and the corpus theorem
sum_sum_gcd_div_le give the weighted row estimate

  sum_{q,k<=D} w(q) sqrt(gcd(q,k)/q)/k
    <= sqrt(sum_{q<=D} w(q)^2) (1+log D)^2.

For w=1, the bound is sqrt(D)(1+log D)^2. If D<=N, multiplying by
abs(mu(q)) log(q)/q and using (floor(N/q)+1)q<=2N gives

  abs(sum_{q<=D} mu(q) log(q)/q * (V(N,q)-N(q-1)/2))
    <= 4 N sqrt(D) (1+log D)^4.

The explicit mean is N/2 times sum_{q<=D} mu(q) log(q) (1-1/q).
It is not absorbed into the centered estimate. Formalization of the gcd
frequency conversion and weighted action is in progress. RH remains open.


## Verified small-modulus completion, 2026-10-09

Paper proof and Lean status: COMPLETE for the following exact statements; RH remains OPEN.

- `MobiusSquareResidueFourier.lean`: least-residue Fourier coefficients, exact centered Fourier identity, and full-period decomposition (9 public theorems).
- `SquareResidueGcdHarmonic.lean`: weighted gcd harmonic Cauchy bound and its unweighted specialization (2 public theorems).
- `MobiusSquareResidueGcdBound.lean`: reciprocal-chord pairing, gcd bounds, and actual centered logarithmic Mobius action estimate (8 public theorems).
- `MobiusSquareResidueSmallModuli.lean`: bound on explicit mean, full small-modulus action, exact large-modulus source, and corresponding RH criterion (5 public theorems).

Let V(N,d) be the sum of least residues s^2 mod d over 0 <= s < N, c(d)=mu(d) log(d)/d, and E(N,D)=sum_{1<=d<=D} c(d)(V(N,d)-N(d-1)/2). For D<=N, the verified estimates are

    |E(N,D)| <= 4 N sqrt(D) (1+log D)^4 <= 16384 N D.

The corpus theorem `exists_abs_sum_moebius_log_div_le` supplies a fixed S>=0 bounding every partial sum of c. Finite summation by parts then gives

    |N/2 * sum_{d<=N} mu(d) log(d)(1-1/d)| <= S N^2.

Consequently the actual full action A(N,N)=sum_{d<=N} c(d)V(N,d), including its explicit mean, satisfies |A(N,N)| <= (S+16384)N^2 unconditionally.

The remaining source is exactly

    L(N) = sum_{N<d<=N^2} c(d)V(N,d)
           - (1+sum_{d<=N^2} c(d)) sum_{s<N} s^2.

For N>=1, the actual square-sampled psi remainder is A(N,N)+L(N). The Lean theorem `riemannHypothesis_iff_mobiusLargeModulusSquareResidueSource_boundedAbove` proves

    RH iff exists B, forall N>=2, L(N) <= B N^2.

This last bound is NOT proved. The route is still active; no proof or falsification of RH is claimed. The next required advance is an estimate on joint large-modulus/counterterm cancellation, retaining the actual Mobius coefficients. Deep corpus search for that estimate returned partial results after its runtime deadline and no applicable closure theorem.

Verification: all four leaf modules directly compiled with exit 0. Source/object timestamps agree. A scratch-only `#print axioms` audit passed for all 24 new public theorems plus `exists_abs_sum_moebius_log_div_le`; only propext, Classical.choice, and Quot.sound occur. Changed files passed whitespace checks. Global formal lint remains failing solely on two unrelated unreachable modules: RHTower.PaperCirclePosteriorProjective and RHTower.PaperCircleSplitBitPosterior. No unrelated files were changed. All seven owned scratch Lean files were removed after their processes exited. Research reads used only Lean corpus search output; no Markdown reads or web searches.


Corpus follow-up: `ReducedFrequencyMobiusAliasCollapse` supplies exact complete-divisor Euler products and `quadraticCongruence_oddGapAliasPhysicalCutoffBalance`. The latter equates the retained cutoff part to the negative discarded part; it does not bound either part. Its root polynomial is r(r+h)=0. These statements neither include the required logarithmic coefficient nor directly estimate the current least-square-residue interval sum. A lexical search for `log` in that module returned zero hits. Therefore the complete-packet cancellation cannot currently discharge the large-modulus source inequality; no closure claim is made from it. All owned compilation and search sessions are terminal.


## All-cutoff centered estimate: paper target, 2026-10-09

The coarea diagonal bound found in the corpus does not bound the remaining signed interaction. The Gauss/gcd proof admits a direct extension: replace ((N/d)+1)d <= 2N by ((N/d)+1)d <= N+D for d<=D. This predicts the unconditional estimate

    |E(N,D)| <= 2(N+D)sqrt(D)(1+log D)^4

for all natural N,D. For every eps>0 and D>=1, log domination predicts

    |E(N,D)| <= 2(1+4/eps)^4 (N+D) D^(1/2+eps).

Thus if N<=D and D^(3/2+eps)<=N^2, the actual centered contribution up to D is bounded by 4(1+4/eps)^4 N^2. This reaches cutoffs below exponent 4/3, beyond the prior D<=N result. The explicit mean for d>N is retained and remains part of the unresolved source. These are dependency-closed paper derivations awaiting Lean verification; RH is not claimed.


## Verified superlinear centered cutoff, 2026-10-09

The preceding paper target is now formalized. `MobiusSquareResidueGcdBound.lean` adds three public theorems:

- `abs_logMobiusCenteredQuadraticResidueAction_le_all`: for every N,D, |E(N,D)| <= 2(N+D)sqrt(D)(1+log D)^4.
- `abs_logMobiusCenteredQuadraticResidueAction_le_rpow`: for eps>0 and D>=1, |E(N,D)| <= 2(1+4/eps)^4(N+D)D^(1/2+eps).
- `abs_logMobiusCenteredQuadraticResidueAction_le_superlinear_aperture`: if also N<=D and D^(3/2+eps)<=N^2, then |E(N,D)| <= 4(1+4/eps)^4 N^2.

The original small-cutoff theorem is preserved as a corollary of the all-cutoff estimate; its statement and earlier constants remain unchanged. This controls the actual centered source at cutoff exponents approaching 4/3 from below, rather than only D<=N. It does not bound the full explicit mean for D>N.

`MobiusSquareResidueSmallModuli.lean` now defines R(N,D)=A(N,N^2)-A(N,D)+mean(N,D)-counterterm(N), named `mobiusCenteredCutoffSquareResidueSource`, and adds three public theorems:

- `mobiusCenteredCutoffSquareResidueSource_eq_sum_Ioc`: when D<=N^2, R(N,D) is exactly the residue sum over D<d<=N^2, plus the mean up to D, minus the original scalar counterterm.
- `psiRemainder_squareSum_eq_centered_add_cutoffSource`: for N>=1, the actual square-sampled psi remainder equals E(N,D)+R(N,D), for every D.
- `riemannHypothesis_iff_mobiusCenteredCutoffSquareResidueSource_boundedAbove`: for any fixed eps>0 and cutoff family D(N) satisfying the displayed numerical aperture conditions for N>=2, RH is equivalent to a uniform one-sided quadratic upper bound on R(N,D(N)).

RH remains OPEN. The unresolved term is the joint tail, explicit mean, and scalar counterterm. No inequality controlling that joint term has been proved. The coarea diagonal search supplied no applicable control of its signed interaction; the deeper signed-bound search was partial after a retrieval deadline. These limitations do not retire the route.

Verification: both updated leaf modules compiled directly with exit 0 and no diagnostics; their compiled objects are newer than their source. A scratch-only axiom audit covered all 19 public theorems in the two affected modules, including all six new theorems and the retained prior endpoints. Every theorem uses only propext, Classical.choice, and Quot.sound (or a subset). Both source files passed whitespace checks. Global formal lint reported one unrelated unreachable module, GaloisForLFunctions.RHTower.PaperCirclePosteriorRating. No unrelated modules were changed. All five owned scratch files were removed after their processes exited. All research reads used Lean corpus search output only.


## Signed short bilinear reconstruction: paper target, 2026-10-09

Research reads found the exact short inverse identity in `LogarithmicMobiusShortReconstruction`: below (U+1)^2, mu = 2 mu_U - mu_U * mu_U * zeta. The related `CCMPrimeDeficitShortQuadraticWork` already gives a different absolute-value RH criterion for a logarithmic deficit; it supplies no unconditional bound for its signed quadratic form. This application retains the actual square-sampled source and its one-sided target.

Define F(N,d)=sum_{s<N} floor(s^2/d), Q(N)=sum_{s<N}s^2, and C(N)=sum_{d<=N}mu(d)log(d)/d. Exact residue division gives sum_{d<=D}mu(d)log(d)F(N,d)=C(D)Q(N)-A(N,D). Applying the short inverse identity with U=N and terminal cutoff N^2 gives a bilinear correction

    B(N)=sum_{a,b<=N} mu(a)mu(b)
           sum_{k<=N^2/(ab)} log(abk) F(N,abk).

All Mobius coefficients in B lie at or below N, while every product cutoff and logarithmic weight is retained. The proposed exact identity is

    sum_{1<=s<N} psiRemainder(s^2)
      = [B(N)-(1+2C(N))Q(N)] + 2A(N,N).

The previously verified bound on A(N,N) makes the difference uniformly O(N^2). Thus the remaining one-sided problem can be posed for the literal signed short bilinear form with its scalar counterterm. No bound on that bilinear form is assumed or claimed. Paper algebra complete; Lean formalization pending.


Bilinear-kernel audit, paper proof: write K(N,q)=sum_{k<=N^2/q} log(qk)F(N,qk). It is nonnegative. For N>=1 and q>=2, K(N,q)>0 exactly when q<=(N-1)^2. Above the largest sampled square, every floor quotient is zero. Below it, the k=1 term and s=N-1 sample provide a strictly positive term. In particular K(N,N^2)=0, while K(N,N)>0 for N>=3. Therefore the principal minor on coefficient indices 1,N is -K(N,N)^2<0. This rules out a positive-semidefinite-kernel shortcut; it does not retire the signed bilinear route.

Positive survivor: the exact support/positivity classification, together with the signed reconstruction, remains useful independently of that obstruction. The actual positive diagonal has the explicit lower bound (log 2)/32 * N^3 for N>=4: retain its a=1 term, then k=2, and use F(N,2)>=N^3/32. The latter follows from the exact square moment, Q(N)>=N^3/8, and V(N,2)<=N. These statements are being checked in Lean with the reconstruction; a one-sided quadratic ceiling for the full signed source remains unproved.

### Verified short bilinear reconstruction — 2026-10-09

Formalized 15 public theorems in `MobiusSquareResidueShortBilinear.lean`: exact signed reconstruction using Möbius coefficients through N, quadratic reconstruction error, equivalent one-sided RH criterion, sharp kernel support/positivity, cubic positive diagonal, and negative terminal principal minor for every N >= 3. Direct leaf compilation passed. All 15 statements and both reconstruction inputs passed axiom audit with only propext, Classical.choice, Quot.sound. Global formal lint and scoped whitespace checks passed. Corpus refresh found the new declarations; retrieval reported partial and compiler metadata source_only, so compilation evidence comes from direct Lean invocation. Three owned scratch files deleted after terminal processes. RH remains unresolved: the full signed source needs a uniform one-sided quadratic bound. Literal kernel PSD shortcut fails; exact support classification and cubic diagonal are its formalized positive survivors.

### Terminal Möbius row cancellation: paper derivation

For N >= 1 and w(n)=log(N*n) F(N,N*n), weighted divisor inversion gives sum_{b<=N} mu(b) sum_{k<=N/b} w(b*k)=w(1). Since N^2/(N*b)=N/b, the literal short bilinear kernel satisfies sum_{b<=N} mu(b) K(N,N*b)=log(N) F(N,N). Subtracting the harmonic main term Q(N) log(N)/N and using V(N,N)+N F(N,N)=Q(N) gives exactly -log(N) V(N,N)/N. The elementary residue bound V(N,N)<=N^2 gives absolute residual <=N log(N)<=N^2. This is an unconditional critical-scale cancellation along the actual Möbius vector despite the negative terminal principal minor. It concerns the terminal row, not the full source, and is now being formalized.

### Terminal row: verified Lean checkpoint — 2026-10-09

Added `formal/GaloisForLFunctions/RHTower/MobiusSquareBilinearTerminalRow.lean` and its RHTower umbrella import. Five public theorems prove exact terminal Möbius row inversion, the centered row identity, nonpositivity, the absolute N log(N) bound, and the N^2 corollary. Scratch compilation and direct final leaf compilation passed; the compiled object is at least as new as source. All five public statements passed the complete axiom/API audit with only propext, Classical.choice, Quot.sound. Owned scratch files were removed after process exit. Scoped umbrella whitespace check passed; new-file whitespace check emitted no diagnostics. Corpus refresh indexed the new module but reported partial retrieval.

Global formal lint was rerun after the shared umbrella changed. It currently fails on three modules outside this change: `GaloisForLFunctions.RHTower.ChronologicalBoundedRowMobiusRigidity`, `GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Snapshot.Near`, and `GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Snapshot.Representative`, each unreachable from its theorem-area umbrella. Those files were not modified. The earlier short-bilinear checkpoint had passed global lint; repository state has since changed.

RH remains open and the goal remains active. The terminal row is now controlled at subquadratic scale before multiplication by its Möbius coefficient. This does not control the interior rows or the full signed source, and does not promote the literal indefinite kernel to a semidefinite one. The next analytic obstacle remains a uniform one-sided quadratic bound on `mobiusShortBilinearSquareSource`.

### Shortening both bilinear factors: paper derivation

Write mu=M+R with M=mu restricted to coefficients <=U. Since mu*zeta=1, the exact identity is mu=2M-M*M*zeta+R*R*zeta. Thus the previous square-sampled reconstruction at coefficient cutoff N extends to arbitrary U with one additional signed high-high rectangle. For U=N-H, 4H<=N, N>=2, every nonzero high-high term has a,b>U, ab<=N^2, k=1, and floor prefix F(N,ab)<=H. Both factors are <=U+3H because N^2<=(U+1)(U+3H). There are at most 9H^2 ordered pairs, each bounded by 2H log(N), hence absolute correction <=18H^3 log(N). The small-modulus action also admits a uniform bound for every U<=N: the existing harmonic partial-sum bound controls its mean by S*N*U, and the existing centered bound controls the remainder by 16384*N*U. Consequently whenever H^3 log(N)<=K N^2, shrinking both factors from N to N-H changes the reconstructed source by a critical O(N^2) error. This does not bound the remaining shorter signed rectangle. Prior corpus searches found truncated inverse identities and unconditional VK-rate sums, but no bound closing that interior rectangle; the deep query was partial because its local judging stage returned malformed JSON. Formalization pending.

### Verified growing boundary region — 2026-10-09

Added `formal/GaloisForLFunctions/RHTower/MobiusSquareBilinearCutoff.lean` and its umbrella import. Ten public theorems now prove: (1) exact arbitrary-cutoff reconstruction with a high-high tail rectangle; (2) its exact relation to the square-sampled Chebyshev remainder; (3) the boundary floor-prefix bound; (4) the boundary kernel bound; (5) the general finite-rectangle estimate; (6) the explicit bound |Tail(N,N-H)|<=18 H^3 log(N) for N>=2 and 4H<=N; (7) agreement with the previous source at U=N; (8) a uniform bound |A(N,U)|<=C N U for every U<=N; (9) |S(N)-T(N,U)|<=C N U+18 H^3 log(N) when N=U+H; and (10) the one-sided RH criterion for every cutoff family H with 4H(N)<=N and H(N)^3 log(N)<=K N^2. These numeric restrictions control a growing boundary region. They do not bound the remaining interior signed rectangle.

Verification: complete scratch compilation passed, direct final leaf compilation passed, all ten public theorems passed axiom audit using only propext, Classical.choice, Quot.sound, and API checks passed. Final object timestamp is at least the source timestamp. Global formal lint passed at this checkpoint, superseding the previous unrelated reachability failures. Scoped umbrella and new-file whitespace checks passed. Corpus refresh indexed the key declarations and returned the precise criterion and source-error statements; retrieval remained partial and compiler metadata source_only, so proof verification is the direct Lean result. Four owned scratch/fragment files were removed after all owned processes exited.

RH remains unresolved; keep the goal active. Next obstacle is an unconditional one-sided quadratic upper bound on the retained shortened source, requiring control of its signed interior contribution.

### Counterterm sign audit: paper derivation

Corpus premise audit: the retrieved Ramaré mean-square result transfers the estimate to an unresolved bilinear norm, and twist/window results retain explicit twist bounds. The classical divisor summatory estimate gives square-root error pointwise, but taking absolute values after the bilinear expansion is too large for the current N^2 target. No interior bound has been obtained from these hits; several deep searches were partial.

The natural sign shortcut must be tested on the actual counterterm-subtracted matrix. Let Q=sum_{s<N}s^2 and define Ktilde(a,b)=K(ab)-Q*(delta(a,1)*delta(b,1)+delta(a,1)*log(b)/b+delta(b,1)*log(a)/a). Its quadratic value at the actual Möbius vector equals the current short source exactly, since mu(1)=1. On indices 2,N with N>=4, every counterterm vanishes, Ktilde(N,N)=0 and Ktilde(2,N)>0, so the determinant is -K(2N)^2<0. The normalized one-coordinate direction e_2 remains positive; retaining k=1 and using V(N,4)+4F(N,4)=Q gives K(4)>=(log 2)/32*N^3 for N>=8. Thus generic semidefiniteness or a uniform quadratic upper bound for arbitrary bounded coefficients cannot prove the actual source bound after this subtraction. This does not refute a bound for the Möbius vector. Positive survivor to formalize: exact two-coordinate indefinite form, explicit negative witness, and cubic positive direction.

## Counterterm sign audit: verified closure, 2026-10-09

The exact renormalized matrix and 12 public statements are formalized in formal/GaloisForLFunctions/RHTower/MobiusSquareRenormalizedKernel.lean. Scratch and final leaf compilation passed; all 12 separate axiom checks returned only propext, Classical.choice, Quot.sound. API checks and scoped whitespace checks passed; generated objects are fresh; corpus search indexes the module; both owned scratch files were deleted.

Sharp survivor: the (2,N) principal minor is negative iff N>=4 (for N>=2); the two-coordinate form is nonnegative for every real pair iff N<=3; an explicit negative direction attains -1; R_N(2,2)>0 for N>=3 and R_N(2,2)>=(log 2)/32*N^3 for N>=8. This retires only the generic sign/size shortcut after a first-row/column correction. It leaves the actual Möbius-vector bound and RH unresolved. The failed-shortcut card records the dependency-closed paper proof and exact scope: docs/drafts/pipeline/5-failed/mobius-square-counterterm-semidefinite-2026-10-09.md.

Global formal lint failed on unrelated unreachable module GaloisForLFunctions.HTGeometry.DiscreteCrossedProductCStar. No unrelated files changed. Keep the RH goal active; the remaining task is arithmetic cancellation for the actual signed vector, not a generic matrix-sign argument.

## Unequal-cutoff cancellation audit: paper target, 2026-10-09

Prior search: exact Selberg logarithmic lcm quadratic asymptotics and minimum-log layer-cake identities were retrieved from Lean corpus. Their kernels differ from the product kernel in the live RH source; no applicable comparison was established. Do not infer a closing bound from those results.

Next target: preserve actual Möbius coefficients while replacing the equal cutoff by U,V. For a weight w supported on [1,X], define B(U,V)=sum_{a<=U,b<=V} mu(a)mu(b) sum_{k<=X/(ab)} w(abk). Full Möbius inversion gives B(U,X)=sum_{a<=U} mu(a)w(a), B(X,V)=sum_{b<=V} mu(b)w(b), and B(X,X)=sum_{n<=X} mu(n)w(n). Partitioning both full ranges proves the exact mixed-cutoff identity with a both-large tail. That tail vanishes when X < (U+1)(V+1).

Specialize X=N^2, w(d)=log(d)F(N,d). The square Chebyshev remainder should then be a rectangular signed bilinear source plus the two residue actions A(N,U), A(N,V). Keep every mean term when centering residues; no claim that an enlarged cutoff automatically retains the O(N^2) error. The purpose is to expose shorter-factor arithmetic estimates, not to assert the RH bound. Paper algebra is derived; Lean implementation and applicability audit pending.

## Unequal-cutoff cancellation: formalized, 2026-10-09

Module: formal/GaloisForLFunctions/RHTower/MobiusSquareRectangularBilinear.lean. Nine public theorems, imported by RHTower.lean. RH remains unresolved and the full goal remains active.

### Exact paper result

Let mu denote the Möbius arithmetic function, Z the constant-one Dirichlet function, M and L its truncations at U and V. From mu*Z=1, commutative ring algebra gives

mu = M + L - M*L*Z + (mu-M)*(mu-L)*Z.

Apply an arbitrary finite weighted sum through X. Expanding the convolution gives the exact rectangular identity with the both-large tail. If X < (U+1)(V+1), every product in the tail exceeds X, so its k-range is empty. This proves the weighted asymmetric identity without any cancellation hypothesis.

Specialize X=N^2 and w(d)=log(d)F(N,d). Write Q(N)=sum_{s<N} s^2, C(D)=sum_{d<=D} mu(d)log(d)/d, and

B(N,U,V)=sum_{a<=U,b<=V} mu(a)mu(b)K(N,ab),
M(N,D)=N/2 * sum_{d<=D} mu(d)log(d)(1-1/d).

The new source is

T(N,U,V)=B(N,U,V)-(1+C(U)+C(V))*Q(N)+M(N,U)+M(N,V).

For N>=1, U,V<=N^2 and N^2<(U+1)(V+1), the exact identity is

sum_{1<=s<N} psiRemainder(s^2) = T(N,U,V)+E(N,U)+E(N,V),

where E is the existing centered quadratic-residue action. Both residue means are retained; neither is discarded at a superlinear cutoff.

If D^4<=N^5, then |E(N,D)|<=4*41^4*N^2. For D<=N use the existing 16384*N*D bound. For D>N apply the existing superlinear-aperture theorem with epsilon=1/10: raise D^4<=N^5 to power 2/5 to obtain D^(8/5)<=N^2. Thus if U^4,V^4<=N^5, the absolute error between the sampled Chebyshev sum and T is at most 8*41^4*N^2. The existing one-sided square-sum RH criterion transfers exactly to T. The upper bound for T is not proved.

### Explicit cutoffs for every N>=2

Set t=Nat.sqrt(Nat.sqrt N), U=(N-1)/t+1, V=N*t. Nested square-root inequalities give 1<=t and t^4<=N. Ceiling division gives U<=N and N<=U*t, hence N^2<=U*V. Also V<=N^2, U^4<=N^5, and V^4=N^4*t^4<=N^5. This removes all auxiliary aperture hypotheses from the concrete RH equivalence. The cutoffs have the fourth-root imbalance: approximately N^(3/4) and N^(5/4).

### Verification and scope

Scratch compilation passed after explicit real-cast annotations. Final direct leaf compilation passed cleanly. Separate scratch audit checked all nine public statements, reporting only propext, Classical.choice, Quot.sound; the referenced real-power and natural-square-root APIs also checked. New .olean and .ilean timestamps are fresh, as are the three direct input modules checked. Scoped whitespace checks passed. Lean-only lexical research refresh indexed all nine statements, both definitions, and private helpers. All three owned scratch files were deleted.

Global scripts/formal_tools.py lint failed on unrelated unreachable module GaloisForLFunctions.RHTower.CCMRiemannKernelBartaLayerBounds. No unrelated module changed. The prior HTGeometry lint issue is no longer the reported blocker.

Prior-research searches inspected Lean declarations and source arguments only. Retrieved Selberg lcm logarithmic forms and minimum-log layer-cake formulas do not themselves establish a comparison to the product kernel. The searches supplied usable snapshots but do not establish corpus-wide novelty or absence of a closing theorem.

Next mathematical task: bound this exact signed rectangular source for the actual Möbius coefficients, using the shorter factor and retaining the longer-factor mean. Inspect applicable Type I/II and finite Dirichlet-packet estimates for this weight; do not replace the signed target by an unsigned matrix bound or assume a twist/mean-square hypothesis that is equivalent to the missing cancellation.

## Rectangular source: Type I/II applicability audit, 2026-10-09

Previous turn classified as progress: nine rectangular-cutoff theorems were integrated and verified. This turn inspected candidate estimates rather than adding another RH equivalence. All research reads used Lean-only output from scripts/formal_tools.py research. An initial slash-form module filter returned no candidates; it was corrected to Sieve. Subsequent relevant searches reported partial=false and no retrieval errors. This is scoped retrieval, not an exhaustive absence claim.

### Verified candidate statements

1. Sieve.norm_typeII_sq_le in TypeIIEnergyBound.lean is a Cauchy bound with a double correlation sum still on the right. Sieve.norm_sum_corr_le treats the specific ndExp/nearDiagonalPhase kernel, under positive T,r, distinct positive inner indices, the two geometric 4r/m bounds, and a curvedLambda bound. A representation of the present square-floor product kernel by this phase has not been established.
2. Sieve.exists_typeII_orientation_block_bound in TypeIIOrientationAssembly.lean gives two orientations for masked Vaughan coefficient blocks. Its geometric and curvature hypotheses remain mandatory. Shortening one factor alone does not establish them or transfer its estimate to the rectangular source.
3. Sieve.exists_norm_logPoly_moebiusCoeff_Icc_one_le in CofactorLowFreqBound.lean supplies a restricted-frequency sharp-prefix estimate. Its displayed envelope contains 3*M*exp(-c*(log M)^(1/10))/pi plus a smoothing term. The exponential saving itself is subpower: for any fixed positive eta, eta*log M-c*(log M)^(1/10) tends to infinity. No critical signed rectangular estimate was obtained from it.
4. Sieve.moebiusSharpBound_eq_mul and Sieve.tendsto_relMoebiusSharp in RelMoebiusSharp.lean certify the positive result moebiusSharpBound(M)=M*relMoebiusSharp(M), with relMoebiusSharp tending to zero. This provides sublinear control.
5. Sieve.exists_norm_LSeries_truncatedMoebius_dyadic_le_routeTPower in RouteTMoebiusPowerSaving.lean requires M^4<=U and routeTInverseBaseHeight+U<=|tau|, where M is the dyadic factor length. Sieve.routeTInverseBaseHeight_ge in RouteTZetaInverseBound.lean proves the base height is at least 100001. A separate Lean scratch proof established that these premises are inconsistent whenever |tau|<=M^4. Hence that theorem cannot directly fill the low-frequency gap. Its saving exponent also retains an explicit height-dependent contour shift; no uniform fixed exponent was inferred.

### Verification

The relevant five module objects checked were fresh relative to source timestamps. First scratch audit checked signatures and axioms for the four central Type II/low-frequency estimates. Second audit checked four additional Route-T/relative-envelope facts and proved the low-frequency premise exclusion. Both Lean runs exited 0; every audited declaration and the scratch exclusion theorem depended only on propext, Classical.choice, Quot.sound. The owned scratch file was deleted. No repository Lean source changed this turn; global lint was not rerun.

### Result and next proof target

The audit rules out a direct application of the retrieved large-frequency power theorem on the low-frequency range. It does not retire the rectangular route or prove an impossibility result for joint signed estimates. The one-sided upper bound for the actual Möbius source remains unproved; RH remains unresolved and the goal remains active.

Next investigate joint signed control of the bilinear term and its explicit counterterms. Estimating the two factors separately has not closed the bound. A candidate calculation already identified is the divisor-main-term expansion in harmonic logarithmic Möbius moments: at equal cutoffs, its rank-three contribution has the algebraic form A_N*L0^2+2*gamma*Q_N*L0*L1-Q_N*L0*L2-Q_N*(L1+1)^2. This remains a paper target: define and retain the exact divisor remainder, audit its signed contribution, and do not infer a bound by discarding it. Any implementation must pursue that missing signed estimate rather than treat another equivalent formulation as completion.


## 2026-10-09 — exact divisor kernel and first quotient sector

Research reading used only `.lean` results and Lean-view passages from `scripts/formal_tools.py research`. No web, Markdown, memory, or direct corpus-source reads. Several deep queries were partial (retrieval deadlines or local JSON failure); available hits were used without claiming corpus-wide absence. No applicable degree-two Voronoi formula was retrieved.

Integrated `formal/GaloisForLFunctions/RHTower/MobiusSquareDivisorKernel.lean` (237 lines; 9 public theorems, 6 definitions, 3 private helpers). Reused `sum_log_divisors_eq_half_card_mul_log` from `LogarithmicDivisorDilation` rather than retaining a duplicate pairing proof. Added the module to the RHTower umbrella.

Exact paper/Lean result: writing K for the existing square short bilinear kernel and tau(n) for divisor count,
K(N,q) = sum_{s<N} sum_{1<=n<=floor(s^2/q)} tau(n) (log q + log n/2), for every N,q, including zero and empty ranges.
Let D(X)=sum_{n<=X}tau(n), P(X)=X log X+(2 gamma-1)X, and delta(X)=D(X)-P(X). The exact discrete Abel action is
A(q,X;F)=(log q+log X/2)F(X)+(1/2)sum_{n<X}F(n)(log n-log(n+1)).
The kernel equals sum_s A(q,floor(s^2/q);P) plus sum_s A(q,floor(s^2/q);delta), without replacing integer floors, dropping lower endpoints, or taking absolute values. The classical bound |delta(X)|<=20 sqrt(X) is formalized also at X=0. The final source identity retains both actual Moebius factors and the original counterterm.

Exact boundary classification, also proved in Lean: if (N-1)^2 < 2q, every sampled quotient is zero or one. Then the remainder kernel equals (2-2 gamma)K(N,q), while the principal kernel equals (2 gamma-1)K(N,q). Thus the first nonzero divisor cell must stay in any proposed signed estimate; it is not removed by writing a classical main term. No route is retired and no RH-equivalence wrapper was added.

Verification: final scratch compilation and installed leaf compilation both exit 0. All nine new public theorems and the reused divisor pairing theorem have only [propext, Classical.choice, Quot.sound]. Installed source SHA256 cb12fb21bf88f2b30255b131d8748f4b42a7fd1b975f8b602090e3bd6b727c46 matches the audited copy; .olean and .ilean are newer than source. Whitespace checks pass. Corpus refresh reports all 18 module declarations. Global formal lint exits 1 with 367 large-file warnings and one unrelated unreachable, untracked module: GaloisForLFunctions.RHTower.PaperCirclePredictionChannelTransport. That module was not modified. Owned scratch files removed after verification.

RH remains unresolved. Neither the principal source nor the retained signed remainder has the required joint one-sided O(N^2) bound. Next: investigate exact quotient sectors or the square-sampled hyperbola/quadratic-residue mechanism while retaining the signed first-cell contribution. The retrieved `sum_div_add_sqrt_sq` in `SymmetricHyperbolaFloorCount.lean` is a possible exact input; its applicability to the signed remainder has not yet been verified. Do not replace the task by another criterion or an unsigned bound.


## 2026-10-09 — square-sampled hyperbola estimate in progress

Only Lean-corpus search results are being read. Paper mechanism: use the existing `routeP_centeredModularRamp_quotient` to write ramp_d(floor(s^2/q)) = ramp_(q*d)(s^2) - ramp_q(s^2)/d. The exact birth is sqrt(q*d*d-1)+1 and divisor cutoff D=sqrt((N-1)^2/q). Retain both moving channels. `squareResidue_weighted_gcd_harmonic_le` supports a sparse set of q*d moduli with square-root dependence on its cardinality, avoiding a dense-modulus replacement.

Target paper bound for q>0: |sum_{s<N} centeredDivisorHyperbola(floor(s^2/q))| <= 8*(N+q*D)*sqrt(D)*(1+log(q*D))^4. It follows from an interval bound, sparse GCD support bound, and H_D<=1+log D; it is not yet Lean-verified. Scratch `/tmp/hgt_square_residue_moving_intervals.lean` contains the interval and sparse-support proofs; its first compile found only an extra `ring` after `field_simp` had already closed a goal. That extra tactic has been removed. No new repository Lean module yet. This is a quantitative input toward the actual signed remainder, not an RH proof or a replacement objective.


Hyperbola estimate update: `SquareSampledDivisorHyperbola.lean` now contains 382 lines and 8 public theorems. Scratch compilation and all eight axiom audits pass with only [propext, Classical.choice, Quot.sound]. Source SHA256 4737bd39cd4af32832d5916dc97271153f26b6261532d2996b8ae236a618431e. Umbrella import added; installed leaf compilation is running on session 93013. `/tmp/hgt_square_sampled_divisor_remainder.lean` is written but not yet compiled; it transfers the hyperbola bound to the actual delta from MobiusSquareDivisorKernel using |delta(X)+2C(X)|<=7+2log(X+1). Owned scratch files currently: /tmp/hgt_square_hyperbola_api.lean, /tmp/hgt_square_residue_moving_intervals.lean, /tmp/hgt_square_sampled_divisor_remainder.lean. The guessed API `Nat.gcd_mul_dvd_mul_gcd` does not exist and is not used. The sparse support method needs no such lemma. RH and the signed double-Moebius remainder remain unresolved.


## 2026-10-09 — square-sampled divisor cancellation verified and integrated

The previous in-progress estimate is now fully proved in Lean. Added `formal/GaloisForLFunctions/RHTower/SquareSampledDivisorHyperbola.lean` (382 lines, 8 public theorems) and `formal/GaloisForLFunctions/RHTower/SquareSampledDivisorRemainder.lean` (123 lines, 2 public theorems), with both umbrella imports. Only Lean-corpus search results and Lean-view passages were used for research reading; no Markdown, web, memory, or direct corpus-source reads. Partial searches were used with their reported limitations.

Let C(X)=centeredDivisorHyperbola X, delta(X)=mobiusSquareDivisorRemainder X, D=sqrt((N-1)^2/q) with natural division and square root, and R=q*D. For every N and every q>0, the exact moving-channel identity retains the birth sqrt(q*d*d-1)+1 and both ramps:
C(floor(s^2/q)) = sum_{d active} [ramp_(q*d)(s^2)-ramp_q(s^2)/d].
The sparse modulus set {q*d:1<=d<=D} is bounded using `squareResidue_weighted_gcd_harmonic_le`; its square-root cost is sqrt(D), not sqrt(q*D). The harmonic correction at modulus q is retained and bounded. This proves
|sum_{s<N} C(floor(s^2/q))| <= 8*(N+R)*sqrt(D)*(1+log R)^4.

The pointwise smooth comparison is also proved:
|delta(X)+2*C(X)| <= 7+2*log(X+1), for every X, including zero.
It uses the existing divisor-count identity, Stirling upper/lower bounds, and `abs_divisorHyperbolaSmoothRemainder_le`, with the logarithmic increment bounded explicitly. Therefore the actual divisor remainder satisfies the uniform finite estimate
|sum_{s<N} delta(floor(s^2/q))| <= N*(7+2*log(N^2+1)) + 16*(N+R)*sqrt(D)*(1+log R)^4.
These are quantitative cancellation estimates, not a new RH equivalence. All floors, empty ranges, zero cutoffs, and moving boundaries are covered by the proved statements.

Verification: both final scratch compilations and both installed leaf compilations exit 0. All 10 public theorem axiom audits return only [propext, Classical.choice, Quot.sound]. Source hashes match the audited copies: Hyperbola 4737bd39cd4af32832d5916dc97271153f26b6261532d2996b8ae236a618431e; Remainder 34ab20abd9991a7b63c42b05eb5cc596b79240e98ba261317514c58e23e3ef84. Both .olean/.ilean pairs are newer than source. Whitespace checks pass; corpus refresh finds all 15 declarations across the two modules. Global formal lint exits 1 with 367 existing large-file warnings and the unrelated unreachable untracked module GaloisForLFunctions.RHTower.PaperMaassFourierReconstruction. That module was not modified. All three owned scratch files are deleted; no owned Lean or search process remains live.

RH remains unresolved. The next missing transfer is logarithmic Abel weighting of delta inside `mobiusSquareDivisorRemainderKernel`: use the new uniform square-prefix estimate for its boundary term, and ordinary delta-prefix control for its internal logarithmic-difference sum. `sum_centeredDivisorHyperbola_bounds` from DivisorHyperbolaPositivePrefix supplies the ordinary centered-prefix estimate needed for the latter. Then assess the actual double-Moebius sum jointly with the principal counterterm; the fixed-dilation result alone does not bound that full signed source by O(N^2). The exact first-cell remainder identity from MobiusSquareDivisorKernel remains mandatory. A low-product estimate is a possible intermediate consequence, not completion of the RH objective.


## Logarithmic divisor-remainder transfer — continued 2026-10-09

RH remains unresolved. Current work: derive finite Abel comparison estimates, apply ordinary divisor-error prefix cancellation to the logarithmic-difference term, and transfer square-sampled prefix cancellation to the logarithmic boundary term. All research reads restricted to Lean-corpus search output. No direct source or Markdown reads. Proposed kernel estimate retains both terms; no claim yet about joint signed double-Möbius cancellation.


### Verified logarithmic remainder transfer

Added `DivisorRemainderLogAbelBound.lean` (172 lines) and `SquareSampledDivisorLogKernel.lean` (190 lines), plus their RHTower umbrella imports. Eight public theorems, one public definition. Both installed leaf compiles exit 0; all eight scratch axiom audits report only `propext`, `Classical.choice`, `Quot.sound`. No raised heartbeat limits or umbrella build. Both object/interface pairs are newer than source. Whitespace checks pass. Corpus refresh returns all nine public declarations.

Let delta(X) = mobiusSquareDivisorRemainder X, D = squareSampledHyperbolaCutoff N q, L = log(N^2+1), and F(N,q) = N*(7+2L) + 16*(N+qD)*sqrt(D)*(1+log(qD))^4. Proved:
- Ordinary signed prefix: |sum_(1<=n<=X) delta(n)| <= X*(8+2log(X+1)).
- Inner Abel term: |sum_(n<X) delta(n)*(log n-log(n+1))| <= (8+2log X)*log X, including X=0 and X=1 under Lean's log-zero convention.
- F(N,q) is nonnegative and monotone in N, including empty cutoffs.
- Weighted square boundary: |sum_(s<N) (log q+log(floor(s^2/q))/2)*delta(floor(s^2/q))| <= 2*F(N,q)*(log q+L/2) for q>0.
- Full kernel: |mobiusSquareDivisorRemainderKernel N q| <= 2*F(N,q)*(log q+L/2) + (N/2)*(8+2L)*L for q>0. Both Abel terms retained.

Proof mechanisms: finite Abel comparison for nonnegative decreasing weights under a linear signed-prefix bound; finite Abel bound for increasing weights under a uniform signed-prefix bound; previous square-sampled divisor cancellation. No claim of cancellation across the actual double-Mobius sum.

Final source hashes:
- DivisorRemainderLogAbelBound: 08195a915d18b206636cb16e324aee4d5c85fdafada31956c39255ddeb5fcdd9
- SquareSampledDivisorLogKernel: 1921be9caf71a031a96c8034d1c38bac3c474c3bf59a390ef0a4f5b6218f09dd

Global lint exit 1, 367 large-file warnings, four unrelated unreachable modules: RHTower.LeeYangSplitCountDifference, RHTower.PaperSuzukiCayleyReconstruction, RHTower.PaperSuzukiCayleySynthesis, HilbertMetric.HorizontalLamzouriSpectral. Did not modify those modules. Previous PaperMaassFourierReconstruction error is absent from this run.

Next mathematical target: use the explicit kernel estimate inside the actual product-cutoff double-Mobius sum, keeping the principal kernel and original counterterm. A possible low-product bound is not the RH target: the joint signed bulk estimate remains open. RH goal remains active and unresolved.


## Product-cutoff remainder transfer — continued 2026-10-09

Target: insert the verified logarithmic kernel estimate into the actual double-Mobius remainder. Derive the sharp fourth-root dependence on a product cutoff Q; count positive pairs ab<=Q by Q*(1+log Q); prove an explicit estimate for the actual restricted sum and its exact split from the full source. The complementary signed bulk and the principal counterterm remain part of the RH objective. No claim that low-product control proves RH. Research reads remain restricted to Lean-corpus search output.


### Verified actual low-product control and critical cutoff budget

Added `MobiusSquareDivisorLowProduct.lean` (251 lines) and `MobiusSquareDivisorProductBudget.lean` (161 lines), with RHTower umbrella imports. Ten public theorems and three definitions. Both scratch proofs and both installed leaf compiles exit 0. All ten public axiom audits use only `propext`, `Classical.choice`, `Quot.sound`. Objects and interfaces newer than source; scoped whitespace checks pass. Refreshed corpus returns all thirteen public declarations.

Definitions: low(N,Q) is the actual sum over 1<=a,b<=N, ab<=Q of mu(a)*mu(b)*mobiusSquareDivisorRemainderKernel(N,ab); high(N,Q) is its complementary ab>Q sum. Product envelope E(N,Q) is the explicit uniform kernel bound, with L=log(N^2+1), H=1+log(1+N*sqrt Q):
E = 2*(N*(7+2L)+32*N*sqrt N*sqrt(sqrt Q)*H^4)*(log Q+L/2) + (N/2)*(8+2L)*L.

Verified mathematical advances:
- Cutoff D=squareSampledHyperbolaCutoff(N,q) satisfies qD<=N*sqrt q and (N+qD)*sqrt D<=2*N*sqrt N*sqrt(sqrt q) for q>0.
- |kernel(N,q)|<=E(N,Q) for 0<q<=Q.
- Positive pair count in any N-square with ab<=Q is <=Q*(1+log Q), including zero endpoints.
- |low(N,Q)|<=Q*(1+log Q)*E(N,Q), using the actual Mobius coefficients.
- For 1<=Q<=N, E(N,Q)<=2104*N*sqrt N*sqrt(sqrt Q)*(1+log N)^5.
- Therefore |low(N,Q)|<=2104*N*sqrt N*Q*sqrt(sqrt Q)*(1+log N)^6.
- Under 1<=Q<=N and Q^5*(1+log N)^24<=N^2, |low(N,Q)|<=2104*N^2. This closes the low-product component on that explicit region.
- Exact source identity: original short bilinear source = (double-Mobius principal kernel minus original counterterm) + low(N,Q) + high(N,Q). No high-product term or counterterm was dropped.

Source hashes:
- MobiusSquareDivisorLowProduct: 5d98923499c712ed6dab1cb3e752f10064a6245c1c21447253398ab82e7f3658
- MobiusSquareDivisorProductBudget: 9bd0236be047df96a4dc42f612dc1314400e7dd975af2a6f8b7d8076fc2205e3

Final global lint exit 1: 367 large-file warnings; sole error is unrelated unreachable RHTower.WeilLogShiftGenericMomentDivergence. Earlier four unreachable modules no longer appear. Did not modify unrelated modules. Scratch files cleaned up; no owned processes remain.

RH is still unresolved. Next work must retain the full principal-plus-high-product signed expression. One optional immediate corollary, not yet formalised, is a uniform quadratic low-product bound under Q^3<=N: use log growth with exponent 1/72 and expect constant 2104*73^6. Corpus search found Real.log_le_rpow_div, Real.one_le_rpow, Real.rpow_mul and Real.rpow_natCast; verify signatures in scratch before use. Existing squareResidue_log_fourth_le_rpow is private and cannot be called. The growing-cutoff corollary is not the RH objective; the signed bulk bound remains open.


## Joint outer-corner cancellation — continued 2026-10-09

Previous turn is verified progress. RH remains unresolved. Current target: the actual full bilinear kernel in the one-quotient outer corner, retaining principal and divisor remainder together. Paper candidate: when (N-1)^2<2ab and a,b<=N, K(N,ab)=log(ab)*(N-ceil(sqrt(ab))). Replacing ceil(sqrt(ab)) by sqrt(a)*sqrt(b) separates the signed tail into four one-dimensional Mobius moments; keep the exact rounding residual and prove its quadratic-in-width envelope. Audit corpus for existing results before formalising. No claim that the four signed moments satisfy the remaining RH bound. All research reads remain Lean-corpus search output only.


### Verified one-quotient corner and full-source insertion

Added `MobiusSquareCornerMoments.lean` (210 lines) and `MobiusSquareCornerSource.lean` (95 lines), plus RHTower umbrella imports. Ten public theorems, six definitions. Both scratch and installed leaf compiles exit 0 without warnings. All ten axiom audits report only `propext`, `Classical.choice`, `Quot.sound`. Final source hashes match audited copies; object/interface files newer than source. Whitespace checks pass; corpus refresh returns all sixteen public declarations.

Let b(q)=squareSampledHyperbolaBirth(q,1)=Nat.sqrt(q-1)+1 and eta(q)=b(q)-sqrt(q). Proved 0<=eta(q)<=1 for q>0. If (N-1)^2<2q, then the full bilinear kernel K(N,q)=log(q)*(N-b(q)), with natural truncated subtraction. If additionally q<=N^2, then K(N,q)=log(q)*(N-sqrt(q))-log(q)*eta(q).

For the actual box U<a,b<=N, define the four signed moments M0=sum mu(a), L0=sum mu(a)*log(a), Mh=sum mu(a)*sqrt(a), Lh=sum mu(a)*sqrt(a)*log(a). Define continuous corner C=2*(N*M0*L0-Mh*Lh), and exact signed rounding E=sum_(a,b) mu(a)*mu(b)*log(ab)*eta(ab). Under (N-1)^2<2*(U+1)^2:
- Actual full-kernel corner = C-E.
- The principal-kernel corner plus divisor-remainder corner equals C-E as well; both terms retained.
- |E|<=2*(N-U)^2*log(N), for every N,U (the interval is empty when U>=N).

Full-source insertion for U<=N retains all mixed rows and the original counterterm. Cross(N,U)=sum_(1<=a<=U, U<b<=N) mu(a)*mu(b)*K(N,ab). CenteredCross=Cross-(sum_(U<d<=N) mu(d)*log(d)/d)*(sum_(s<N) s^2). Proved:
source(N)=cutoffSource(N,U)+2*CenteredCross(N,U)+C-E,
and therefore the absolute error on replacing the source by cutoffSource+2*CenteredCross+C is <=2*(N-U)^2*log(N) in the one-quotient corner regime.

Scope: this corner uses U<a,b<=N. It is NOT the entire previously defined logMobiusTailBilinearSquareAction, whose indices extend to N^2. No claim that the four moments, mixed rows, or inner source separately satisfy the RH bound. Replacing their signed contributions by trivial absolute bounds would recover the cubic obstruction.

Final hashes:
- MobiusSquareCornerMoments: a8e139ab65dfce4d433645400f46408aba5325cac55a332378c57091f082e82f
- MobiusSquareCornerSource: 95cb7579682147ccccab275091e925e84e89817a5bbda2704ce2db750304da4b

Global lint exit 1: 367 large-file warnings and three unrelated unreachable modules: RHTower.WeilLogShiftBoundedCubeGenericity, HTGeometry.BandKernelOperators, HTGeometry.PaperStableCoordinate.ExponentialShift. Did not alter those modules. Prior WeilLogShiftGenericMomentDivergence error absent from this run.

RH remains unresolved and the goal stays active. Next target is a joint one-sided estimate for the inner source, centered mixed rows, and four-moment corner, retaining their cancellations. All research reads used only Lean-corpus search output; no Markdown or direct corpus-source reads. Scratch files cleaned after verification; no owned processes remain.
