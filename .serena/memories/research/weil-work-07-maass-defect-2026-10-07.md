# WP07 actual interior Maass packet checkpoint (2026-10-07)

Goal remains ACTIVE and unbounded: solve exact denominator-three rigidity in docs/reports/weil-work/07-higher-denominator-rigidity.md. Do not complete/pause goal for this checkpoint. Previous cycle PROGRESS; no scientific novelty or full WP07 claim. Follow hgtl7 every turn. No subagents authorized.

## Exact target / conjecture
Full-positive real lambda, abs Dirichlet convergence, third-integral canonical mass on every bounded interval => lambda(n)=vonMangoldt(n), n>=2. Correspondence gives g1=1, absconv Lg on Re>1, entire finite-order E=(s(s-1)GammaR)^3 Lg, FE +/- and E1 nonzero, all E zeros critical, derivative Lg=-3 Llambda Lg. No Euler product, multiplicativity, coefficient signs, RH, simplicity or additional producer premise.

C1: every nontrivial complete cubic datum has infinitely many deficits BELOW ONE COPY xi: ord(E)<ord(xi). Finite deficit support is competing conjecture. Stronger positive-linear deficit-count growth remains open. Do not silently weaken to threshold 2 or 3 copies, or G/zeta². First OPEN CORE now spatial Poisson transport in finite-deficit branch, not endpoint algebra. After interior poles vanish reuse Multiplicity's divisor-containment theorem; do not rebuild a degree-two classification.

## Current owned files / workflow
Card docs/drafts/pipeline/1-in-progress/weil-work-07-denominator-three.md has current checkpoint and next entry.
Results docs/reports/weil-work/results/07-denominator-three/{RESULT,PROOF,EVIDENCE}.md updated.
Owned code formal/GaloisForLFunctions/RHTower/WeilWorkHigherDenominator*.lean; unrelated concurrent files untouched. Five new imports at RHTower.lean around7097-7101, but recheck anchor before edits because concurrent changes occur.
Session docs/architecture.md and docs/testing.md absent.
Serena manual read; Lean symbol operations unsupported. list_memories(topic) returns empty; explicit read/write works. update_plan unavailable; card records plan.
Use rg --files BEFORE choosing filenames; do not infer filename from namespace. Actual axis file MaassAxisUniqueContinuation.lean, namespace MaassAxisContinuation. A wrong filename guess was corrected this cycle.
No active owned build/search process; all scratch files cleaned. Existing .olean artifacts retained for imports.

## Five new modules, all final direct Lean checks passed
Namespace RHTower.WeilHigherDenominator.

1. ResiduePolynomial (146 lines):
residueLogPolynomial F rho k=sum j<k monomial j ((-1)^j laurentCoeff F rho (-1-j)/j!).
Public coeff_residueLogPolynomial; residueLogPolynomial_eq_zero_iff;
laurentCoeff_mellin_weight_eq_polynomial (analytic clearing shift, k>=1, x>0);
residueLogPolynomial_eq_zero_iff_order_nonneg;
exists_mellin_residue_polynomial (MeromorphicAt).
All pole orders. Q=0 iff nonnegative meromorphic order, i.e. removable PUNCTURED GERM, not necessarily pointwise analytic with arbitrary assigned pole value.
Private normalized Taylor product and exponential coefficient proofs. Existing Laurent/principal-part machinery reused.

2. InteriorPoles (145 lines):
xi_zero_re_mem_Ioo;
deficitPolynomial_root_xi_zero;
deficitPolynomial_root_re_mem_Ioo;
deficitPolynomial_root_deficit_pos;
poleClearedNumerator_ne_zero_at_root;
poleClearedDegreeTwoCompletion_order_at_root = -(xiDeficit E rho);
poleClearedDegreeTwoCompletion_order_neg_at_root.
Every P root is xi zero, 0<Re rho<1; exact P E=H xi + exact orders + E1,H1 nonzero imply H(rho) nonzero. No RH/simple-zero premise.

3. LogPolynomialDefect (63 lines):
exists_poleCleared_residue_polynomials supplies Q for all rho,x>0 and Q0 iff order>=0.
degreeThree_infiniteDeficits_or_logPolynomialDefect: hD:ZetaPowerDatum3 g E, E1ne => infinite deficit support OR P,H,epsilon,Q normal form, FE retained as conclusion, all interior Q nonzero in strictstrip, actual theta identity with endpoints still included.

4. EndpointResidues (158 lines):
residueLogPolynomial_doublePole hB:
Q_{B(s)/(s-p)^2,p,3}=C(deriv B p)-C(Bp)*X.
laurentCoeff_mellin_doublePole: x^-p (B'(p)-B(p)logx).
degreeTwoEndpointNumerator E s=E s/(2*xi s*s²).
degreeTwoEndpointNumerator_analyticAt_one hE.
poleClearedDegreeTwoCompletion_germ: near a nonzero xi value, actual F=E/(2 xi s²(s-1)²). Neighborhood equality preserves assigned values here.
poleClearedDegreeTwoCompletion_residue_one:
x^-1 (b-a logx).
poleClearedDegreeTwoCompletion_residue_zero:
-epsilon(b+a logx), with FE original.
a=degreeTwoEndpointNumerator E 1; b=deriv degreeTwoEndpointNumerator E 1.
Double-pole clearing uses exponent THREE: t³ B(p+t)/t²=t B(p+t), including t0; exponent2 would mishandle value at0.
At zero the analytic numerator is epsilon*B1(1-s). Apply FE at1-s to obtain E(s)=epsilon E(1-s); no extra epsilon-square premise for residue formula.

5. MaassDefect (146 lines):
degreeTwoQuotient_maass_axis_defect derives actual U axis packet from normal form and supplied Q representation (which previous existence theorem pays).
degreeThree_infiniteDeficits_or_maassDefect:
hD:WeilZetaPower.ZetaPowerDatum3 g E, hE1:E1ne =>
Infinite deficits OR exists P,H,epsilon,Q, Pmonic,normepsilon1,FE,exactPorders,diffH,finiteH,H1ne, P E=Hxi,
all roots rho: 0<Re rho<1 AND Qrho ne0,
all x>0:
U(ix)-epsilon U(i/x)=sum rho in P.roots.toFinset x^(1/2-rho)Qrho(logx).
U=RHTower.MaassBesselSeries.maassFun (degreeTwoQuotientCoeff g) (epsilon*a) (epsilon*b).
IMPORTANT actual namespace MaassBesselSeries, definition in MaassBesselFunction.lean; maassFun=4*cosSeries+constTerm. There is NO factor1/4 in final packet.
Private sign_mul_self derives epsilon²1 from FE and E1ne. Private sum_degreeTwoPoleSet splits roots from0,1. Private maass_axis_of_theta_packet cancels endpoint algebra.
At final field_simp, correct linear_combination multiplier is (a*logx-b)*hε2, without extra sqrt(x). First-pass wrong multiplier was corrected; final passes.

## Validation
Each new module final command from formal/:
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/NAME.olean GaloisForLFunctions/RHTower/NAME.lean
Exit0 no diagnostics. One foreground Lean process at a time. No full/umbrella build, heartbeat/recDepth change, numerical experiment, commit or push.
14 public theorem audit for first3, 8 for last2: all only [propext, Classical.choice, Quot.sound]. Final capstone types and mathlib API probes checked. Scratch audits exit0; removed after logging.
All5 imports wired. Owned forbidden-source and whitespace scans pass.
Latest lint exit1 only17 unrelated unreachable modules:
RHTower WeilPaperCauchyLattice; WeilWorkPBAPCritical{Abel,Boundary,Coefficients,Datum,DensityLaplace,Kernel,Laplace,Residue,Resonator,Window}; WeilWorkSettledPhaseInteriorCancellation.
HTGeometry ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra.
No WP07 error. Do not modify concurrent modules.

## Current search / primary evidence
Deep Laurent residue exponential polynomial logarithm arbitrary pole order Mellin budget90: partialfalse, semantic unavailable, refresh incomplete, mostlypending/stalecompiler; all candidate/source names/ingredient metadata inspected. Proposed discrete valuation field ingredients inapplicable.
Deep laurentCoeff double pole analytic numerator inverse square budget60: partialtrue, incomplete residue queries; availablehitsused.
Deep polynomial logarithmic Poisson mode differentiable under integral quarter eigenfunction budget90: partialtrue;68449files;stale snapshot/semantic unavailable,refresh incomplete. All20candidate+20source statements/ingredients inspected. Proposed log-derivative polynomial combination irrelevant. Existing quarterDefect_maassFun relevant and checked.
Lexical exact hasDerivAt_integral_of_dominated_loc_of_deriv_le: one declaration Bottcher.hasDerivAt_B in Bottcher/Brolin/RieszFlux.lean, others empty. Read225-268 as compact-interval usage pattern, NOT sufficient for noncompact integral.
Primary reopened Hochfilzer–Oliver https://arxiv.org/html/1910.02821v5 Lemma3.5; Neururer–Oliver https://arxiv.org/html/1809.06586v3 introduction. Twists/coefficient hypotheses stillunpaid. Allcurrent contributions BRIDGE / REDISCOVERED. Prior Lewis–Zagier source in EVIDENCE knows strongerperiodfunction machinery; do not claim novelty from corpus addition.

## Next spatial work — exact receiver and paid ingredients
MaassAxisUniqueContinuation.lean259:
RHTower.MaassAxisContinuation.eq_zero_of_axis requires ContDiffOn R infinity V upper, quarterDefect V=0, horizontal evenness, zero imaginary axis, AnalyticOnNhd R horizontal restrictions univ. Conclusion V0 throughoutupper.
Actual U already has smoothness and quarter equation from MaassBesselFunction, and coefficient PolyGrowth follows weighted absconv via MaassConverseLevelOne.polyGrowth_of_summable. Need pay these for actual polynomialPolarMode, not assume.
Existing polynomialPolarMode rho P z = sqrt(z.im)*integral P(log|t|)*polarKernel rho z t. All logarithmic moments integrable and invertible polynomial axis map alreadychecked (LogMoments,AxisPolynomial). Base polarMode evenness exists; polynomial evenness extension stillunwritten.
Mathlib Analysis/Calculus/ParametricIntegral.lean288 has hasDerivAt_integral_of_dominated_loc_of_deriv_le, works real/complex scalar; requires common neighborhood, measurability, startingintegrability, integrableuniformderivativebound, pointwiseHasDerivAt. Its Frechet version210 alsolocated.
PROOF.md now has explicit spatial paper plan:
q=(x-t)²+y², W=|t|^-rho P(log|t|).
Local y>=delta,|x|<=M => q^-1/2<=C/sqrt(1+t²).
Order n kernel derivative Pn(X,Y)q^-n-1/2 with homogeneous degree n polynomial. Recurrence q∂XP-(2n+1)XP and q∂YP-(2n+1)YP. Bound Cn delta^-n q^-1/2, plus sqrt(y) Leibniz. Integrable via existinglogmoments. Dominated continuity/differentiation induction gives C∞.
Dxx+Dyy=q^-3/2,Dy=-yq^-3/2, hence Δ(sqrt(y)D)=-sqrt(y)D/(4y²).
Horizontalholomorphic extension ((w-t)²+y²)^-1/2 for|Imw|<y/2 hasargument positiveReal, sameuniformmajorants; needsbranch/measurability/derivativeboundsinLean.
Moving boundary x->x0>0,y->0: subtractW(x) indicator|t-x|<=eta. UniformlocalLipschitz + tailmajorant gives integral=2W(x)arsinh(eta/y)+O(1) uniformlyx. Dividebylogy -> -2W(x0). Handlesmodularmovingimages; existingfixedx1limit insufficient.
Afterspatialidentification+modularboundaryrelations, existingFiniteBoundary forcespolynomials0, hencePnointeriorroots, thenMultiplicityrigidity. CompleteWP07alreadyepsilon+ viaCentralExclusion.
Fulltarget AND infinite-deficitconjecture remainOPEN.

## Self audits
All5 anti-theatre and4 anti-laziness answers inEVIDENCE: classical bridge,no scientificclassification,theoremfrontiermovedtoactualinteriorMaasspacket; spatialtransportfirstunpaidcore, no effortexcuse, reuse existing machinery. Nextgoalturn beginsfrom this checkpoint, not with redundantmodulebuilds.
Previouscontext: mem:research/weil-work-07-theta-defect-2026-10-07.
