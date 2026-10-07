# WP07 actual theta defect checkpoint — 2026-10-07
Goal ACTIVE: exact denominator-three rigidity, docs/reports/weil-work/07-higher-denominator-rigidity.md. Current cycle PROGRESS, classical BRIDGE / REDISCOVERED; no scientific novelty or full rigidity. Use hgtl7 every turn. No subagents. Previous memory: research/weil-work-07-strip-decay-2026-10-07.

## New checked modules
Namespace RHTower.WeilHigherDenominator.
1. WeilWorkHigherDenominatorQuotientMellin.lean (6 public):
degreeTwoQuotientCoeff g = g convolved with integer Möbius cast to C.
degreeTwoQuotientCoeff_one preserves g1; degreeTwoQuotientCoeff_summable and LSeries_degreeTwoQuotientCoeff give absconv and L(f)=Lg/ζ on Re>1.
degreeTwoQuotientCoeff_weighted_summable supplies real weighted summability.
hasMellin_degreeTwoQuotient: actual MaassThetaMellin.kTheta f transform = (1/4) ΓR² Lg/ζ.
hasMellin_poleClearedDegreeTwoCompletion: transform = (1/4) L₂ on Re≥2, with exact P orders and P E=H ξ.
2. WeilWorkHigherDenominatorFinitePoleMellin.lean (6 public):
degreeTwoPoleSet P = P.roots.toFinset ∪ {0,1}.
deficitPolynomial_ne_zero_left from exact orders for Re≤−1.
degreeTwoPoleSet_re gives ALL possible poles in (-1,2), not yet strict (0,1) for interior poles.
poleClearedDegreeTwoCompletion_analyticAt_off, integrable_line (σ=-1 or2 and x>0 weights), horizontal_tendsto for both signs of height, contour_shift give actual arbitrary-order Laurent residue identity.
Every estimate produced from hD, exact P/H and existing rapid tails; no global bounded-through-poles assumption.
3. WeilWorkHigherDenominatorThetaDefect.lean (3 public):
reflection_right: L₂(1-s)=εL₂(s) on Re≥2 from E FE and exact factorization/orders.
degreeTwoQuotient_theta_defect:
Θ(x)−ε x^(-1) Θ(1/x)=(1/4) Σp∈Z laurentCoeff(s↦x^(-s)L₂(s),p,-1), every x>0.
degreeThree_infiniteDeficits_or_thetaDefect hD hE1:
Infinite deficit support OR ∃P,H,ε monic P, normε1, exact orders, entire finiteorder H,H1ne, exact factorization, actual theta identity for all x>0.
No added producer premises.
Existing StripDecay private xi_ne_zero_right was exposed unchanged as public theorem, final rechecked.

## Checks
All three final direct foreground lake --old env lean -o ... module checks exit0, no diagnostics, one process at time. StripDecay rechecked exit0 after exposure. All SIXTEEN public theorem audits (6+6+3+1) print only [propext, Classical.choice, Quot.sound]. Final scratch reused API audit also exit0. Imports wired into RHTower.lean (lines shift with concurrent work). No umbrella/full builds, heartbeat hacks, experiments, commits/pushes.
Lint captured exit1: thirteen unrelated unreachable modules. RHTower WeilWorkPBAPCritical{Abel,Coefficients,Datum,Kernel,Laplace,Residue,Resonator,Window}; HTGeometry ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra. No WP07 error. Owned scans pass.
A mistaken unchanged StripDecay invocation after relative-path edit failure was terminated using exact owned PIDs, exit143 checked before replacement. All final builds succeeded. No live process at checkpoint.

## Next mathematical work
Full target and conjecture 'every nontrivial complete datum has infinitely many deficits BELOW ONE COPY ord ξ' OPEN. Competitor finite support; stronger linear deficit growth candidate remains open.
Actual Mellin/contour/reflection is now paid. Next:
1. Strict interior pole strip 0<Reρ<1. Current contour lemma only (-1,2). Source RiemannXiZerosInfinite exists_riemannZeta_zero_mem_openStrip proof shows ξ→ζ and reflected ζ, zero-free Re≥1. Can prove directly via two_xi_eq plus ξFE and ξ1ne; verify names.
2. Expand every residue as x^-ρ Qρ(log x), arbitrary Laurent orders; prove Q=0 implies removability. Endpoint terms at0,1 degree≤1. PROOF.md has exact cancellation sqrt(y)(b+a log y)/4 for positive sign. Complete datum supplies ε+ through CentralExclusion.
3. Existing AxisPolynomial invertible axis realization already pays all polynomial orders. Spatial Poisson smoothness, quarter PDE, horizontal real analyticity and moving-point polynomial boundary limits remain unformalized.
4. Once interior poles vanish, reuse checked Multiplicity divisor-containment rigidity on complete datum. Do NOT rebuild degree-two classification.
Endpoint survivor c(1−1/x) forbids extending strict-positive-exponent boundary no-go to exponent0.

## Next API entry points
Read this turn:
HTGeometry/MeromorphicPrincipalPart.lean exists_taylor_remainder, eq_add_principalPart;
MeromorphicLaurentCoefficient.lean laurentCoeff_eq_taylorCoeffZero, laurentShift, taylorCoeffZero.
Searched but exact applications not yet audited:
MeromorphicLaurentTranslation.laurentCoeff_congr, laurentCoeff_eq_zero_of_analyticAt;
Mathlib Analysis/Calculus/IteratedDeriv/Lemmas.lean iteratedDeriv_mul (ContDiffAt inputs).
General residue formula: for admissible clearing k,
Q(X)=Σj<k laurentCoeff F ρ(j-k) (-X)^(k-1-j)/(k-1-j)!.
All coefficients vanish if Q0; principal part splitting gives removability. No simple-pole shortcut.

## Process reminders
AGENTS/docs absence/current card already checked for completed turn; next turn initialize fresh. Read hgtl7 every turn and inspect current corpus/literature. Broad deep search completed partial=false but 66k output truncated; do not claim exhaustive reading. Lexical target query source/idea sections empty. Primary audit Hochfilzer–Oliver arxiv1910.02821v5 Theorem3.1 still requires twists/coefficient bounds, Kaczorowski–Perelli arxiv2603.13885 starts extendedSelberg inputs.
Use rg before guessed paths; >500lines slices; no reading research source/help unless failure. Keep card/results current; shared ledgers read-only. Preserve concurrent work.
Successful ContinuousAt.comp in line proof needs explicit f,g,x to prevent incorrect inferred domain.
No Complex.analyticAt_const_cpow / Complex.hasDerivAt_const_cpow; use verified Differentiable.const_cpow then analyticAt.
Final docs contain paper proof before code and exact verified checkpoint. Anti-theatre5/anti-laziness4 posted honestly.
