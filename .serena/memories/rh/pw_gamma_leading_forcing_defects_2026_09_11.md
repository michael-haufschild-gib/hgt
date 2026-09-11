# PW-B exact leading-prime forcing and raw connection separation — 2026-09-11

RH remains unproved; full goal active. Proof chain: literal finite-energy PW first winding -> FE partner imbalance -> positive Deninger Ward transmutation -> independently source-forced fixed-grade balance -> RH. Missing source-specific global balance, operator/domain/transmutation and Xi occurrence remain open. Do not mark the RH goal complete for this leaf.

## Closed new leaf
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusLeadingForcing.lean` (295 lines), imports GammaMobiusCurrent and Mathlib.Analysis.Normed.Group.Tannery. 12 public theorems, no new public definitions. Umbrella-wired.
Card: `docs/drafts/pipeline/3-formalized/pw-b-gamma-leading-forcing.md`. Attack card iteration 10 and next parameter-generator candidate: `docs/drafts/pipeline/1-in-progress/pw-b-source-orientation-attack.md`. Frontier and route-independent STATUS updated. Five deep search results and source/paper audit saved `.../1-in-progress/pw-b-gamma-leading-searches.json`.

Actual Q(x)=sqrt(x)e^-x, M(x)=sum mu(n)Q(nx), E(x)=sum -mu(n)log(n)Q(nx), x>0. Prior current and positive-reconstruction leaves prove admission, ZM=Q, JM=E, ZE=JQ>0. Do not confuse arithmetic E with a spatial differential forcing.

### New mathematical results
1. `pwGammaRaySource_ratio_scale` (line27): Q(nx)/Q(2x)=Q(n)/Q(2)*exp(-(n-2)(x-1)), n,x>0.
2. `pwGammaMobiusLogCurrent_leading_prime` (106): E(x)/Q(2x) -> log2 at +infinity. Normalize all summands at x=1; coefficients c_n=-mu(n)log(n)Q(n)/Q(2) form an absolutely summable series. n=0,1 vanish. For x>=1,n>=2 the remaining factor has norm<=1; n=2 stays log2 and all n>2 tend0. One uniform majorant and Tannery, no tail discarded.
3. `_eventually_pos` (123): Re E(x)>0 eventually (NOT global positivity).
4. `pwGammaRaySource_double_ratio` (133): Q(2x)/Qx=sqrt2 exp(-x), x>0.
5. `pwGammaMobiusLogCurrent_source_quotient` (147): E(x)/Qx ->0 at +infinity.
6. `_inverse_forcing_defect` (203), every z: (E(exp t)-rminus_z(t))/(exp(t)q(t)) ->1/2, where q(t)=exp(t/2-exp t), rminus_z=(-sinh(t)-z)q(t).
7. `_positive_forcing_defect` (224), every z: same with rplus_z=(1-exp t-cosh t-z)q(t) tends3/2.
8-9. `_ne_inverse_forcing` (247), `_ne_positive_forcing` (256): E o exp differs as function from either raw Gamma connection forcing at every z. Exact defect limits are the quantitative positive survivors; a negligible correction at this scale cannot repair equality. No physical counterterm constructed.
10. `pwLogInverseGainReflection_source_quotient` (267): Rf(t)/q(t)=f(-t)/q(-t), Rf=a^-1 f(-t), from a*q=q(-t).
11. `pwGammaMobiusLogCurrent_reflected_source_quotient` (275): R(E o exp)(t)/q(t) ->0 at -infinity. This is NOT a small-x estimate on E itself, nor reflection fixation of E.
12. Closed capstone `pwGammaMobiusForcing_leading_and_separation` (283): first-prime limit, eventual positivity, both inequalities for all z. No unproved RH premise.

## Audits
Scratch `/tmp/pwb-gamma-leading.lean`; axiom scratch `/tmp/pwb-gamma-leading-axioms.lean`; logs `/tmp/pwb-gamma-leading-{scratch,direct,build,axioms,lint,index}.txt`. Scratch/direct clean, targeted leaf build passed (107s,10689 jobs mostly cached replay), all12 have only propext/Classical.choice/Quot.sound. Lint passed (existing large-file warnings). Index regenerated and all12 entries confirmed. No public name collisions, diff check passed. All owned Lean/search processes finished. No full/umbrella build, no numerical experiments, no commits. Other user agents' processes/files preserved.

## Next concrete attack, current-source evidence
Arithmetic derivative in `DeningerMobiusConnection.lean` is coefficient -mu(n)logn, not t-derivative. Candidate actual Gamma family M_b(x)=sum mu(n) exp(-b logn) Q(nx). At b=0 derivative should be E(x). Needs uniform derivative-series bound on neighborhood across0. For |b|<1,n>=1, exp(-b logn)<=n (complex version by real part); logn<=n, so term derivative norm<=n^2 Q(nx). Exact source scaling gives n^2 Q(nx)=sqrt2[n^2 exp(-nx/2)]Q(nx/2); exponential tangent bound gives a constant uniform in n, and Q(nx/2) is summable. This is paper-only, not yet Lean.

IMPORTANT PRIOR WORK: follow-up deep search found `DeningerAdiabaticGreenStokes.lean`: `deningerAdiabaticMobiusScalar_hasDerivAt` line138; `hasDerivAt_deningerAdiabaticEvenPreimageLpExt` line428; `deningerAdiabaticEulerPositiveLp_ae_eq_parameterDerivative` line477. Already proves parameter derivative in L1 for DeningerMeyerSource and a>0. Majorant lines302-334 requires b>=d>0, summing logn/n^(d+1). Cannot specialize to Gamma (outside stronger source class) or at0. Transfer its method, not theorem assumptions. Current Mathlib `Analysis/Calculus/SmoothSeries.lean:90`, `hasDerivAt_tsum_of_isPreconnected`, exposes open preconnected neighborhood, a common summable derivative bound, term derivatives and convergence at one point. Pointwise Gamma derivative near0 must not be promoted to L1 derivative or selective spectrum without proof. Full tilted convolution should yield J_b M_b=partial_b M_b, with Lambda(m)m^-b. Need independently identify b with spectral Ward parameter and derive complete reflected balance; naming b spectral does nothing.

## Search/literature
Five deep searches partial; inspected declarations, source arguments, methods, proposed ingredients. Useful Tannery plus LSeries/Injectivity normalized tail and SuzukiWeilAppendixDerivative:513 fixed-majorant Lerch proof. Polynomial tailCoeff and XiShiftedMobiusHalfDensityGenerator are different objects; generic endpoint/ODE proposals do not match forcing.
Broad echo/droplet/impedance/renewal/condensation mostly irrelevant/old. Read Aug18 arxiv2608.17844 abstract and sectionII-D: Hermitian/Fourier commutation requires symmetric block-Toeplitz/circulant structure not established here. Jun25 arxiv2606.26789 abstract: data-based atmospheric spectral diagnostic, no arithmetic balance theorem. No external paper formal premise.

## Lean notes
One foreground Lean process per agent. All checks lake env lean; only final target lake build. Scratch name checks; #print axioms only tmp. New module uses `set_option backward.isDefEq.respectTransparency false`; with it unapplied composition/lambda expressions often need `Function.comp_def` or `dsimp only` before rw. `Function.comp_apply` may fail on an unapplied composition. Annotate constant limit in combined Tendsto.add. For private coefficient Summable goal, `change Summable (fun n=>...)` before simpa avoids instance/definition mismatch. No norm_num/decide evaluation in new leaf. Preserve shared worktree edits.
