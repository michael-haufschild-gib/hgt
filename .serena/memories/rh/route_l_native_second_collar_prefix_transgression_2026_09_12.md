# Route L C66: native second collar and prefix transgression

Goal ACTIVE: full-source fixed Gamma/BV reader agreement and RH remain UNPROVED. Proof chain: complete original source -> fixed-reader agreement -> conormal vanishing -> RH. C65 and C66 made verified progress; do not describe them as search-only. No unconditional reader producer yet.

## Verified C66 leaf
`formal/GaloisForLFunctions/RHTower/MobiusThetaNativeSecondCollar.lean`, wired after NativePrefixMass in RHTower.lean. Source exactly C64 h_(k,m), every k, positive native depth m and original cutoff p. Existing collar J h=e^-t h(-t). New actual second source is deningerMeyerCollarExchange(nativeMeyerSource), not a fabricated endpoint.
- Exact term law: mu(n) H_Jh(n|x|)=(-1)^k |x|^(m-1) mu(n)n^(m-1)H_h(n|x|), x!=0; n0 killed by mu0.
- `summable_norm_mobiusThetaNativeSecondCollar_weighted`: absolutely summable weighted tail all m>0, source membership produced by C65 and actual exchange.
- `mobiusThetaNativeSecondCollarTail_eq_weighted`, `_integrable`: complete p-tail, no depth or prefix replacement.
- Define Kp=F D(Ap(h))-D(Ap(Jh)); actual source prefix QBoundary=F D(Qp(h))-D(Qp(Jh)). `mobiusThetaNativeFullCollarBoundary_eq_commutator_sub_prefix`: Kp=K0-QBoundary. Private generic source a.e. decomposition and L1/distribution linearity prove it, not assumed agreement.
- `mobiusThetaNativeFullCollarBoundary_gamma_transgression`: existing adiabatic GammaBoundary-Kp=existing GreenStokesTransgression+QBoundary. This Gamma distribution has NOT been identified with fixed degree-six Gamma/BV reader. Do not substitute full distribution nullity for the requested scalar reader comparison.
- dual v=-v+i(1-1/m), `mobiusThetaNativeCollarDualParameter_centered`: m*s(dual)=1-m*s(v).
- `mobiusThetaNativeSecondCollarSource_mellin_data`: absolute admission and integral exp(m*s(v)t)Jh(t)=Xi^(k)(dual)/m for |Im dual|<1. Holomorphic reflection, not Hermitian physical reflection. No enlarged chamber claimed.

## Checks
Scratch /tmp/MobiusThetaNativeSecondCollar.lean passed terminal48100 exit0 without warnings. Final `lake build GaloisForLFunctions.RHTower.MobiusThetaNativeSecondCollar` terminal57499 exit0, leaf79sec,12353dependencyjobs; existing replay warnings only. /tmp/route-l-native-second-collar-build.log. No umbrella/full build, no limit raises, no eval/decide/new axioms/axiom reports. Global lint80096 exit1 solely concurrent unrelated unwired MaassCircleTransfer and ThetaCuspHawkingBMScalarJetEntries; headers checked, left untouched. /tmp/route-l-native-second-collar-lint.log. Scoped git diff --check passed. All owned Lean/search processes completed. No agents, commits or pushes.

Card `docs/drafts/pipeline/1-in-progress/route-l-second-collar-prefix-transgression.md` contains paper proof, exact endpoint checks, literature, seven audited search inventories and next target. Route L comparison paragraph updated. Universal STATUS unchanged: findings are route-specific.

## Full corpus searches C66
Seven direct documented deep --any cached JSON searches,120second budget; all20 candidate statements plus all20 method assumptions and all groups/ideas audited each. Partial source-only results, inventory complete, no hit treated as compiled proof/no hit absence. Artifacts under docs/drafts/pipeline/1-in-progress:
1 route-l-second-collar-weighted-source-search.json gen881517 snapshot881522;57123files47491Lean736002decl;pending44651. Useful actual exchange+sourcebounds, covariance notnullity. GammaCommonInverseCollar source-read147-189: local inverse branches late Gamma poles, not this comparison.
2 route-l-prefix-fourier-transgression-method-search.json samecounts/gen: linear subtraction relevant; conditionalSonin notproducer.
3 route-l-native-poisson-kernel-comparison-search.json gen881534 snap881553/current881554;57125/47491/736002;pending44651. Poisson/Meyer-cap and coPoisson premises remain; leadingconormal nonzero.
4 route-l-sewing-central-charge-comparison-search.json gen881593 snap881612/current881613;57128/47494/736472;pending44654. Cochains not actual modularfunctors/equalcharge.
5 route-l-native-power-fourier-comparison-search.json gen881714 snap/current881720;57130/47495/736487;pending44655. Dilation/weightedmeasure no nativeTate=spatialdimension identification.
6 route-l-native-theta-mobius-inversion-search.json gen881756 snap/current881760;57131/47496/736512;pending44656. Poisson transfer idea assumes actual preimage has Meyer-cap Schwartz representative. Logbinomial group notvanishing. Strict-chamber inverse-zeta transform retains Xi derivative.
7 route-l-native-logarithmic-prime-forcing-search.json gen881775 snap/current881780;57133/47498/736537;pending44658. Convolution, Mellin gauge and secondjet identities are actual sources; do not kill current. Two modular-theta signatures truncated, unused. Method missing for pwGammaMobiusPreimage, no inference. First5 zeroideas/1group each; last2 oneidea/1group each. Allgroups unverified.

## Recent primary literature
Broad single-word sewing arxivsearch newestfirst after unsuccessful recent transgression/descent. Maibach-Peltola2608.23201 Aug24 PDF: theorem1.1, Prop3.9 locality/sewingperfectness, section5.1 disk normalization read. Requires local smooth real1D modularfunctors and matched centralcharges; none constructed for readers, primecover not circle diffeo. Bakr-Zhang2608.11721 Aug12 HTML: sections10.1-10.3,13.1-13.2,theorem18.1 read. Complete proper-time history vs separatelycut segments have differentdomains; matching/positiveoperator/analyticcontinuation hypotheses not supplied here. No Lean import, no freecounterterm licensed.

## Next mathematical attack / source-derived caution
Power-coordinate normalization alone fails to justify removing affine reflection: positive ray u=x^m pushes dx to (1/m)u^(1/m-1)du. Merely replace by du changes Fourier. This is paper Jacobian observation, no new Lean power-Fourier theorem. Do not invent spatial dimension m.
Read actual ThetaCuspFinitePrimeSource: seed2pi(2pi t^4-3t^2)e^-pi t²; sourceTerm exp(t/2)Seed(n exp t); Phi=sum terms; D²g+Dg=Seed. C64 h=(exp(-mt/2))(im t)^k Phi(-mt). Reflection yields for n>0,x>0 termwise H_(k,m)(nx)=(im log(nx))^k sum_l Seed(l n^m x^m). Thus an unweighted Mobius inversion only addresses special jets/depths. Full all-k,m product-fibre regrouping with log weights and original p-prefix is not proved C66.
At m1,k1 coefficient sum_(d|N)mu(d)logd=-Lambda(N); a vonMangoldt current survives. **Do not reprove it generically**: full source-read `DeningerMobiusConnection.lean` proves -mu·log*zeta=Lambda and Lambda*mu=-mu·log; `deningerMobius_connection hh hx` establishes whole absolutely convergent ray current sum_m Lambda(m) MobiusPreimage h(mx)=MobiusDerivative h x. Source smoothness/allExp supplied C65. Potential next step source-derived higher internal-jet recurrence and exact fixed-reader pairing, retaining all p,m,k; no generic wrapper/zerojet-only proof claimed as RH progress.

## Exact endpoint inspected
`RouteRDegreeSixBVGreenPhysicalCyclicDescentWall`: tau=(5/6)d1+d6, normalized on Q, equal1/6 products, killsboundary. `DeningerOrdinaryIntegerBVGreenStokesRadialComparison`: E_n(s)=n^-1(1-g_n(s)^-1); reflectedn(E(s)-E(1-star s))=g-g^-1. `DeningerBurnolConormalRadialTopBoundaryComparison`: literal doubled Burnol windows, leading multiplicity-exact jet nonzero, squarednorm centeredcharacter=g. `RouteRDeningerBVGreenPositiveUnitComparison`: fixedreflecteddegree6boundary positiveunit*retainedHodgematecoefficient. Fixedequality def in RouteRDegreeSixGammaCoronaLocalGlobalFracture221 and iffzero229 remains equivalent to wallplacement, not produced. Full source-to-these-fixedreaders is obstacle.

Tools: Serena find_symbol failed ignored Lean paths; rg/sed fallback. Use narrow rg -g '*.lean', avoid dumping giant .ilean or all GammaSix hits. Explicit cast SchwartzMap required to apply DeningerMeyerSource.toSource subtype; complex absolute cast ((|x|:Real):Complex), not (|x|:Complex). integral_neg_eq_self needs explicit integrand; .comp_neg worked. Proof optimized with exact/simp only and Lp.toTemperedDistributionCLM map_sub, no limits.
