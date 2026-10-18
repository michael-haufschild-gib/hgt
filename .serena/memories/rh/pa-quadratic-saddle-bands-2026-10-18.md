# PA: populated positive saddle bands at quadratic scale

RH remains OPEN. Full Hausdorff positivity remains OPEN. This component is unconditional and removes the local absolute-phase bottleneck, not the complementary-spectrum sign problem.

## Canonical files
- formal/GaloisForLFunctions/BiScaleUncertainty/CompensatedHausdorffPhase.lean
- formal/GaloisForLFunctions/BiScaleUncertainty/HausdorffSaddleScale.lean
- formal/GaloisForLFunctions/RHTower/PrimeArchQuadraticSaddleBands.lean
All wired into relevant umbrellas. Do not full-build umbrellas.

## Exact result
RHTower.exists_quadratic_positive_primeArchHausdorff_saddle_bands: exists real H>=1 and natural A>0 such that for every k,r with A*(k+1)^2<=r, T=sqrt(r/(k+1)), the actual radius-one atom sum over T<|Im rho|<=T+H retains at least half its total absolute mass and is strictly positive. Atoms are x_q^(k+1)*(1-x_q)^r. No RH, simplicity, or new analytic hypothesis.
RHTower.scaledHausdorffMomentDifference_one_eq_saddle_add_complement: exact normalized prime--archimedean difference at radius 1 = band real sum + absolutely convergent complement.
RHTower.exists_quadratic_primeArchHausdorff_complement_deficit: in the same type of quadratic region, any negative full source difference forces the complementary sum below minus half the positive band's absolute mass.

## Mechanism
BSU signedPowerPhaseBudget n r tau sigma = |n*tau-r*sigma|+(n*|tau|^3+r*|sigma|^3)/3. Existing cubic arctangent remainder gives global Re(product)>= (1-B^2/2)*norm(product), so B<=1 retains half. Actual lambda=Re x at height u satisfies 1/(u^2+1)<=lambda<=1/u^2, hence a=lambda/(1-lambda) is in [1/u^2,1/(u^2-1)]. In T<=u<=T+H with r=n*T^2, T>=max(4,H), |n-r*a|<=4nH/T, r*a<=2n, a<=1, |tau|<=2/T. Budget <=8nH/T^2+8n/T^3<=5/16 when 32nH<=T^2. This replaces the earlier local requirement T proportional to n by T^2 proportional to nH.
The unconditional logarithmic RVM remainder supplies nonempty fixed-width bands: H=16*pi*(C+1), threshold S>=max(H,4,(2*pi*e)^2,T0). Take A=ceil(S^2+32H+1).

## Validation
All 3 canonical commands lake --old env lean <leaf> -j1 with olean/ilean outputs exit 0, empty logs. All 19 public declarations checked via /tmp/hgt-pa-axioms.lean: only propext, Classical.choice, Quot.sound. Three capstone/source types checked. Initial and 35 additional API probes passed. scripts/formal_tools.py lint exit 0 (existing large-file warnings only). Source hashes verified unchanged. Lexical research finds all 3 signedPowerPhaseBudget declarations. Audit files: /tmp/hgt-pa-{phase,scale,source,axioms,lint}.log, /tmp/hgt-pa-audit-manifest.json, /tmp/hgt-pa-source-sha256.txt. No owned Lean/search process remains after audit.

## Cards and boundary
Formalized component: docs/drafts/pipeline/3-formalized/pa-quadratic-saddle-bands-2026-10-18.md.
Open full-array conjecture: docs/drafts/pipeline/1-in-progress/pa-growing-order-phase-cancellation-2026-10-18.md.
Radius is explicitly 1, not the endpoint radius. A positive band can coexist with an off-line divisor; it does not establish RH. Need arithmetic control of complement. Do not rebrand extracting the already implicit cubic full-array threshold as significant progress. Short-window Littlewood result assumes RH and was rejected as dependency.

## Lean lessons
Use lam/hlam rather than lambda Greek character, which parsed as reserved token. Rational scalar normalizations may require explicit calc/ring instead of linarith or convert. field_simp for slope identity needs explicit nonzero thermal node and complement. No heartbeat changes. Other workers share workspace; preserve their files/processes.
