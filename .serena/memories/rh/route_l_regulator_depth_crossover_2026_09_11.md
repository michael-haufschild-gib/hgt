# Route L C29 — original regulator/depth crossover, fully audited

RH remains unproved; active goal remains open. Proof chain: complete Green/BV source -> agreement with fixed Burnol/Deninger reader at original horizontal anchor -> conormal vanishing -> RH. C29 supplies an exact source-side classification, not that agreement or all-prime source-action intertwining.

## Completed artifact and audit
- Module: formal/GaloisForLFunctions/RHTower/DeningerGammaSixRegulatorDepthCrossover.lean, 25 theorems, five definitions, wired immediately after CompleteIntegrandAdmission in RHTower.lean.
- Card: docs/drafts/pipeline/3-formalized/route-l-regulator-depth-crossover.md. Full dependency-closed paper proof, search/failed-transfer record, and audit.
- Scratch /tmp/route_l_regulator_depth_crossover.lean passed with empty log (all 25). Targeted lake build GaloisForLFunctions.RHTower.DeningerGammaSixRegulatorDepthCrossover succeeded; new module 15 seconds, dependency messages replayed. No full/umbrella build.
- /tmp/route_l_crossover_axioms.lean and .log print every source theorem. Exact set match, all 25 use only propext, Classical.choice, Quot.sound. No sorry/admit/added axiom/opaque/unsafe/#eval/native_decide.
- scripts/formal_tools.py lint passed, exit0, /tmp/route_l_crossover_lint.log ends formal lint passed. Repository warnings remain. This supersedes previous unrelated reachability failures.
- C26 (27 theorems), C27 (29), and C28 (45) already had completed targeted builds and complete axiom audits; the newly passing global lint cleared their only remaining gate. Their cards also moved to stage3, all matching doc links updated. Earlier memories saying stage2/pending global lint are obsolete. Their Lean sources were not changed/rebuilt independently.
- Updated frontier map, source-selected-completion-attack C29 closed section, and universal STATUS Must distinguish joint-limit damping from source annihilation.
- All owned processes terminal. Last successful scratch49240, build94648, axiom98846, lint58658. Earlier failed scratch52538 was explicitly terminated (owned pids98282/98209); all subsequent scratch sessions terminal. No subagents, commits, pushes, numerical experiments, or full builds.

## Exact mathematical result
At original w with |Im w|<1 and sigma=Re(s(w))>0, let c=XiC^(k)(w)*XiC^(l)(w), T_M=E_(6^M)*(T_kl(w,w)-cQ), N_M original successor normalizer, q=N1^-1, A=2*mu(successor6), B=log6/6, K=log6*c*(1-q)^-1*A*B. Let epsilon_M be eventually positive and tend to0. D_M=N_M*AbelDefect(epsilon_M,6,T_M)/epsilon_M^2, b_M=6^(-M*epsilon_M).
- D_M/b_M -> K for every such path, without assuming a limit of M*epsilon_M. This explicit diagnostic division does not redefine the fixed reader.
- Finite product limit tau gives D_M ->6^(-tau)*K. Infinite product gives D_M->0.
- At every ORIGINAL Xi divisor, K at multiplicity-top jet is nonzero. Actual (unnormalized) top defect is eventually nonzero along every such regulator path, even infinite-product paths. Adjacent lower/top actual defects form an exact zero/nonzero conormal pair.
- Finite ordinary diagonal repairs disappear pointwise from all literal Abel defects at sufficiently late original cutoffs, uniformly in regulator and ordinary dilation. Finite-product crossover is explicitly specialized; pointwise equality is stronger. This is not a finite-rank repair theorem.
- Critical top sources also retain these data. No RH selector or fixed physical comparison follows from suppression.

## Source proof mechanism
Apply original a^(-epsilon) and divisibility6 filter to C28 admitted integrands before integration. Norm<=1 preserves full integrated-norm summability, integrability of complete sum, integral/tsum equality. At late admitted cutoffs the actual projected Gibbs trace IS this complete source integral.
Exact H_m(eps)=sum actual divisible a in [6^m,6^(m+1)) a^-eps/a equals6^(-m eps)*G_m(eps), with G retaining a/6^m. Sandwich6^-eps H_m0<=G_m<=H_m0, C27 H_m0->B gives joint convergence and uniform bound.
Exact actual defect factorization retains gain6^eps-1 and original partitionZeps: gain/eps *1/(eps Zeps)*weighted projected trace. Fibre regrouping preserves n+216 and admission, then q^j*N_(M+j)=N_M extracts b_M. Moving array q^j6^(-j eps)[N_(M+j)C_(M+j)]G_(M+j)(eps) has fixed summable geometric majorant and limit sum=(1-q)^-1*A*B. Gain->log6, partition residue->1. This is an actual operator proof, not merely a shell model.

## Main APIs (namespace RHTower)
- deningerGammaSixNormalizedGibbsShell, _bounds, _nonneg, _uniform_bound; tendsto_..._joint.
- deningerGammaSixRegulatedMovingTail; tendsto_deningerGammaSixRegulatedMovingTail.
- deningerGammaSixGibbsShell_factor; deningerGammaSixRegulatedTailTerm, summable_..., ..._fiber, ..._tsum, ..._normalized.
- deningerGammaSixIntegralTailOperator_gibbsTrace; ..._regulated_factor.
- deningerGammaSixRegulatedSource; ..._tsum_data (norm summability+Integrable+integral=tsum); deningerGammaSixRegulatedTailTerm_eq_integral; deningerGammaSixIntegralTailOperator_gibbsTrace_eq_complete_integral.
- tendsto_deningerGammaSixIntegralTailOperator_crossover, ..._crossover_infinite, ..._crossover_deattenuated.
- deningerOrdinaryIntegerAbelDefect_congr_diagonal; eventually_deningerOrdinaryIntegerAbelDefect_finite_tail_repair.
- tendsto_deningerGammaSixIntegral_finite_repair_crossover.
- deningerGammaSixTailBoundaryLimit_crossover_top_ne_zero; deningerGammaSixIntegralTailOperator_crossover_all_divisors.
- eventually_deningerGammaSixIntegralTailOperator_regulated_top_ne_zero; ..._regulated_conormal_pair.

## Search audit / next work
Two deep/method queries each inspected20 candidates and20 source arguments; latest partial generation823349, semantic2196271/2337170, 56,615 files/56,021 inventoried/523 pending-stale. Suggested alternative Hurwitz cutoff exponent loses coupled source normalization; generic geometric estimates do not identify a reader. Broad recent adiabatic/resonance/homogenization/dilation searches checked arxiv2607.28383,2609.00942,2607.14372; effective-generator change, fixed ODE continuation/Wronskian, or preexisting contractivity assumptions provide no actual fixed-reader bridge and were not imported.
Do not repeat C29 or reduce it to a pure shell toy. The next hard attack must supply source-specific fixed-physical comparison at original anchor, retaining arithmetic actions and the conormal data; a zero joint limit cannot substitute for it. Universal ledger entry is deliberately route-neutral. Goal must NOT be marked complete for this auxiliary result.
