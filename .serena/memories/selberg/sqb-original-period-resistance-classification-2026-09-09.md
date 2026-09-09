# SQB original-period resistance classification — 2026-09-09

Goal remains ACTIVE: unconditional RH proof/falsification through SQB. RH NOT proved; do not mark complete or blocked. User says frontier map READ ONLY. Preserve peer changes. Continue broad OR full-corpus research via scripts/formal_tools.py research --any --per-module 0 --limit 100000 --explore 0 --json, then inspect actual selected source proofs. No numerical computation was needed.

Completed module: formal/GaloisForLFunctions/RHTower/SelbergMaassPeriodResistance.lean (namespace same), 17 public declarations, ~340 lines. Imports SelbergMaassUnipotentPaths, SelbergMaassTraceDirection, SelbergMaassRegulatorMass. One RHTower umbrella import. Intrinsic source f is the complete congruence MaassCuspEigenform, arbitrary real lambda and positive height; helper cases remain explicit. No source node is asserted to exist.

Actual R_e(y)=integral_0^1 1/sqrt(D(x+iy)+e^2) dx. Exact classification:
* BddAbove(range R_e) over all e>0 iff D>0 on entire [0,1] period.
* Existence of finite real regulator limit iff same zero-freeness.
* R_e tends to atTop iff original period contains a common zero.
* Zero-free case: compact minimum constructs source/height-specific amplitude floor d>0; literal reciprocal integral R0 finite, 0<=R0-R_e<=e/d^2, R_e<=R0<=1/d.
* At any original node z=a+iy, C2 source regularity gives finite common first-derivative bound C on following complete period. Component mean-value bounds yield sqrtD<=L(x-a), L=1+sqrt(cardDeck*C^2)>=1. Thus r_e<=L(x-a)+e and R_e >= [log(L+e)-log(e)]/L -> infinity. Literal T-periodicity identifies node-started integral with original R_e.

Main declarations: exists_linear_amplitude_bound_at_node, integral_reciprocal_affine, exists_periodResistance_log_lower, periodResistance_tendsto_atTop_of_node, exists_period_amplitude_floor, reciprocal_error_bounds, reciprocal_amplitude_intervalIntegrable, periodResistance_error_bounds, periodResistance_tendsto_of_zero_free, unregularizedPeriodResistance_le, periodResistance_bddAbove_iff_zero_free, periodResistance_tendsto_atTop_iff_node, periodResistance_finite_limit_iff_zero_free. Definitions sliceAmplitude and unregularizedPeriodResistance; also continuity and scalar radius error.

Positive survivor is full actual-source finite-limit/floor/error theorem and exact classification, not only a toy obstruction. No route retired. Do NOT claim uniform d over y/N/f, infer nodes exist, or infer behavior of R_e*E_e from R_e divergence alone. Nodal residual curvature remains retained.

Connection to prior work: mem:selberg/sqb-unipotent-current-periods-2026-09-09 proves K_e(z)=N(2N+1)/12*(C_e(Imz)+C_e(Im(S^-1z))) with C_e=R_e E_e and original H_e=(pairE1+phase1^2+e^2 directionalE1)/r^3. Full original comparison retains mean plus (D+e²)K. Current period classification resolves R factor only.

NEXT: investigate JOINT current/resistance products and passage from weighted line estimates to literal quotient-area curvature lower bound >= amplitudeMass/8. Current total quotient curvature= lambda*amplitudeMass/2. Quarter gap is OPEN. Independent full-Xi spectral occurrence also OPEN, so quarter alone does not close RH. Broad new mechanisms can use full corpus; don't repeat toy resistance, pointwise/measure identification, block mixing or exact period scaling already closed.

Broad OR discovery metadata this turn: weights 62 rows/26 modules; nodal 775/226; mass/coarea 737/178; Lipschitz/reciprocal/log 734/613. /tmp/sqb17_{weights,nodal,mass,lipschitz}_broad.json. Actual inspected sources: SelbergMaassUnipotentPaths, TraceDirection, RegulatorMass, TraceMass, ResidualSupport, CurvatureNoAtoms, FourierMean, SelbergNodalResistance and mathlib mean-value/compactness/filter calculus. Counts aren't all-source proof inspections.

Audit ALL PASS: /tmp/sqb17_resistance.lean scratch, actual source via lake env lean; lake --no-build build leaf showed only new leaf stale; final lake build GaloisForLFunctions.RHTower.SelbergMaassPeriodResistance compiled only leaf (8817 cached graph jobs). All17 #print axioms reports only propext/Classical.choice/Quot.sound. All17 indexed exactly once; umbrella once. python3 scripts/formal_tools.py index and lint passed (existing large-file warnings). No owned compiler remains. No full/umbrella build, commit, push, numerical Runpod computation, or frontier-map edits.
Logs /tmp/sqb17_resistance_{scratch,source,preflight,build}.log, /tmp/sqb17_axioms.{lean,log}, /tmp/sqb17_audit_names.txt, /tmp/sqb17_{index,lint}.log, /tmp/sqb17_indexed_declarations.json.

Cards: docs/drafts/pipeline/{1-in-progress,3-formalized}/sqb-original-period-resistance.md. Updated previous stage1 sqb-unipotent-current-paths current dependency note and universal-law STATUS with route-independent reciprocal-cost/floor constraint. Preserve prior peer dirty shared files.

Lean details: .comp on horizontal point map needs explicit (f := fun t : Real => point t y); same point function partially applies in opposite argument if inferred. Type (e:Real)>0 explicitly from e.2 for linarith. For reciprocal affine primitive, construct typed HasDerivAt and simp only [id_eq,mul_one] using derivative chain before rewriting derivative value; naive convert produces nondefeq instance equality goals. Explicit IntervalIntegrable (... ) volume needed for unbound measure. integral_nonneg interval hx is Icc here (hx.1 already <=). Qualify UpperHalfPlane.im when Complex also open. regulatorAtZero = comap coe (nhds 0); lift to nhdsGT via positivity and tendsto_nhdsWithin_iff, not by definitional simplification. Put @[simp] attributes on separate lines for index parser.
