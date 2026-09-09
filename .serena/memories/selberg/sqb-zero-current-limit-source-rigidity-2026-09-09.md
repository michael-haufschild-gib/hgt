# SQB zero current-limit source rigidity — 2026-09-09

Active RH goal UNPROVED; do not mark complete or blocked. Goal turn SQB19 made verified progress: new source rigidity, nonflat-node positivity and actual exceptional-source alternative, 31 public declarations all audits PASS. Frontier map READ ONLY, no edits to it. No subagents, external numerics, Runpod, commit or push. Preserve shared peer work. Continue broad OR whole-corpus research, not ultraspecific default AND.

New module formal/GaloisForLFunctions/RHTower/SelbergMaassPeriodCurrentRigidity.lean (~396 lines), namespace same, imports only SelbergMaassPeriodCurrentLimit. One RHTower umbrella import.

## Exact new source mathematics

N and arbitrary real eigenvalue, complete original Maass source f; previous E_e(y)->E0(y)=periodCurrentLimit >=0. E_e integrates original H_e=(pairEnergy1+phaseCurrent1²+e²G1)/r³, G1=directionalEnergy1, r=sqrt(D+e²).

1 horizontalNumerator=pairEnergy1+phaseCurrent1², nonnegative. horizontalWeight b = numerator/r_b³. For all e<=b, W_b<=H_e. Continuity and actual period1 energy identify int[a,a+1] H_e=E_e. Pass to limit: EVERY fixed b, a has int W_b <=E0.
2 A nonzero numerator at any point forces positive fixed-weight integral, hence E0>0. E0=0 forces pairEnergy1=0 and total phaseCurrent1=0 at every point of that entire height.
3 Actual identity D*radialResidual=pair+phase and sum-square equality imply all component derivatives share the same real radial slope on D>0: Fq,x=(current1/(2D))*Fq.

4 At actual node z=a+iy with G1(z)>0, continuity gives d in(0,1] with G1>=k=G1(z)/2 on[a,a+d]. Prior source-derived L>=1 gives sqrtD<=L(x-a) on[a,a+1]. For e<=d and x in[a,a+e], r_e<=(L+1)e, so H_e>=e²G1/r³>=k/((L+1)^3 e). Integrate interval length e: E_e>=c=k/(L+1)^3>0 for ALL sufficiently small regulators. No guessed nodal measure, no pointwise-limit interchange. Therefore E0(y)>0 at every nonflat horizontal node.
5 Thus E0=0 forces G1(z)=0 at EVERY source node at height y, and every component's horizontal derivative vanishes there. The common real radial equation extends through ALL nodes (values also zero).
6 A nonflat node forces complete periodCost=R_e E_e ->infinity by previous R_e divergence and E0>0. Bounded nodal product families force zero E0, all pair/phase vanishing and zero first horizontal derivatives at nodes.

## Actual exceptional-source positivity

For μ in(0,1/4), source g, y>0:
* zero-free complete [0,1] period => E0(y)>0.
Proof: density period1 extends positivity to all x. If E0=0, normalized component derivative is zero everywhere (amplitude_mul_direction_dir + common radial law); derivative-zero mean value theorem gives constant normalized components on entire line. Actual Maass component zero means imply exists_separated_direction from every positive-density base point, giving squared chord>2 at same height. Constant directions give chord0, contradiction.
* E0(y)=0 => exists x in[0,1] with D(x+iy)=0 AND G1(x+iy)=0.
* Every positive height satisfies E0>0 OR exists such node.

CRITICAL scope:
- No exceptional source or node is asserted to exist.
- Alternatives need NOT be exclusive.
- A flat node does NOT imply E0=0; no converse classification proved.
- FLATNESS IS HORIZONTAL ONLY. F_x=0, not F_y=0 or full gradient zero.
- RadialSlope=current/(2D) has not been proved regular/integrable across nodes. Do NOT invoke ODE uniqueness at a source zero without proving needed coefficient regularity.
- Common radial derivative does NOT mean the source is constant or zero. On zero-free heights normalized direction is constant only in the zero-E0 case, which exceptional zero means exclude.
- No uniform source/height/level lower floor from positivity. Quarter-area bound remains OPEN.
- Independent full-Xi spectral occurrence remains OPEN; quarter alone would not close RH.

Main declarations: horizontalWeight_integral_le_limit, periodCurrentLimit_pos_of_numerator, pair_phase_eq_zero_of_limit_zero, component_radial_of_limit_zero, exists_node_derivative_floor, exists_node_current_floor, periodCurrentLimit_pos_of_nonflat_node, directionalEnergy_eq_zero_at_node_of_limit_zero, component_derivative_eq_zero_at_node_of_limit_zero, component_radial_everywhere_of_limit_zero, periodCost_tendsto_atTop_of_nonflat_node, component_derivative_eq_zero_of_node_bddCost, density_pos_on_height_of_zero_free_period, direction_constant_of_zero_free_limit_zero, exceptional_periodCurrentLimit_pos_of_zero_free, exceptional_exists_flat_node_of_limit_zero, exceptional_positive_limit_or_flat_node.

## Next substantive research

Full chain remains original modular source -> independent current comparison or full-Xi spectral occurrence -> critical-line classification -> RH. Need ORIGINAL source control of equality case (horizontal common radial law plus nodes with zero horizontal derivative), relative product rates there, and quantitative quotient-area comparison totalOrbitCurvature>=amplitudeMass/8. Actual full curvature=lambda*amplitudeMass/2. Do not merely restate positivity as quarter coercivity.
Broad corpus investigation of source PDE, nodal/symmetry geometry, original higher derivatives, quantitative radial-slope control could target remaining case. Do not assume horizontal analyticity/unique continuation theorem missing from corpus. Search hits in ChronometricRegionLocalization define an abstract UniqueContinuation predicate, not actual Maass elliptic continuation. Stronger claims must have independent paper and Lean proof.

Prior finished context: mem:selberg/sqb-full-original-period-current-limit-2026-09-09; mem:selberg/sqb-original-period-resistance-classification-2026-09-09. Exact source block cost two periods factor N(2N+1)/12, complete mean retained. Existing zero-free regulator removal and improved limiting coefficient4/3 are DONE.

## Search and audit

Broad OR full retrieval, per-module0:
zero energy/vanishing energy/rigidity/transverse zero/nodal/unique continuation:5008rows778modules;
concentration/shrinking interval/boundary layer/jump/positive integral/local mass:2305/538;
local positivity/positive mass/compact minimum/zero integral/vanishing derivative:303/208.
Metadata counts not all proof inspections. /tmp/sqb19_{rigidity,local_mass,positivity}_broad.json.
Actual sources inspected: PairPhaseEnergy, TraceRadial, TraceDirection (component means, negative correlation, normalized derivative), SourceCurrents, CurrentTests, PeriodCurrentLimit, PeriodResistance, CongruenceTrace periodicity. Mathlib interval positive integral, continuity neighborhoods, periodic representatives and is_const_of_deriv_eq_zero checked in scratch.

ALL audit PASS:
- Full scratch /tmp/sqb19_rigidity.lean and source lake env lean, no warnings.
- lake --no-build build named leaf found only new leaf stale.
- final lake build GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentRigidity compiled only leaf3.5s,8819 cached graphjobs. No full/umbrella build. Existing EvenL2LogUnitary informational replay.
- All31 public #print axioms reports only propext/Classical.choice/Quot.sound.
- All31 indexed exactly once, one umbrella import.
- python3 scripts/formal_tools.py index and lint passed, existing large-file warnings. Whitespace pass. All owned compiler handles terminal, final Lean/Lake executable scan0.
Logs /tmp/sqb19_rigidity_{scratch,source,preflight,build}.log; /tmp/sqb19_axioms.{lean,log}; /tmp/sqb19_audit_names.txt; /tmp/sqb19_{index,lint}.log; /tmp/sqb19_indexed_declarations.json.

Cards docs/drafts/pipeline/{1-in-progress,3-formalized}/sqb-zero-period-current-rigidity.md. Updated prior stage1 sqb-original-period-current-limit.md with new equality-case constraints. Added universal-law STATUS constraint on resolving equality cases before claiming strict lower bound. Frontier map untouched by this work. Goal active.

Lean details: directionalEnergy slice evaluates field derivatives at coe(ofComplex(point)), normalize with simp_rw[coe_ofComplex_point _ hy] before continuity. Explicit volume annotations on standalone IntervalIntegrable. intervalIntegral rewrite of pathEnergy needs explicit a (a+1) to target RHS, otherwise rewrites wrong subinterval first. For neighborhood floor, use typed x in Metric.ball and Metric.mem_nhds_iff; change beta-applied target before rw ofComplex_point_self. field_simp may close all algebra, omit trailing ring. direction normalized derivative proof: transfer ofComplex coe point and im=y explicitly, derive amplitude*dir=0, eliminate positive amplitude, then HasFDerivAt.comp_hasDerivAt point_horizontal and is_const_of_deriv_eq_zero. Function.Periodic.exists_mem_Ico₀ extends complete period positivity globally. Every compiler run foreground, one process per agent; dependent file creation/source checks guarded.
