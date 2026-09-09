# SQB full original current-period limit — 2026-09-09

Goal ACTIVE, RH UNPROVED. This goal turn SQB18 made verified progress: 33 public Lean declarations plus two private differentiation helpers, all audits passed. Frontier map READ ONLY; no edits to it. No numerical computation, Runpod work, commit, push or subagents. Preserve shared peer changes.

New module: formal/GaloisForLFunctions/RHTower/SelbergMaassPeriodCurrentLimit.lean, namespace same, ~344 lines. Imports SelbergMaassPeriodResistance, SelbergMaassRegularizedCusp, mathlib DominatedConvergence. Wired once in RHTower umbrella.

## Main new mathematical content

Complete original Maass source F, D=||F||², e>0, r=sqrt(D+e²). Horizontal current H_e=(pairEnergy1+phaseCurrent1²+e² directionalEnergy1)/r³, actual one-period E_e(y)=int0^1 H_e(x+iy).

Define accelerationPair A_x(z)=Σq Re(Fq,xx(z) conjugate Fq(z)); accelerationBound B_x(z)=Σq ||Fq,xx(z)||; accelerationDensity=A_x/r; sourceAccelerationDensity=A_x/sqrtD (zero quotient at common zeros); periodCurrentLimit E0(y)=-int0^1 sourceAccelerationDensity.

PROVED, arbitrary intrinsic Maass eigenvalue and every y>0, WITHOUT zero-free or extra regularity/integrability assumptions:
1. Full second derivative D_xx=2(directionalEnergy1+A_x).
2. Radius second derivative r_xx=H_e+A_x/r, at every source point including nodes.
3. Actual C2 plus period1 cancels int r_xx exactly, so E_e(y)=-int0^1 A_x/r.
4. Each ||Fq||<=sqrtD; |A_x|<=B_x sqrtD; hence ||A_x/r||<=B_x. At D=0, A_x=0. Both regulated and limiting source quotients bounded by B_x.
5. Original C2 makes B_x continuous on horizontal slices, hence an integrable majorant on every compact interval. Quotient measurable even with nodal discontinuities. Dominated convergence proves complete signed-acceleration integral limit WITHOUT deleting nodes.
6. E_e -> E0, E0>=0, and E_e,E0<=int B_x. All original period current integrals have finite limit and a regulator-independent source-specific bound.

CRITICAL: This is NOT integral of pointwise H_e limit. Periodic boundary cancellation transforms the integrand first, retaining all nodal energy. Do not drop nodal curvature or claim sourceCurrentDensity alone captures total current. The acceleration functional may be zero; no E0>0 existence claim is made.

## Joint products and exact regulator removal

Previous mem:selberg/sqb-original-period-resistance-classification-2026-09-09 gives R_e finite limit iff period zero-free, R_e->infinity iff node. Here C_e=R_e E_e:
* Zero-free period => C_e -> R0 E0.
* Node plus E0>0 => C_e->infinity.
* Bounded family C_e at a node => E0=0.
* Under E0>0, C_e divergence iff original period contains a node.
* At nodal heights with E0=0, relative rates remain UNDECIDED. Finite E_e limit is not product control.

limitingPeriodCost=R0 E0. If both original complete periods y=Imz and y'=Im(S^-1z) are zero-free:
blockPathCost K_e -> parameterMoment N*(C0(y)+C0(y')).
D <= cardDeck*||sourceMean||² +16 D parameterMoment N*(C0+C0').
For D>0 and original sourceMean=0:
1 <= (4/3) N(2N+1)*(C0+C0').
This is the exact limiting constant (no factor2 regulator threshold), with both zero-free premises RETAINED. It is not a global nodal-free assertion or quarter-area bound.

Main declarations: radius_horizontal_second, periodCurrentEnergy_eq_acceleration, sourceAccelerationDensity_intervalIntegrable, acceleration_integral_tendsto, periodCurrentEnergy_tendsto, periodCurrentLimit_nonneg, periodCurrentEnergy_le_accelerationBound, periodCurrentLimit_le_accelerationBound, periodCost_tendsto_of_zero_free, periodCost_tendsto_atTop_of_node, periodCurrentLimit_eq_zero_of_node_bddCost, periodCost_tendsto_atTop_iff_node, blockPathCost_tendsto_of_zero_free, density_le_mean_add_limiting_periods, limiting_period_cost_lower_of_mean_zero.

## Active next research

Full chain original modular source -> independent current comparison or full-Xi spectral occurrence -> critical-line classification -> RH. Quarter quotient target totalOrbitCurvature >= amplitudeMass/8 OPEN; actual totalOrbitCurvature=lambda*amplitudeMass/2. Full-Xi occurrence ALSO OPEN. Do not equate quarter gap with RH.

Current source functional E0 now exact, finite, nonnegative. Need source-specific positivity/rate information and quotient-area comparison retaining invariant mean, source-dependent resistance, level factor and actual nodal curvature. Potential new investigation: characterize actual E0=0 case; it is forced by bounded nodal products. Do not assume every zero transverse, strict E0 positivity, or global nodal-free periods. Generic C2 periodic scalar sources can have flat nodal crossings, so source PDE/congruence structure must provide any stronger assertion. This latter observation is only analysis guidance, NOT a newly formalized classification. Broad corpus research before new code.

## Search and authoritative proof evidence

Broad full-corpus OR queries, no per-module cap, full retrieval:
weighted length/arc length/resistance energy/capacity/Cauchy defect/weighted variation:2495rows367modules;
transverse zero/simple zero/nodal/boundary layer/concentration:1480/324;
oscillation/harmonic mean/Poincare/coarea/isoperimetric/Cheeger:2478/375;
acceleration/second derivative/periodic integration/boundary cancellation/signed curvature:1041/430.
Counts metadata, not all proof inspections. Outputs /tmp/sqb18_{product,nodal,area,acceleration}_broad.json.
Read actual TraceEnergy, TraceRegularized, TraceRadial, SourceCurrents, UnipotentPaths, PeriodResistance, ChordEnergy, CurrentDensity, RegularizedCusp, ScalarHorizontalAverage, NodalCurvature. Decisive reusable generic results: normSq_second_dir, second_dir_sum, average_horizontal_second_eq_zero and radius_slice_periodic. PhysicalIntervalAnchorCoarea inventoried only, not an actual source comparison.

ALL AUDIT PASS:
* /tmp/sqb18_current_limit.lean full scratch lake env lean; source lake env lean both no warnings.
* preflight lake --no-build build named leaf found only new leaf stale.
* final lake build GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentLimit compiled only leaf 4.2s;8818 graphjobs cached. No full/umbrella builds.
* All33 public #print axioms reports only propext Classical.choice Quot.sound; public results transitively cover both private helpers.
* All33 public indexed exactly once; index ALSO returns private sq_dir,sq_second_dir =>35 total rows. Do not misinterpret35 as duplication.
* One umbrella import; repository python3 scripts/formal_tools.py lint passed with existing large-file warnings; diff whitespace checks passed.
* No owned Lean/Lake process remains; all handles collected terminal.
Logs /tmp/sqb18_current_limit_{scratch,source,preflight,build}.log; /tmp/sqb18_axioms.{lean,log}; /tmp/sqb18_audit_names.txt; /tmp/sqb18_{index,lint}.log; /tmp/sqb18_indexed_declarations.json.

Cards docs/drafts/pipeline/{1-in-progress,3-formalized}/sqb-original-period-current-limit.md. Updated current notes in stage1 sqb-original-period-resistance.md and sqb-unipotent-current-paths.md. Added universal-law STATUS constraint: identify full integrated limit before singular product; exact boundary cancellation and nodal rate distinction. No route retired; don't add a frontier label.

Lean details: conj written (starRingEnd Complex), continuity via (Complex.conjCLE:Complex->L[Real]Complex).continuous.comp; Continuous.re not available, use Complex.reCLM.continuous.comp. Ne.symm hz rather than hz.symm when by_cases inferred implication. Explicit mu:=volume in free integral_mono_on prevents stuck measure. Change pointwise negative integrand before intervalIntegral.integral_neg when Continuous.neg inferred function-neg. coe_ofComplex_point takes x hy (no N/f). Open ModularGroup and SelbergMaassCongruenceAverage for literal S and sourceMean, else autoImplicit can introduce unintended variables. blockPathCost_eq_two_periods uses explicit N factor, so simp parameterMoment_eq too. Two local sq_dir/sq_second_dir helpers mirror private inaccessible regularization identities, with full proof; no added axioms. Mutations and dependent compile calls sequential; use task root for paths beginning formal/, formal cwd only for Lake commands.
