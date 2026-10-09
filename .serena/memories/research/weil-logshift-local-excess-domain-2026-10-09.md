# Local excess replaces global finite excess

OUR LEAN CORPUS ONLY. No web/external papers. Goal active.

Formalized formal/GaloisForLFunctions/RHTower/WeilLogShiftLocalExcessDomain.lean, imports WeilLogShiftSingleProbeDomain. Card docs/drafts/pipeline/3-formalized/weil-logshift-local-excess-domain.md.

Write a=weilDeviation lam, e=deviationExcess, v=deviationDeficit, P_y=paired full kernel. The new exact local criterion for every m>=2 is:
Summable(a_n P_logm(n)) iff Summable(e_n P_logm(n)) AND an eventual integer-cutoff lower bound on actual probe Q_m.
No global finite-excess assumption. Signed summability always gives positive-part summability. Under local e moment, signed and v moments sum together. The exact split yields Q_L(c)<=W_L(c)+2*kernelPotential(e,c)+4*D_v(L)-2*T_v(L,c). Use arbitrary-positive-shift gain when origin moment diverges, bounded origin otherwise. Thus local e moment + nonsummable signed sample => real-cutoff Q_m -> minus infinity. Signed sample convergence gives exact finite limit via prior inward transfer, independent of finite excess.

Cofinal consequence: for ANY integer sequence m_j with log m_j unbounded above (no monotonicity or m_j>=2 requirement), whole-line signed convergence iff whole-line excess convergence plus individually lower-bounded probes. Reverse selects log m_j>=|y|+1, then m_j>=2 and inward transfer applies. Equivalently: subexponential a growth iff subexponential e growth AND cofinal probe lower bounds. Bounds/cutoffs depend on each probe.

Strictness witness formalized: lam(n)=vonMangoldt(n)+sqrt(n). a=e=1 for n>=2,0 otherwise; e is not summable, but all real-shift signed potentials converge by growth rate zero below every local critical rate. Therefore global finite excess was genuinely stronger.

Nine public declarations:
summable_excess_potential_of_summable_potential;
summable_potential_iff_deficit_of_local_excess;
logShift_probe_le_local_excess_deficit;
tendsto_logShift_probe_atBot_of_nonsummable_sample_of_local_excess;
summable_potential_iff_local_excess_and_probe_lower_bound;
exponential_bound_of_local_excess_probe_lower_bound (all b>2*pi/m);
summable_potential_iff_cofinal_local_excess_and_probe_lower_bounds;
subexponential_deviation_iff_excess_growth_and_cofinal_probe_lower_bounds;
exists_nonsummable_excess_with_summable_potentials.

Verification: direct leaf lake --old env lean with local -o exit0/no diagnostics. All9 scratch #print axioms only propext/Classical.choice/Quot.sound. Umbrella wired,index refreshed,all9 API rows checked,scoped diff-check passed. GLOBAL LINT FAILED on one unrelated unreachable module: GaloisForLFunctions.RHTower.CCMRestrictedWeilCrossFormBound. The two PaperCircle errors from preceding increment are resolved. Do not touch unrelated imports or rerun absent state change. All owned processes terminal; eight /tmp/hgt-weil-local-excess scratch files cleaned. No added analytic assumptions, numerical experiments, axioms, heartbeat increases, full builds, commits, subagents.

Important scope: inspected WeilLogShiftPointwiseCriterion.lean lines41-67; uniform positivity iff pointwise theorem STILL requires global finite excess even with sample convergence. Current result only strengthens domain/growth criteria; no removal of positivity premise asserted.

Next candidate: reflect coefficients lam'=2*Lambda-lam. Expect normalized deviation sign reversal, e/v exchange, and Q_lam+Q_lam'=2W from exact identity. Dual local theorem: finite deficit moment + nonsummable signed sample => Q_m -> plus infinity. Positive exponential deviation above local rate should yield lower-bounded divergent probes, proving local excess cannot be dropped. Requires fresh source/paper audit including n<2. Critical growth endpoint remains open. Prior: mem:research/weil-logshift-positive-shift-single-probe-2026-10-09.
