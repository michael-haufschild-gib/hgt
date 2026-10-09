# Every positive shift; exact single-probe convergence domain

Source restriction: OUR LEAN CORPUS ONLY. No web/external papers. Goal remains active.

Formalized two new leaves:
- formal/GaloisForLFunctions/RHTower/WeilLogShiftPositiveTailGain.lean (imports WeilLogShiftTailComparison)
- formal/GaloisForLFunctions/RHTower/WeilLogShiftSingleProbeDomain.lean (imports PositiveTailGain and LocalDecayThreshold).
Card: docs/drafts/pipeline/3-formalized/weil-logshift-positive-shift-domain.md.

Core premise discharge: c>=4 is replaced by c>0 in uniform truncated autocorrelation tail gain. bulkCutoff(L,t)=S(L-t)S(L+t). For |t|<=L-d, cutoff>=S(d)^2. On central interval radius d, z>=0 and z/2+2d<=L, K_L(z)>=(2d*((2*pi^2)*S(d)^2)^2)*exp(-2*pi*exp(z+2d)). Take d=c/4,z=y-c; when original kernel is visible, y<2L gives the margin automatically. Lower rate B=2*pi*exp(-c/2)<2*pi leaves room for an upper full-kernel rate q between B and 2*pi. Ratio decays; arbitrary tail gain holds uniformly in ALL real cutoffs. Three public theorems: bulkCutoff_ge_transition_sq; truncatedRiemannAutocorr_central_lower_of_margin; exists_truncatedRiemannAutocorr_tail_shift_gain_of_pos.

SingleProbeDomain eight public theorems:
1 exists_truncated_origin_gain_bound_of_pos: arbitrary nonnegative weights, c>0, 4*D_L<=T_L(c)+4H.
2 tendsto_logShift_probe_atBot_of_nonsummable_deficit_origin_of_two_le: finite excess, divergent deficit-origin moment, m>=2 => actual real-cutoff probe tends to minus infinity.
3 summable_deficit_origin_of_probe_bounded_below_of_two_le: one eventual integer-cutoff lower bound, finite excess, m>=2 => origin deficit summable.
4 summable_kernelPotential_of_abs_lt: arbitrary signed v; convergence at c implies convergence at y whenever |y|<|c|, with NO minimum gap. Proof uses local critical rates and an intermediate exponential growth bound.
5 tendsto_logShift_probe_of_summable_sample: m>=2, signed sample convergence => exact finite real-cutoff limit 2*(psi(log m)-psi(0)); NO finite excess or separate origin hypothesis.
6 summable_potential_iff_logShift_probe_bounded_below: finite excess,m>=2 => sample summable iff eventual integer-cutoff lower bound.
7 tendsto_logShift_probe_atBot_of_nonsummable_sample: finite excess,m>=2,nonsummable signed sample => probe tends to minus infinity. Split on origin deficit moment; no oscillatory/positive-divergence alternative.
8 exponential_bound_of_logShift_probe_lower_bound_of_two_le: finite excess,m>=2,lower bound => |a_n|<=C_b exp(bn) for EVERY b>2*pi/m, removing old log m>=4.

Verification: both direct leaf `lake --old env lean <leaf> -o <local olean>` checks exited0 no diagnostics. All11 #print axioms only propext/Classical.choice/Quot.sound. Both umbrella imports added. Index refreshed and all11 API rows inspected; scoped diff-check passed. GLOBAL LINT FAILED on three unrelated unreachable modules: RHTower.CCMRestrictedWeilCrossFormBound, RHTower.PaperCirclePosteriorFourierMetric, RHTower.PaperCirclePosteriorPortraitStability. Do not report global lint clean, touch those imports, or rerun without observed state change. All jobs terminal; nine owned /tmp/hgt-weil-small-shift files removed. No full builds, numerical jobs, new analytic assumptions/axioms, heartbeat increases, commits, subagents.

Next conjecture: relax global unweighted finite excess to summability of positive-excess potential at the individual probe. The probe identity only needs an upper bound on its positive-excess sample contribution; new strict inward transfer gives its origin moment too. Need fresh paper/corpus audit of signed/deficit decomposition and origin/sample divergence cases. Critical growth endpoint still open. Prior memory: mem:research/weil-logshift-local-decay-threshold-2026-10-09.
