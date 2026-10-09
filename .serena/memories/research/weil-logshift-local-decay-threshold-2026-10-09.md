# Local paired-kernel exponential threshold

User source restriction: OUR LEAN CORPUS ONLY. No web or external papers.

Formalized `formal/GaloisForLFunctions/RHTower/WeilLogShiftLocalDecayThreshold.lean`, importing `WeilLogShiftSubexponentialDomain`. Card: `docs/drafts/pipeline/3-formalized/weil-logshift-local-decay-threshold.md`.

For K=riemannAutocorr and P_y(n)=K(y+log n)+K(y-log n), define r(y)=2*pi*exp(-|y|). At log m, m>=1, r=2*pi/m. Existing ExposingRayTail autocorr_upper/lower give P_y(n)<=C exp(-a*n) for all positive a<r and n>=1; eventually D exp(-b*n)<=P_y(n) for every b>r. Lower bound selects K(log n-|y|) using evenness.

Arbitrary signed v: summable |v_n|exp(-a*n) for ANY a<r implies potential summable at y; converse gives every damping b>r. Pointwise growth |v_n|<=C exp(rho*n), rho<r, implies convergence. Convergence gives a pointwise bound at each b>r. Pure exponential weights exp(rho*n), rho>r, diverge. CRITICAL EQUALITY OPEN: no iff/assertion at rho=r.

Actual probes: subcritical normalized-deviation growth at rho<2*pi/m gives exact finite real-cutoff probe limit 2*(psi(log m)-psi(0)), WITHOUT finite excess. Conversely, finite excess plus eventual lower boundedness of one integer-cutoff probe with log m>=4 implies all coefficient-growth bounds b>2*pi/m.

Public API: logKernelCriticalRate; logKernelCriticalRate_pos; logKernelCriticalRate_log_nat; exists_paired_logKernel_upper_of_lt_rate; exists_paired_logKernel_lower_of_rate_lt; summable_kernelPotential_of_damping_lt_rate; summable_damping_of_kernelPotential_of_rate_lt; summable_kernelPotential_of_exponential_growth; exponential_bound_of_summable_kernelPotential; not_summable_exponential_kernelPotential_of_rate_lt; tendsto_logShift_probe_of_subcritical_exponential_growth; exponential_bound_of_logShift_probe_lower_bound.

Verification: leaf `lake --old env lean ... -o .lake/build/lib/lean/...` exit0 no diagnostics; all12 #print axioms only propext/Classical.choice/Quot.sound. Umbrella wired, index refreshed and all12 API rows checked. GLOBAL FORMAL LINT PASSED (previous unrelated missing imports now resolved). No added assumptions, sorries, heartbeat changes, numerical work, full builds, commits or subagents. All owned jobs terminal; scratch prefix /tmp/hgt-weil-local-threshold removed.

Read current RiemannKernelTailDecayRate entire200lines: bounds theta kernel Phi derivative/antitonicity/edge minimum, not autocorrelation local threshold. No need reread external materials. Prior chain memory: mem:research/weil-logshift-subexponential-domain-2026-10-09.

Next unresolved candidate: lower log m>=4 to any positive shift in cutoff-tail gain using positivity inside smooth cutoff transition; requires fresh paper and corpus audit. Endpoint rho=r needs finer prefactors, not settled by current exponential envelopes. Goal stays active.
