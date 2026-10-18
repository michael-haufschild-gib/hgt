Completed RB rotation contribution, corpus-only and unconditional (no RH or open analytic premise).

Files:
- formal/GaloisForLFunctions/BiScaleUncertainty/MertensValuationBudget.lean
- formal/GaloisForLFunctions/BiScaleUncertainty/RobinMovingValuationDefect.lean
- docs/drafts/pipeline/3-formalized/robin-moving-valuation-defect-2026-10-18.md
Both modules are wired into BiScaleUncertainty.lean.

Theorems: write N=floor(log n), L=log log n, D(n,N)=sum_{prime p<=N}p^(-(v_p(n)+1)). For every epsilon>0, eventually all n satisfy sigma(n)/n <= exp(gamma)*L*exp((1+epsilon)/L-D(n,N)). Thus every sufficiently large Robin counterexample satisfies D(n,N)<=(1+epsilon)/L. For every fixed 0<eta<1, every prime power p^k<=eta*L divides every sufficiently large counterexample, simultaneously in p,k. Consequently every positive integer m<=eta*L divides it, i.e. a growing lcm core.

Mechanism: identify the two reciprocal-prime sums and their constants; retain the favorable sign of the higher-prime-power tail to get inverse Mertens product <= exp(gamma)*log N*exp(a/log N), for any a>0 eventually, from Sieve.MertensSecondExpRate. Retain the floor ratio in the large-prime tail: exp((log n/N)/L), whose numerator tends to 1. Combine with exact sigma_div_le_mertens_defect. Choosing a=epsilon/4 yields the uniform budget. Prime factorization turns the budget into simultaneous divisibility.

Public capstones (namespace RHTower): eventually_inv_mertens_le_exp_small; eventually_sigma_div_le_moving_defect; eventually_robin_failure_defect_le; eventually_robin_failure_prime_power_core; eventually_robin_failure_integer_core. Both canonical leaves passed direct lake --old env lean -j 1 -o ... -i ... with no diagnostics. All 13 public declarations passed /tmp/hgt_rb_axioms.lean; only propext, Classical.choice, Quot.sound. Canonical source hashes: MertensValuationBudget 3c56a6b3dda4a0001b4e732fc4576d8d2c19efb9395d80d2bf67740597b9659a; RobinMovingValuationDefect 69abc714320e07fb23f6ff72162cabeeb06c81dfb475a5cb59e1a1ff5b8e19ce. Manifest /tmp/hgt-rb-audit-manifest.json. Logs /tmp/hgt-rb-{mertens-final,defect-final,axioms}.log. Superseded scratch Lean source copies removed.

Index passed (3 changed, 0 removed). Lint --check-generated fails only on three unrelated unreachable BiScale modules: IntegerAffineShear; StationaryResolventMarkovPositivityAndNodalDefectProducer; SummableIntegerAffineShear. No generated-index error or error in either owned module. Log /tmp/hgt-rb-final-lint.log.

This quantifies the fixed-defect exclusion; it does NOT settle the signed source estimate on increasingly saturated extremals at the square-root remainder scale. RH remains open. Rotate away from RB next; see mem:research/route-rotation-rb-2026-10-18.