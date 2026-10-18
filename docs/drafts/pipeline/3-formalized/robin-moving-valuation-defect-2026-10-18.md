# Robin counterexamples require a growing prime-power core

- **ID:** RB-moving-valuation-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RB route; `RobinInequalityKFree`, `MertensThirdTheorem`, `Sieve/MertensSecondExpRate`.
- **Statement:** For every ε > 0, all sufficiently large Robin counterexamples n satisfy
  `Σ_{p≤⌊log n⌋} p^{−(v_p(n)+1)} ≤ (1+ε)/log log n`. Consequently, for every 0 < η < 1,
  every prime power `p^k ≤ η log log n` divides every sufficiently large counterexample.

## Goal

Rotate from RW, TH and MSC into RB. Replace the fixed positive valuation-defect exclusion
with an unconditional shrinking budget. The two scales are n and its Euler-product cutoff
⌊log n⌋. This does not settle the increasingly saturated extremals, whose remaining signed
remainder is still open; it quantifies the necessary saturation rather than assuming it.

## Gates and plan

- [x] Prior-corpus search and direct inspection of applicable source theorems.
- [x] Dependency-closed paper proof below.
- [x] Formalize one-sided Mertens estimate with error o(1/log N).
- [x] Formalize moving defect bound and growing prime-power divisibility.
- [x] Clean canonical leaf audits, umbrella wiring, and index regeneration.
- [x] Standard-axiom audit of all 13 public declarations.
- [ ] Repository lint gate (three unrelated modules are missing umbrella imports).

## Paper proof [PROVED HERE]

Write `L=log log n`, `N=⌊log n⌋`, `S(N)=Σ_{p≤N}1/p`, and
`D(n,N)=Σ_{p≤N}p^{−(v_p(n)+1)}`. All eventual statements are at natural infinity.

1. The two corpus definitions of the reciprocal-prime sum agree termwise. Their constants
   agree by uniqueness of limits: the older prime-reciprocal theorem and the sieve estimate
   `|S(N)−log log N−M|≤C/log N` give the same limit. The corpus identifies
   `M=γ−H`, where `H=Σ_p(−log(1−1/p)−1/p)`.
2. Every summand of H is nonnegative. Therefore its finite partial sum is at most H, and
   `−log ∏_{p≤N}(1−1/p) ≤ S(N)+H`. The unconditional exponential estimate for S gives,
   for every a>0 and eventually N,
   `∏_{p≤N}(1−1/p)^{-1} ≤ exp(γ) log N exp(a/log N)`.
   Indeed `log N exp(−c sqrt(log N))→0`: put `u=sqrt(log N)` and use
   `u² exp(−cu)→0`. No absolute estimate for the higher-prime-power tail is needed:
   its favorable sign is retained.
3. Let r count the prime divisors of n greater than N. The exact arithmetic inequality in
   `sigma_div_le_mertens_defect` retains every local defect and bounds the remaining factors
   by `(1+1/N)^r`. Since `(N+1)^r≤n`, we have `r log(N+1)≤log n`. Since
   `log(N+1)≥L`, this tail is at most `exp(log n/(N L))`.
4. Fix ε>0 and put a=ε/4. Eventually `log n/N≤1+ε/2` and `L/log N≤2`, because
   `N/log n→1` and `log N/L→1`. Also `log N≤L`. Combining steps 2–3 gives
   `σ(n)/n ≤ exp(γ)L exp((1+ε)/L−D(n,N))`.
   Therefore `D(n,N)>(1+ε)/L` forces strict Robin. Contraposition proves the stated
   counterexample budget, including equality in the failure condition.
5. Fix 0<η<1 and choose ε=(1−η)/(2η), so `(1+ε)η<1`. Eventually `ηL≤N`.
   If `p^k≤ηL` is a prime power not dividing n, then `v_p(n)<k`, hence
   `p^{v_p(n)+1}≤p^k≤ηL` and its defect summand is at least `1/(ηL)`.
   This is strictly greater than `(1+ε)/L`, contradicting step 4. This proves all
   prime-power divisibilities simultaneously, with growing k and growing p.
6. Every positive integer `m≤ηL` then divides n: each prime power in the factorization of m
   is at most m and hence divides n by step 5. Compare each prime valuation. Equivalently,
   n contains the least common multiple of all positive integers through `⌊ηL⌋`.

## Scope and search audit

Both deep searches completed with partial results and a background-index refresh warning;
the compiler snapshot contains stale/source-only entries. Search results were treated as
leads only. Directly inspected the existing fixed-defect theorem, prime-sum exponential-rate
proof, Mertens constant identification and exact Euler-factor bound. Lean must verify all
used declarations against this toolchain. No numerical experiments or external sources.

## Log

- 2026-10-18 — selected RB after RW → TH → MSC; paper proof complete, formalization started.
- `MertensValuationBudget.lean`: canonical `lake --old env lean -j 1 -o ... -i ...` audit
  passed with no diagnostics. Five declarations identify the source constants, retain the
  favorable higher-prime-power sign, and produce the required shrinking product budget.
- `RobinMovingValuationDefect.lean`: clean canonical compilation passed for the moving defect,
  prime-power core, and all-positive-integer core, with no diagnostics. The 13-declaration
  axiom audit from `/tmp/hgt_rb_axioms.lean` passed: every declaration depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- Both new modules are imported by `GaloisForLFunctions.BiScaleUncertainty`.
- Index regeneration passed (`3 changed, 0 removed`). `lint --check-generated` found no
  generated-index error and no error in either new module. The global gate still reports
  three unrelated unreachable modules: `IntegerAffineShear`,
  `StationaryResolventMarkovPositivityAndNodalDefectProducer`, and
  `SummableIntegerAffineShear`, all in `BiScaleUncertainty`.
- Audit logs: `/tmp/hgt-rb-mertens-final.log`, `/tmp/hgt-rb-defect-final.log`,
  `/tmp/hgt-rb-axioms.log`, `/tmp/hgt-rb-final-index.log`, `/tmp/hgt-rb-final-lint.log`.
  Final-source fingerprint manifest: `/tmp/hgt-rb-audit-manifest.json`.

## Lean certificate and remaining frontier

- Source estimate: `RHTower.eventually_inv_mertens_le_exp_small` in
  `formal/GaloisForLFunctions/BiScaleUncertainty/MertensValuationBudget.lean`.
- Uniform signed exponent bound: `RHTower.eventually_sigma_div_le_moving_defect`.
- Counterexample budget: `RHTower.eventually_robin_failure_defect_le`.
- Growing prime-power core: `RHTower.eventually_robin_failure_prime_power_core`.
- Growing integer core: `RHTower.eventually_robin_failure_integer_core`.
  These four declarations are in
  `formal/GaloisForLFunctions/BiScaleUncertainty/RobinMovingValuationDefect.lean`.

The theorem strengthens fixed-defect exclusions to a uniform shrinking budget and a growing
divisibility core. It does not establish the required signed estimate on the surviving saturated
extremals at the square-root remainder scale. RH remains open. Rotate to another family before
extending RB; RW, TH, MSC, and RB have now received consecutive contributions.
