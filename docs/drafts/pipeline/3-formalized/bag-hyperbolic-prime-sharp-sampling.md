# BAG: actual hyperbolic kernel variation and sharp sampling

2026-10-06,20az. CLOSED in Lean: the actual ordered hyperbolic prime
kernel has global variation O_M(sqrt N), and its complete von Mangoldt
sampled displacement is uniformly o(N/log²N) throughout the entire
multiplicative averaging window. The exact integral comparison to the
dual average and signed packet cancellation remain open in Lean.

Write K(N,M,x) for the literal kernel and δ=N^(1/5-1). For every natural
M, there is C_M>0 such that, for N≥4 and log N≥1,

    Var(K(N,M,·); R) ≤ C_M sqrt N.

This includes global bounded variation and every sharp cutoff jump.
For every ε>0, eventually in N, for every t∈[1/(1+δ),1], Lean proves

    (log²N/N) ‖Σ_{1≤n≤floor3N} Λ(n)[K(N,M,n)-K(N,M,tn)]‖ < ε.

No analytic premise, assumed regularity budget or deleted exceptional
set appears. The actual V/W factors, recentered complex phase, physical
reciprocal, logarithmic density and both noncontraction exclusions remain.

## Proof

Expose the proved compact derivative budget of the actual scaled
logarithmic Gaussian profile as a uniform norm/Lipschitz producer.
Factoring the literal amplitude gives norm O(1/(N log N)) and Lipschitz
constant C(d+1)/(N² log N), d=|p-r|. Nonzero integer gaps satisfy d≥1.
Clamp the amplitude to [N,2N]∩[r-Mr/d,r+Mr/d]; its length is at most
4MN/d. The three indicator factors defining the exact support have
total variation at most6, including open/closed endpoints and empty
supports. Product variation gives pair variation at most
(8CM+12pi)/(N log N).

Nonempty support forces d²≤2MN, hence d≤(M+1)sqrt N. Reuse the proved
hyperbolic integer-pair count at real anchor0 with strip parameter
2(M+1)N sqrt N. At most28(M+1)N sqrt N log N pairs remain. Summing
their global variations proves the actual full-kernel estimate. The
extra logarithm relative to the sharper paper count is harmless for
the required displacement and avoids an unnecessary new counting lemma.

For a bounded-variation complex function, its monotone variation
primitive bounds ‖f(n)-f(tn)‖ by v(n)-v(max(0,n-h)) whenever
(1-t)B≤h and n≤B. Finite telescoping leaves at most h values bounded
by total variation. This includes all jumps. Apply to the actual K,
retain Λ(n)≤log(3N), and take h=ceil(3Nδ). The complete weighted
displacement is bounded by C_M(3Nδ+1)sqrt N log(3N). Its normalized
envelope is at most constants times log³N/N^(3/10)+log³N/sqrt N,
which tends to zero unconditionally.

## Lean and validation

- `ChiCubicHyperbolicPrimeVariation.lean`,631 lines: actual amplitude
  Lipschitz producer at259, structural variation family at572,
  unconditional eventual variation at620. Final foreground leaf56733,
  `lake --old env lean` with explicit olean, exit0 and empty output:
  `/tmp/bag-hyperbolic-prime-variation-final-20az.log`.
- `ChiCubicHyperbolicPrimeSampling.lean`,238 lines: actual sampling at100,
  full von Mangoldt sampling at119, entire short window at154, uniform
  normalized negligibility at188. Final foreground leaf43723, same
  audit command, exit0 and empty output:
  `/tmp/bag-hyperbolic-prime-sampling-02az.log`.
- `ChiPrimeGaussianProgressionProfile.lean:169`:14-line actual profile
  producer; final foreground leaf98625 exited0 with empty output:
  `/tmp/bag-actual-log-profile-lipschitz-02az.log`.
- `ChiCubicHyperbolicPrimeKernel.lean`: exposes the existing literal
  support, amplitude and amplitude norm bound at123,128,142; bodies
  unchanged. Final foreground leaf20848 exited0 with empty output:
  `/tmp/bag-hyperbolic-kernel-public-api-20az.log`.

Imported axiom/API audit92008 exited0:
`/tmp/bag-hyperbolic-prime-variation-axioms-20az.log`. All20 checked
declarations, including every public kernel declaration and all new
producers, use only propext, Classical.choice and Quot.sound. API probes
26966,96360,4802 passed; nonexistent `Finset.sum_Ioc_eq_sum_range` was
discarded before the successful probe. Leaf failures exposed casts and
algebraic normalization obligations, no mathematical counterexample.
No new axiom, admission or heartbeat override.

Both new leaves are wired once. Index13677 exited0; all eleven new
public API rows were checked. Authoritative lint92001 exited1:367
large-file warnings, fifteen unrelated unreachable modules and one
unrelated proof-debt finding in `KuznetsovGammaZeroModulusSum.lean:267`.
No finding names the four changed BAG leaves. Global lint is not clean.
Log: `/tmp/bag-hyperbolic-prime-variation-lint-20az.log`.
No full/umbrella build, numerical experiment, subagent, commit or push.

## Remaining exact transfer

The uniform sampling theorem does not itself identify the dual average.
The next target is the actual identity obtained by x=nt in each original
half-open dual window, with full integrability and finite exchange.
Let a=1/(1+δ), w=1/(δt), c=(1+δ)/δ and V=ΣΛ(n)K(n). On [a,1], c has
mass1, 0≤w≤c and |w-c|≤1. Integrating the full sampled difference
therefore gives ‖A-V‖≤E+δ‖V‖ when E is its uniform norm bound. The
existing actual kernel bound pays ‖V‖≤64pi(M+1)*3N log(3N), making
the remaining normalization error negligible. This direct comparison
avoids introducing or dividing by κ=log(1+δ)/δ. Paper proof is on the
active phase-cell card; Lean implementation remains.

Then formalize the averaged prime-pair specialization and complete phase
period cancellation. No estimate for the growing complement, full cubic,
growing moments/cofactors, common-height return or RH is claimed.
