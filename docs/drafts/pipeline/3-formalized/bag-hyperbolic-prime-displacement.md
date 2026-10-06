# BAG: actual ordered prime packet to continuous kernel

2026-10-06,21az. The actual ordered hyperbolic triple-prime packet P(N,M)
and literal signed continuous kernel J(N,M) satisfy, for every natural M,

    (log²N/N) ‖P(N,M) - J(N,M)‖ → 0.

No analytic premise appears. All original V/W factors, recentered phase,
physical reciprocal, contraction exclusions and sharp boundaries remain.
This closes the discrete-to-continuous transfer. Cancellation of J and
the full cubic complement remain separate obligations.

## Proof

Let δ=N^(1/5-1), a=1/(1+δ), and F(t)=Σ_{n≤floor3N}Λ(n)K(nt).
The actual dual average A equals ∫_[a,1] F(t)/(δt) dt, with full
integrability. Prove this termwise by positive dilation x=nt. The literal
kernel vanishes off [N,2N]; null endpoints reconcile the original half-open
windows. At t=1 the trace equals the original discrete von Mangoldt sum V.

Use c=(1+δ)/δ: c(1-a)=1, 0≤1/(δt)≤c and |1/(δt)-c|≤1 on [a,1].
Thus a uniform normalized sampled error η yields

    (log²N/N) ‖A-V‖ ≤ η + (log²N/N) δ ‖V‖.

20az supplies arbitrary η>0 eventually, uniformly on this entire window.
The actual kernel norm bound gives ‖V‖≤64π(M+1)·3N log(3N).
The normalization debt is O_M(log³N/N^(4/5)) and tends to zero.
Compose with19az's actual prime-power correction and A-to-J estimate.
No averaging mass is assumed equal to one, and no exceptional samples
are discarded.

## Lean audit

`ChiCubicHyperbolicPrimeDisplacement.lean`,436 lines:

- 58: `chiCubicHyperbolicPrimeTrace`.
- 63: `chiCubicHyperbolicPrimeTrace_one`.
- 207: `chiCubicHyperbolicVonMangoldtAverage_dilation`, including integrability.
- 371: `chiCubicHyperbolicVonMangoldtDisplacement_tendsto`.
- 404: `chiCubicHyperbolicPrimePacket_integral_tendsto`.

Final foreground leaf84470: `lake --old env lean` with explicit olean,
exit0, empty output. Log: `/tmp/bag-hyperbolic-prime-displacement-03az.log`.
Wired once into RHTower. Index99162 exited0; all five public API rows
checked. Imported axiom/API23376 exited0: all five declarations use only
propext, Classical.choice and Quot.sound. Log:
`/tmp/bag-hyperbolic-prime-displacement-axioms-21az.log`.
Lint67922 exited1:367 large-file warnings and eighteen unrelated unreachable
modules; no finding names this leaf. Global lint is not clean.
Log: `/tmp/bag-hyperbolic-prime-displacement-lint-21az.log`.

## Next hard step

Prove cancellation of the signed continuous kernel: uniform averaged
prime-pair prefixes pay small gaps, complete integer phase periods cancel
in the bulk, and actual amplitude freezing, ordering holes and band edges
must all be paid. The actual cumulative and harmonic prime-pair producers are now closed in
`ChiCubicHyperbolicPrimePairs.lean`; see `bag-hyperbolic-prime-pairs.md`.
Their full divisor remainder is paid uniformly in the gap cutoff.
The full cubic tail, growing moments/cofactors, common-height return and
RH remain open.
