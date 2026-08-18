---
name: route-e-fibre-step-one
description: The Hall-law fibre step 1 — the anchored-count fix, the o(√x/log x) requirement, and the single remaining gate
metadata:
  type: project
---

Step 1 of the two reciprocal-marker cards (`route-e-reciprocal-marker-mobius-hall-law`,
`route-e-growing-reciprocal-marker-low-breadth-transport`) is closed on its squarefree half and
blocked on exactly one thing.

**The requirement is `o(√x/log x)`, not "a small fraction of √x".** The marker join discards bad
fibres from a dyadic block carrying `≍ √x/log x` primes. A constant tolerance is therefore useless
however small; only a rate helps. Do not re-derive a positive-proportion statement and mistake it
for progress.

**The anchored-count fix.** `Sieve/AveragedSquarefreeTail.sum_tail_divisor_count_le` pays a `+1`
per divisor, giving `+M`; at the fibre data that term is `≍ 400√x` and no choice of `R` removes it.
Anchoring the multiple count at the origin (`Nat.Ioc_filter_dvd_card_eq_div`, so `⌊N/d²⌋ ≤ N/d²`
with no defect) removes it entirely — `Sieve/AveragedSquarefreeTailSharp.sum_tail_divisor_count_le_sharp`.
`Sieve/SquarefreeMaximalWindow.sum_tail_divisor_count_le_sqrt` only weakens `M` to `√(B+L)`; it is
not the same fix.

**Where it landed.** `Sieve/FibreTailSharp` (budget + Markov), `Sieve/FibreStepOnePositive`
(`card_outerBlock_ge`, `eventually_fibre_step_one_growing`, `eventually_fibre_step_one_positive`).
Truncation level `R = ⌈(log x)³⌉+100` is admissible because the squarefree-mass hypothesis only
needs `R` below a fixed fraction of `h = exp((log x)^{99/100})`, which beats every power of `log x`.
Squarefree exceptional count: `√x/(log x)²`.

**The one gate left.** `Sieve/MoebiusMeanSquare.averagedMeanSquare_moebius` is stated as
`Tendsto … (𝓝 0)`. Step 1 needs an explicit `≤ (log x)^{-A}`, `A > 1`. The majorants below it are
already explicit closed forms — `RhoLimit.rhoMajorant`, `SlopeQuotientLimit.slopeMajorant`,
`ConstQuotientLimit.constMajorant` — with dominant term `(log x)^{5/4-β-γβ}` squared, i.e. past
`(log x)^{-1.1}` at `β, γβ > 9/10`. Turning those three limits into inequalities is the remaining work.

See [[mt-e3-programme]] for the other Route E lane and [[lean-name-collision-breaks-umbrella]] —
`RHTower.Sieve.perronKernel` collided between `MixedMomentAssembly` and another session's
`HalaszPerronAssembly`; mine is now `perronTruncKernel`.
