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

**The one gate left is Halász for μ, not bookkeeping.** `MoebiusMeanSquare.averagedMeanSquare_moebius`
has rate `Θ(1/log log x)`, and step 1 needs `o(1/log x)`. The obstruction is structural, so do not
try to fix it by turning `RhoLimit`/`SlopeQuotientLimit`/`ConstQuotientLimit` limits into explicit
inequalities — those three are already powers of `log x`. The binding term is the fourth summand in
`BudgetLimit.tendsto_normalised_omegaBudget`: `NonSpectralBudget.nonSpectral_div_le` gives
`120·mertensS(zhi)/W²` with `W = mertensS(zhi) − mertensS(zlo) ≍ (β−γβ)·log log x`, i.e. the Ramaré
normalisation's `1/W`, and `W ≤ log log x + O(1)` for every admissible prime range.

The power of `log` in Menon's `(log log L)²/(log L)²` comes from Halász: `D(μ,n^{it};N)² ≥ (2−o(1))
log log N` uniformly in `t`, so `(1+M)e^{-M}` carries a `1/log`. The corpus owns Halász mean-value
machinery (`Sieve/HalaszMeanSquare`, `Sieve/DirichletPolyAffineMeanSquare`,
`Sieve/HalaszDichotomyInstance`) but not the pretentious-distance lower bound for `μ`. That, plus
its insertion into the omega budget in place of the trivial `|μ| ≤ 1` coefficient bound, is the work.

The corpus's long-range Möbius savings (`Sieve/MoebiusKappaTwoRate` exponent 1/3,
`Sieve/MoebiusSavingKappaTwo`) do not substitute: at window `exp((log x)^{99/100})` the zero-free
region error `x·exp(−c(log x)^{1/3})` dwarfs the window.

See [[mt-e3-programme]] for the other Route E lane and [[lean-name-collision-breaks-umbrella]] —
`RHTower.Sieve.perronKernel` collided between `MixedMomentAssembly` and another session's
`HalaszPerronAssembly`; mine is now `perronTruncKernel`.
