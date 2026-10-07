# WP01 — Full PBAP existence

Status: open research target. Mode: paper research, then Lean. Read [shared contract](/Users/michael/Documents/code/hgt/docs/reports/weil-work/README.md).

## Single objective

Prove `RHTower.WeilOneSided.PrimeBlindPositive` unconditionally, using its full pole-plus-archimedean functional. This supplies some real integer-indexed full-positive sequence through an existing theorem. It does not by itself identify that sequence with von Mangoldt or prove RH.

For every finitely supported mixture `c` of full test functions, the exact target is

\[
c_f\ge0,\qquad \sum_f c_f L_n(f)=0\quad(n\ge2)
\quad\Longrightarrow\quad
\sum_f c_f A_{\rm full}(f)\ge0.
\]

Here `L_n` and `A_full` mean the existing `logValue` and `weilArchRe (EF.weilTest f f)` expressions. Preserve their normalizations and pole terms. Individual tests need not be prime-blind; cancellation can occur between tests.

## Starting evidence

- [Full PBAP definition and equivalence](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeOneSidedCriterion.lean:431): `PrimeBlindPositive`; `exists_weilPositiveFull_iff_primeBlindPositive`. Separation and realization from PBAP are already done.
- [Polar finite-level compactness](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistence.lean:119): `exists_weilPositive_iff_forall_level`. Its positivity premise remains necessary; it concerns the polar predicate.
- [Dilation-free support bound](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/DilationFreeSetMeasure.lean:103) and [log-lattice anticoncentration](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/LogLatticePoissonAnticoncentration.lean:837): usable restrictions, not the desired sign theorem.
- [Small-aperture polar positivity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PoleVanishingWeilPositivityPrimeTwo.lean:984): a bounded-aperture result, not an all-aperture proof.
- [Two-walls research card](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/producer-existence-two-walls.md) and [certified pinning card](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/certified-producer-pinning.md): inspect claimed paper/numerical progress separately from Lean status.

## First research milestone

Choose one precise class of signed or complex **mixtures** that extends the established subclasses in the refreshed corpus. Derive the exact archimedean-plus-pole energy under all integer-null constraints. Prove a new quantitative lower bound, or identify and prove the obstruction to that bound. Explain why the class is nonempty and which mixed cancellation it captures.

Then determine whether the argument extends to arbitrary finite mixtures. If approximation is used, prove preservation or controlled correction of every null constraint and convergence of the full functional. A small residual at finitely many log-integers does not establish PBAP.

## Exclusions and traps

- Zero weights, absolutely `1/√n`-summable weights, sparse total support of growth exponent below `1/2`, and the exact prime-only `log p` weights are already obstructed. See the audit's no-go table before proposing a producer.
- A positive signed measure on **real** multiplicative support is not an integer-indexed producer.
- Nonnegative-function or disjoint-support arguments do not cover arbitrary signed/complex mixtures. The known archimedean-only negative witness does not automatically satisfy the full PBAP premises.
- Carlson-type uniqueness applies under specific exponential-decay hypotheses. Do not infer that the entire compact-test null cone is trivial.
- A certified negative full-PBAP witness would contradict the proved implication RH ⇒ PBAP. It would be a major mathematical conclusion requiring exact admissibility and proof, not a numerical “failed optimizer” label.

## Search entry points

Run from `/Users/michael/Documents/code/hgt`:

```sh
scripts/formal_tools.py research 'PrimeBlindPositive' --mode lexical --exact --per-module 0 --explore 0
scripts/formal_tools.py research 'prime blind signed mixtures archimedean pole positivity' --mode deep --module Weil --budget-seconds 300
scripts/formal_tools.py research 'dilation free prime blind' --any --module DilationFree
```

## Completion and handoff

`CLOSED` requires the unconditional full PBAP theorem and its compiled application to `exists_weilPositiveFull_iff_primeBlindPositive`. A new subclass sign theorem is `CONDITIONAL ADVANCE`, with the extension gap stated. Send any produced λ and every proved property of it to the detector packages; existence alone does not pay their hypotheses.

Owned result directory: `/Users/michael/Documents/code/hgt/docs/reports/weil-work/results/01-pbap/`.

Owned initial card: `/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/weil-work-01-pbap.md`.

Reserved new Lean scope: `/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilWorkPBAP*.lean`. Existing modules are read-only. Output `RESULT.md`, `PROOF.md`, `EVIDENCE.md` as specified in the shared contract.
