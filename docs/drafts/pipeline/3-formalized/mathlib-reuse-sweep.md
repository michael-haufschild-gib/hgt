# Systematic sweep of unused mathlib assets

Status: audit result (with one connector formalized)
Date: 2026-08-09

## Method

Three reuse wins this session came from noticing mathlib files the corpus never imports (`Matrix.gram`,
`Gamma/Digamma`, `Analysis/SumOverResidueClass`). Rather than keep finding these by hunch, I enumerated every
mathlib module under `NumberTheory/`, `Analysis/SpecialFunctions/` and `Analysis/InnerProductSpace/` and
compared against every `import` line in the corpus.

**393 modules in scope, 216 never imported.**

## Result: the axis is close to saturated

Almost all 216 are other subjects — number fields, class numbers, FLT, p-adics, modular forms, Pell equations,
Diophantine approximation. Only three are plausibly relevant, and none fills a gap:

* `NumberTheory.LSeries.ZetaZeros` — mathlib's `riemannZetaZeros` with closedness, discreteness, and
  finiteness on compacts. The corpus states its zero facts through the `Ξ` divisor
  (`MeromorphicOn.divisor xi`), which already carries local finiteness, so nothing is duplicated. It is a
  *vocabulary* gap, addressed below.
* `Analysis.InnerProductSpace.Reproducing` — RKHS framework. The Nyman--Beurling carrier's bounded point
  evaluation is built directly as an inner product (`BaezDuarteL2Carrier`), which is complete; presenting it as
  an RKHS would be a re-presentation, not a gap fill.
* `Analysis.InnerProductSpace.Projection.Minimal` — the corpus's least-squares layer already goes through
  `starProjection` (`LeastSquaresProjection.starProjection_eq_of_normalEquations`).

Checked and confirmed *not* duplicated: `CarrierBoxCount` takes its finite zero set as a hypothesis rather than
proving finiteness, so mathlib's compact-finiteness lemma discharges nothing there; and the corpus already
imports `NumberTheory.AbelSummation` where it needs Abel summation.

## The one connector

`RHTower/ZetaZerosBridge.lean` closes the vocabulary gap:

* `exists_mem_riemannZetaZeros_of_not_riemannHypothesis` — `¬RH` produces a member of `riemannZetaZeros` with
  `½ < Re ρ < 1`;
* `riemannHypothesis_of_forall_mem_riemannZetaZeros` — the converse.

So results here can be quoted against mathlib's zero-set API, and mathlib's discreteness and compact-finiteness
lemmas apply to the zeros this development produces.

## For the next session

Do not repeat this sweep for these three directories. If looking for reuse, the productive directories were
`Analysis/InnerProductSpace` (Gram matrices), `Analysis/SpecialFunctions/Gamma` (digamma) and
`Analysis/SumOverResidueClass` — all now connected. Unswept areas that might repay the same treatment:
`Mathlib/MeasureTheory/`, `Mathlib/Topology/`, `Mathlib/LinearAlgebra/`.
