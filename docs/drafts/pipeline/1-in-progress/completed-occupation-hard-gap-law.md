# Completed occupation forces same-draw hard gaps

- **ID:** `completed-occupation-hard-gap-law`
- **Stage:** 3 -- formalized (canonical card moved to `../3-formalized/completed-occupation-quantitative-same-draw-hard-gap-law.md`)
- **Type:** theorem / deterministic same-draw plateau bridge
- **Status:** `[FORMALIZED] [SUPERSEDED BY QUANTITATIVE LAW]`
- **Date:** 2026-08-21

## Frontier

Existing completed-time laws bound long-time circuit-capture density for each fixed Hamiltonian.
Existing continuous-plateau laws instead start from ensemble fixed-time bounds and pay a time-grid
union.  Missing bridge is deterministic: turn completed occupation into a continuous hard interval
for the same Hamiltonian, without redrawing it.

## Theorem target

Let `A,B ⊆ ℝ`, `δ>0`, `W≥0`.  Suppose every `t∈A` satisfies
`Ioc t (t+δ) ⊆ B`.  If

`limsup_T windowProbabilityMeasure(T)(B) ≤ b`

and `b < δ/(W+δ)`, then for every `A₀≥0` there is `u≥A₀` such that
`Icc u (u+W) ∩ A = ∅`.

## Closed paper proof

Assume no such gap after `A₀`.  For each `k<N`, choose

`tₖ ∈ A ∩ Icc (A₀+k(W+δ)) (A₀+k(W+δ)+W)`.

The half-open intervals `Ioc tₖ (tₖ+δ)` are contained in `B`, pairwise disjoint, and contained in
`Ioc 0 (A₀+N(W+δ))`.  Their union therefore has volume `Nδ`.  Hence along
`T_N=A₀+N(W+δ)`, the window capture probability is at least

`Nδ / (A₀+N(W+δ)) → δ/(W+δ)`,

contradicting the strict limsup bound.

## Intended application

Take `A` as narrow-radius capture by the complete cutoff circuit dictionary and `B` as its
wide-radius version.  Uniform orbit speed gives visit thickness
`δ=(ε_w-ε_n)/speed`.  The completed physical-time circuit-density theorem supplies `b`.  Result:
arbitrarily late continuous intervals on which one fixed ordinary static local Hamiltonian avoids
the entire cutoff circuit set.

## Exact boundary

This proves arbitrarily late hard blocks and a first-return lower bound measured from each block
origin.  It does not yet force the first block to begin immediately after laboratory-time linear
growth; closing that onset gap remains necessary for the full growth--plateau--first-recurrence law.
