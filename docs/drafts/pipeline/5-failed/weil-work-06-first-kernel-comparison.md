# C21: universal first-kernel comparison fails

- **ID:** weil-work-06-first-kernel-comparison
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** docs/reports/weil-work/results/06-deficit/PROOF.md, C21
- **Statement:** The conjecture `K_k(1)<E_k` for every derivative order k is false at k=1.

## Goal

The proposed comparison would exclude C15's positive cardinal-spike mixture
at its first integer sample. Its failure retires this comparison only;
C15, C11q and the assigned spectral-deficit problem remain open.

## Gates

- [x] 0 → 1: exact actual product kernel and actual derivative energy fixed.
- [x] 1 → 2: dependency-closed counterexample and positive-survivor paper proof.
- [x] 2 → 3: six exact Lean statements, target build, unchanged direct source audit and standard-only axiom audits passed.
- [ ] 3 → 4: no publication or scientific-novelty certification.

## Approach

Expand the corpus cusp polynomials at k=0,1. The Schlaefli integral and
order recurrence bound B_1(z)/B_0(z) by 1+1/z for z>=1. A polynomial
with positive coefficients in y-6 then fixes the product-kernel signs.
Absolute divisor summation transfers those signs to entire integer columns.

## No-go closure

- **Exact killing theorem:** `RHTower.WeilWorkDeficitSign.energy_one_lt_productKernel_one_one` proves E_1<K_1(1), with the literal derivative-square integral.
- **Strongest positive survivor:** K_0(x)>0>K_1(x) for every real x>=2; consequently A(n,0)>0>A(n,1) for every integer n>=2. Also K_0(1)<E_0. These are complete signed-column statements, not just the negation of the failed comparison.
- **New insight:** The first two actual derivative columns point in opposite directions at every arithmetic row. Positive-mixture cancellation has genuine sign freedom. Single-summand Cauchy--Schwarz does not compare its reflected correlation with the energy of the entire theta sum.
- **Status:** `formal/GaloisForLFunctions/RHTower/WeilWorkDeficitLowOrderSigns.lean`, namespace `RHTower.WeilWorkDeficitSign`, six public theorems. Paper proof in owned PROOF. Target build23s/9886 jobs exit0; final unchanged `lake --old env lean` exit0/empty; all six exact-type and axiom audits exit0, only propext/Classical.choice/Quot.sound. Umbrella import verified. Mechanism is a classical-parent BRIDGE; no external scientific novelty claim.

## Log

- 2026-10-08 — C21a proposed, attacked, disproved, and its complete positive sign survivor formalized. Search coverage and primary-source ancestry recorded in owned EVIDENCE. Main WP06 card remains in progress.
