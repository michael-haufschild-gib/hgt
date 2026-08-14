# Triple-reporter fusion, additive dissipation, and fourth-organ propagation

- **ID:** ULF-TRF-PROGRAMME-1
- **Stage:** 1-in-progress
- **Type:** FUSION MECHANISM
- **Status:** `[ABSTRACT FUSION LAW LEAN-PROVED] [SOURCE REALIZATION OPEN]`
  `[NOT ROUTE-SPECIFIC] [NOT RH]`
- **Date:** 2026-08-14

## Target mechanism

Let one source history `x_n in E` have three structurally different continuous linear reporters

\[
 R_i:E\to F_i\qquad(i=1,2,3)
\]

whose product reporter `R=(R_1,R_2,R_3)` has a common decoder `Q`, so `QR=id`. Give each organ a
nonnegative continuous strictly convex energy `W_i` with compact sublevels and form

\[
 W(z)=W_1(R_1z)+W_2(R_2z)+W_3(R_3z).
 \tag{TRF.1}
\]

Prove one fusion law, not three analogies:

1. `R` reconstructs the entire formed source core;
2. `W` is strictly convex because joint recovery makes `R` injective;
3. component compact sublevels and `Q` force compact sublevels of `W`;
4. midpoint dissipation is exactly additive across the three organs;
5. convergent total energy plus nonlinear no-loss selects a singleton source core;
6. every fourth continuous affine reporter then has singleton formed core.

The exact conservation identity to prove is

\[
 \Delta_W(a,b)=\Delta_{W_1}(R_1a,R_1b)+
 \Delta_{W_2}(R_2a,R_2b)+\Delta_{W_3}(R_3a,R_3b),
 \tag{TRF.2}
\]

where

\[
 \Delta_V(u,v)=\frac{V(u)+V(v)}2-V\!\left(\frac{u+v}2\right).
\]

This is the requested three-organ fusion plus fourth-organ prediction. It dies if proof needs route
labels, a fitted source selector, or a postulated compact source carrier.

## Acceptance gate

Abstract gate is closed by ULF-TRF-1: `(TRF.1)`--`(TRF.2)`, joint reconstruction,
component-to-global properness, selection, and arbitrary fourth-reporter propagation are Lean
proved without added axioms.

Remaining gate is source realization: construct one pre-specialization HGT source with three named,
structurally nonisomorphic reporters satisfying common recovery and the energy hypotheses. A formal
product of three existing organs does not count.
