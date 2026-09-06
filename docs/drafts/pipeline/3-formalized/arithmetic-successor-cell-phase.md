# Actual successor cells: exact source connection and alternating signs

Module: `formal/GaloisForLFunctions/RHTower/ArithmeticSuccessorCellPhase.lean`.
Namespace: `RHTower.DeletionMixedRefinement`.

**RH remains unproved.** This module closes a specific proof-strategy audit; it supplies no zero-exclusion law. No mathematical novelty claim is made.

## Exact theorems

For `b(x)=(fract(x)^2-fract(x))/2`, define the complex cell

`C_s(m)=integral_(m..m+1) b(x)x^(-conjugate(s)-2) dx`

and its real phase form

`J(sigma,t;m)=integral_(m..m+1) b(x)x^(-sigma-2)sin(t log x) dx`.

Ten public theorems prove:

1. `bernoulliComplexCell_im`: `Im(C_s(m))=J(Re(s),Im(s);m)` for positive integer cells.
2. `powerSumRemainder_successor_difference`: the exact trapezoid-defect successor recurrence, with no omitted endpoint.
3. `bernoulliComplexCell_eq_remainder_difference`: for `Re(s)>0`, `s!=1`, `m>=1`, `C_s(m)=[conjugate(R_s(m))-conjugate(R_s(m+1))]/[conjugate(s)(conjugate(s)+1)]`.
4. `sum_bernoulliComplexCell`: the finite cell sum retains the exact terminal remainder.
5. `tendsto_sum_bernoulliComplexCell`: ordinary infinite cell cutoffs converge to the initial normalized remainder. This declaration concerns ordinary cutoff convergence; no stronger summation statement is claimed here.
6. `bernoulliPhaseCell_dyadic_alternates`: for every real `sigma` and natural `k`, `(-1)^k J(sigma,pi/log(2);2^k)<0`.
7. `bernoulliPhaseCell_even_depth_neg`: even depths are strictly negative.
8. `bernoulliPhaseCell_odd_depth_pos`: odd depths are strictly positive.
9. `bernoulliPhaseCell_both_signs_cofinally`: both signs occur beyond every integer cutoff.
10. `not_eventually_bernoulliPhaseCell_nonpos`: eventual cellwise nonpositivity is impossible at this exact height.

The sign proof uses the phase interval `(k*pi,(k+1)*pi)`, the negative periodic quadratic inside each selected integer cell, and the positive power weight. It includes every dyadic depth, not a numerical sample. The source connection uses the already proved Bernoulli integral and remainder decay.

## Scope

The fixed height is not asserted to be a zero. The theorem concerns cells at a fixed unit anchor; it is not a theorem about normalized summands at moving anchors or prime-sieve insertion steps. It refutes the all-parameter cellwise strategy S, while leaving the separate conjecture `Im(g_s(n))<0` for `0<Im(s)<2*pi*n` open. Even that conjecture would not settle the exceptional head or imply RH.

The ordinary representation and integration identities are classical; the precise audit is a symbolic consequence of them. No excluded spectral or completed-function mechanism is used, and no numerical output enters the proofs.

## Validation

Scratch `/tmp/rh_cell_phase.lean` and source `lake env lean` checks passed. The module is wired into `GaloisForLFunctions.RHTower`. Final serialized leaf build, twelve public declaration axiom checks, and repository lint: pending at certificate creation.

Related records: [research card](../1-in-progress/arithmetic-successor-phase-threshold.md), [failed strategy and positive survivor](../5-failed/arithmetic-cellwise-phase-sign.md), [Runpod report](../2-fully-proven/computations/arithmetic-successor-phase-threshold/REPORT.md).
