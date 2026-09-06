# Failed producer principles for arithmetic minimum classes

- **Stage:** 5-failed, specified candidate principles only
- **Parent objective:** [arithmetic classification and classwise RH exclusion](../1-in-progress/arithmetic-zero-minimum-classes.md), still open

## Candidate C: no negative minimum at a zero

The literal normalized profiles are `X_p=p Re(mu(p)W_p/[u(u+1)])` and `Y_p=p^(4 Re(s)-1) Re(mu(p)W_p/[u(u+1)])`, with `u=conjugate(s)` and the actual deletion remainder `W_p` defined in the parent card. The conjecture asserted nonattainment of a negative global minimum at every nontrivial zero.

**Outcome:** rejected on paper, with a Lean-proved obstruction. Exact arithmetic inversion gives `sum X_p/p^2=-Re(1/[u(1-u)])/2`. At a critical-line zero, a telescoping estimate `S2=sum 1/p^2<=2` forces some finite `X_p<-S2/[8(t^2+9/4)]`. The existing paper remainder asymptotic makes that threshold the lower tail boundary; the strict finite undershoot forces an attained negative minimum. The new Lean module proves the balance, reciprocal-square bound and finite undershoot. The final asymptotic-to-attainment step remains paper-only, so a complete Lean negative theorem for C is not claimed.

## Candidate D: divisor dominance

The independent conjecture asserted `|W_(pq)|<=|W_p|` at every nontrivial zero.

**Outcome:** numerically rejected, not a Lean counterexample. At the 67th zero approximation, `|W_19|/|W_1|` is approximately `549.523061184344`, independently checked at 80 digits. The detailed computation and limitations are in the [Runpod report](../2-fully-proven/computations/arithmetic-zero-minimum-classes/REPORT.md). A uniform power-decay envelope does not imply pointwise dominance under divisibility.

## Positive survivor and formal status

The survivor is the exact negative arithmetic balance, unique exhaustive minimum classes including all ties and nonattainment, squarefree support of positive labels, the derivative-normalized profile envelope, opposite-side decay and finite-minimum confinement, the minimum/mean inequality, and mandatory finite undershoot at every critical-line zero. These have dependency-closed paper proofs and are formalized in `ArithmeticZeroMinimumClasses.lean`; [the certificate](../3-formalized/arithmetic-zero-minimum-classes.md) lists the exact declarations.

This does not retire proof by arithmetic classes. It rejects the two specified producer principles. The finite-label classes still require an independent arithmetic constraint excluding their off-line zeros. Merely making the labels exhaustive, or verifying equal labels on points already on the line, does not provide that constraint.
