# Failed producer principles for arithmetic minimum classes

- **Stage:** 5-failed, specified candidate principles only
- **Parent objective:** [arithmetic classification and classwise RH exclusion](../1-in-progress/arithmetic-zero-minimum-classes.md), still open

## Candidate C: no negative minimum at a zero

The literal normalized profiles are `X_p=p Re(mu(p)W_p/[u(u+1)])` and `Y_p=p^(4 Re(s)-1) Re(mu(p)W_p/[u(u+1)])`, with `u=conjugate(s)` and the actual deletion remainder `W_p` defined in the parent card. The conjecture asserted nonattainment of a negative global minimum at every nontrivial zero.

**Outcome:** the obstruction is closed in Lean pointwise at every critical-line zero. Exact arithmetic inversion gives `sum X_p/p^2=-Re(1/[u(1-u)])/2`. A telescoping estimate `S2=sum 1/p^2<=2` forces some finite `X_p<-S2/[8(t^2+9/4)]`. The actual scaled remainder limit now identifies that threshold with the limiting lower boundary. The strict undershoot therefore forces an attained negative global minimum: `rightMinimum_attained_on_line`. Both profiles coincide there. This statement is quantified over actual critical-line zeros; the new modules do not separately prove the existence of such a zero from scratch.

## Candidate D: divisor dominance

The independent conjecture asserted `|W_(pq)|<=|W_p|` at every nontrivial zero.

**Outcome:** numerically rejected, not a Lean counterexample. At the 67th zero approximation, `|W_19|/|W_1|` is approximately `549.523061184344`, independently checked at 80 digits. The detailed computation and limitations are in the [Runpod report](../2-fully-proven/computations/arithmetic-zero-minimum-classes/REPORT.md). A uniform power-decay envelope does not imply pointwise dominance under divisibility.

## Positive survivor and formal status

The survivor includes the exact negative arithmetic balance, exhaustive classes with ties, squarefree positive labels, profile envelope, minimum/mean inequality, and critical-line undershoot. The [completed global audit](../3-formalized/arithmetic-global-minimum-classes.md) strengthens it: the ordinary remainder has an explicit first coefficient with a proved error bound; its multiples sum has an exact scaled limit; every positive-half-plane parameter has negative profile entries; profiles below the exact decay exponent attain negative minima and those above it are unbounded below. All have dependency-closed paper proofs and Lean certificates. The coarse class patterns are `(positive,0)` on the strict right, `(0,positive)` on the strict left, including at nonzeros, and equal positive labels at critical-line zeros. The `(0,0)` class contains no strip zero. At a strip zero, both labels positive is equivalent to critical-line location.

This does not retire proof by arithmetic classes. It rejects the two specified producer principles. The finite-label classes still require an independent arithmetic constraint excluding their off-line zeros. Merely making the labels exhaustive, or verifying equal labels on points already on the line, does not provide that constraint.
