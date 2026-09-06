# Arithmetic zero classes from attained remainder minima

- **Stage:** 1-in-progress
- **Frozen objective:** independently defined, exhaustive arithmetic zero classes with a proved location constraint in every class. No classification alone counts as an RH proof.

**Current result:** A and B are formalized, including exact analytic admission, unique coverage of all complex exponents, squarefree positive labels, the class-specific minimum/mean constraint, and a proved critical-line undershoot. C fails: the undershoot is now proved without numerical input; together with the existing paper remainder asymptotic it forces negative minimum attainment at critical-line zeros. D fails numerically, with an independent 80-digit witness. The objective's third requirement is unresolved for the finite-label classes. No RH proof, novel proof architecture, or impossibility of other classifications is claimed.

## Source and frozen conjectures

The corpus mechanisms are exact multiples-coordinate reconstruction, minimal threshold witnesses (`MaynardWitnessedSubHeightPacking`), and decay versus noncontracting refinement. Their actual proofs were inspected; no unknown arithmetic bound is imported from these mechanisms. Finite-prime scalar filtering and arbitrary least-witness labels were considered but do not supply a new location constraint.

For `s`, define the actual ordinary remainder `R_s(n)=sum_(k=1..n)k^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2` and `W_p=p^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(pn))`. Put `u=conjugate(s)` and

`X_p(s)=p Re(mu(p) W_p/[u(u+1)])`,

`Y_p(s)=Re(mu(p) W_p/[u(u+1)])/[p |p^(-s)|^4]`.

Both definitions use arithmetic remainder data and apply before a zero is chosen. Neither tests whether `Re(s)=1/2`.

**Conjecture A — exact negative arithmetic balance.** At every zero with `0<Re(s)<1`,

`sum_(p>=1) X_p/p^2 = sum_(p>=1) Y_p |p^(-s)|^4`

` = -Re(1/[u(1-u)])/2 < 0`.

This should follow by dividing the proved Möbius inverse by `u(u+1)` and retaining the real part. Each profile therefore has a negative entry. Absolute convergence of the weighted sums must be proved.

**Conjecture B — arithmetic classification and directional confinement.** Label a profile by the least positive index attaining a negative global minimum; use a separate symbol `infinity` if it has no attained negative global minimum. Label each zero by the pair of its `X` and `Y` labels, retaining ties through the least-index rule. This gives disjoint exhaustive classes. The existing remainder estimate should force a finite `X` label at every strict-right zero and a finite `Y` label at every strict-left zero. Thus a zero in the `(infinity,infinity)` class must lie on the critical line. This is a proposed [BRIDGE], not closure of the finite-label classes.

**Conjecture C — arithmetic minimum principle (hard target).** At every nontrivial zero, neither profile attains a negative global minimum. This is an independently frozen candidate, not an assumption in B. A proof would settle every finite-label class by exclusion. The first attack is falsification at actual critical-line zero approximations: there `X=Y`, and the paper remainder asymptotic predicts subsequential lower boundary `-zeta(2)/(12) Re(1/(u+1))`. A finite value strictly below that boundary would reject this proposed all-zero principle. An independent high-precision check and a mathematical proof of the boundary would still be needed before calling such a rejection a theorem.

## Experiment design

Compute actual remainder profiles at the first 96 critical-line zero approximations and horizontally shifted nonzero controls, on the specified Runpod only. Use direct ordinary power sums plus an Euler–Maclaurin tail, vary the head and tail order, and independently recompute selected suspicious points using high-precision Hurwitz tails. This can reveal finite minima and modulus patterns not determined by the current symbolic bounds. Numerical values must never enter Lean proofs.

No claim about literature novelty, absence of off-line zeros, or success of C is made before those tests and proofs.

## Independent second falsification target

**Conjecture D — divisor dominance of the unnormalized remainder.** At a nontrivial zero, `|W_(pq)|<=|W_p|` for every pair of positive integers `p,q`. If true, it would supply a direction for arithmetic descent rather than merely a class label. This is an independent frozen conjecture, not a repair or weakening of C. Test every product within the already specified modulus grid, and verify any selected violation independently. The existing uniform decay bound does not imply this pointwise monotonicity.

## Dependency-closed positive results

Write `b_p=Re(mu(p) W_p/[p u(u+1)])`. The proved normalized Möbius inverse gives

`sum b_p=-Re(1/[u(1-u)])/2`.

Indeed the unit inverse before normalization is `-(u+1)/(2(1-u))`; cancelling the actual nonzero factor `u(u+1)` gives this equality. Also `Re(u(1-u))=sigma(1-sigma)+t^2>0` in the open strip, so the real reciprocal is positive and the displayed balance is strictly negative. The actual summability proof survives division by the fixed normalization and taking the real part.

For arbitrary real `a`, put `P_a(p)=p^(a+1)b_p`. Then the exact weighted sum is `sum P_a(p)/p^(a+1)=sum b_p<0`, and some `P_a(p)` is negative. The original remainder bound, after cancelling the derivative factor in its norm, proves

`|P_a(p)| <= [sum_(n>=1)n^(-2 sigma-1)]/(sigma+1) p^(a-2 sigma)`.

Therefore `P_a(p)->0` when `a<2 sigma`. Taking `a=1` gives the first profile, and `a=4 sigma-1` gives the second. A negative entry in a sequence tending to zero forces a negative global minimum: outside a finite initial segment all values are larger than the selected negative entry; minimize the finite segment. Choosing the least minimizing positive index treats ties exactly. If there is no attained negative minimum, use the separate label `infinity` (encoded by `0` in Lean). This construction proves unique exhaustive coverage without any zero assumption.

Consequences at zeros:

- A strict-right zero has a finite first label; a strict-left zero has a finite second label. The class `(infinity,infinity)` is confined to the line.
- Each positive label is squarefree, since a nonsquarefree modulus has `mu(p)=0` and profile value zero.
- On the line the two profiles are identical, so their least-minimum labels agree. This equality is automatic on the line even at nonzeros and is not evidence for an arithmetic RH producer.

## Exact obstruction exposed by the failed minimum principle

Let `S2=sum_(p>=1)1/p^2`. Comparing each summand to `2(1/p-1/(p+1))` gives `0<=S2<=2`. If the first profile is bounded below by `b`, its exact mean obeys

`b S2 <= -Re(1/[u(1-u)])/2`.

In particular every attained minimum obeys this necessary inequality. At a critical-line zero, the right side is `-1/[2(t^2+1/4)]`. If every finite value were at least `-S2/[8(t^2+9/4)]`, summing with the positive reciprocal-square weights would instead bound that mean below by

`-S2^2/[8(t^2+9/4)] >= -1/[2(t^2+9/4)]`,

which is strictly larger. Thus every critical-line zero has some positive modulus with

`X_p < -S2/[8(t^2+9/4)]`.

This finite undershoot is a Lean theorem. The existing paper asymptotic `W_p=-u zeta(2)/(12p)+O_s(p^(-3))` on the line makes the displayed threshold the lower tail boundary of `X`, because `|mu(p)|<=1`. The strict finite undershoot then forces an attained negative minimum on paper. That asymptotic-to-attainment step is not formalized in the new module. The positive survivor of C is therefore an exact arithmetic mean obstruction and mandatory finite undershoot, not a renamed vanishing conjecture.

## Remaining hard problem

The proposed use of the real balance as the missing exclusion law is now rejected on the actual source: [the phase-completeness audit](arithmetic-minimum-phase-completeness.md) proves nearby nonzero projected witnesses at every strip zero and an off-line nonzero projected witness from any strip zero. The negative weighted mean and the minimum-attainment argument below the decay exponent already follow at projected witnesses. The full complex discrepancy is retained exactly, but its required imaginary vanishing remains unproved.

The classes are independently defined and exhaustive, but their existence does not resolve the finite-label cases. A proof still needs an arithmetic relation involving the nonzero minimum values and the terms connecting distinct moduli that is incompatible with an off-line zero in each remaining class. Neither a generic minimum principle, divisor dominance, nor matching labels on already critical-line points supplies that relation. No conditional RH receiver with this missing relation as a premise has been added.

[Formal certificate](../3-formalized/arithmetic-zero-minimum-classes.md) distinguishes the checked positive results from this open source problem. [Runpod report](../2-fully-proven/computations/arithmetic-zero-minimum-classes/REPORT.md) records both failed tests and the independent checks. [Search evidence](arithmetic-zero-minimum-classes-searches.json) retains 15 capped mechanism searches; additional exact statements were inspected with `rg`. This is not an exhaustive corpus or literature novelty audit.
