# Arithmetic zero classes from attained remainder minima

- **Stage:** 1-in-progress
- **Frozen objective:** independently defined, exhaustive arithmetic zero classes with a proved location constraint in every class. No classification alone counts as an RH proof.

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
