# HCF: exact transfer across singular Hankel gaps

Status: formalized. All four focused builds and final direct source audits pass. Fifty-four API checks and thirty-two axiom checks pass. Umbrellas wired and index refreshed. Global lint reports three unrelated umbrella-reachability errors, recorded below.

## Starting frontier and objective

The corpus now resolves normal-block inertia and the complete finite/escaping root factorization at every positive heat time. Its block Jacobi census counts signatures but does not construct the polynomial transfer between consecutive canonical regular heads. Scalar one-degree recurrences require intermediate nonsingular pivots; the new target is an exact recurrence that crosses arbitrary singular gaps, with nonzero edges and an explicit polynomial Bezout certificate.

## Conjecture loop

1. Escaping-root quadrature weights might add source information, but available positive-quadrature results require a first-contact positive finite section. They do not supply unconditional weights through arbitrary indefinite blocks. Defer this direction.
2. Conjecture: consecutive normal blocks force a polynomial three-term recurrence between their regular-head admissions. Divide the next admission by the current one. The remainder is orthogonal to all but the last row of the current regular section; the previous admission spans that one-dimensional orthogonal complement.
3. The terminal moment determines the remainder exactly: if mu_j is the first nonzero coupling after head n_j, then P_(j+2)=A_(j+1) P_(j+1)−(mu_(j+1)/mu_j) P_j. A_(j+1) is the monic Euclidean quotient of degree n_(j+2)−n_(j+1), and every edge is nonzero. No intermediate pivot enters.
4. Next conjecture: a companion sequence with Q_0=0, Q_1=1 and the same recurrence gives an exact constant Casoratian. This provides a Bezout identity and excludes common complex roots at consecutive regular heads, including singular times and indefinite sections.
5. Proved in Lean with the sharper source normalization Q_1=mu_0: the Casoratian is exactly −mu_j. Both the frame and each transfer step are units over the polynomial ring; actual-source capstones take only positive time and index. Consecutive heads have an explicit Bezout certificate, hence no common complex root.
6. New conjecture: Q_j(x)=L(P_j / (X−x)), where the quotient is polynomial division and therefore the divided difference (P_j(X)−P_j(x))/(X−x). The positive-moment corpus has this identification only along nonsingular scalar recurrences. For the new block recurrence, the product rule contributes L(P_j times the divided difference of A_j), which vanishes by extended normal-block orthogonality. At the first gap, only the initial coupling survives. This identifies the canonical companion directly with the source, without a positivity premise.
7. The source identification passed Lean. A second explicit Bezout identity proves that P_j and this source numerator Q_j are coprime at every regular head. Thus the exact transfer frame gives reduced rational approximants, not a companion unrelated to the moment source. The initial gap is handled even when total mass vanishes.

## Paper proof

Let normal blocks have heads m, n=m+d, and l=n+e, with nonzero first couplings mu_0=L(X^(n−1)P_m), mu_1=L(X^(l−1)P_n). Write P_l=A P_n+R by monic division; A is monic of degree e and deg R<n. For i<n−1, extended orthogonality of P_n kills L(X^i A P_n), so L(X^i R)=0. At i=n−1, only the leading term of A survives, giving L(X^(n−1)R)=−mu_1. Therefore R+(mu_1/mu_0)P_m has degree below n and vanishing moments in all n rows. Regularity of H_n forces it to vanish. This proves the exact recurrence.

For a cofinal chain, define beta_j=mu_(j+1)/mu_j and Q_0=0, Q_1=mu_0, with Q obeying the same recurrence as P. The companion recurrence gives W_j=P_(j+1)Q_j−Q_(j+1)P_j with W_0=−mu_0 and W_(j+1)=beta_j W_j. Hence W_j=−mu_j, a nonzero constant. Dividing the polynomial identity by that scalar gives explicit Bezout certificates both for adjacent admissions and for the source numerator/denominator. The actual HCF source has canonical cofinal normal blocks at every positive time, so every premise is discharged.

For source identification, write D_x P=P/(X−x). The exact polynomial product rule is D_x(AP)=A(x)D_xP+P D_xA. At a noninitial regular head, deg D_xA is below the extended vanishing range, so its moment contribution is zero. At the initial head P_0=1, all earlier moments vanish and the monic quotient D_xP_1 has degree n_1−1, giving L(D_xP_1)=mu_0. Induction along the block recurrence gives the claimed source formula.

## Lean artifacts

- `formal/GaloisForLFunctions/HTGeometry/MomentNormalBlockRecurrence.lean`: exact block quotient degree, nonzero coupling, three-term recurrence and Euclidean remainder.
- `formal/GaloisForLFunctions/HTGeometry/MomentNormalBlockDividedDifference.lean`: product rule for divided differences, normal-block annihilation, first-gap source normalization.
- `formal/GaloisForLFunctions/RHTower/XiGaussianHeatRegularTransfer.lean`: actual canonical recurrence, Euclidean chain, nonzero Casoratian, explicit adjacent-head Bezout certificate, polynomial unit frame and transfer.
- `formal/GaloisForLFunctions/RHTower/XiGaussianHeatRegularPade.lean`: actual source numerator identification, explicit numerator/denominator Bezout identity, reducedness and common-complex-root exclusion.

## Validation

Each of the four modules passed its focused foreground `lake --old build +Module:olean` check. Final direct checks, run sequentially from `formal/`, all exited 0 without warnings or other output:

```
lake env lean GaloisForLFunctions/HTGeometry/MomentNormalBlockRecurrence.lean
lake env lean GaloisForLFunctions/HTGeometry/MomentNormalBlockDividedDifference.lean
lake env lean GaloisForLFunctions/RHTower/XiGaussianHeatRegularTransfer.lean
lake env lean GaloisForLFunctions/RHTower/XiGaussianHeatRegularPade.lean
```

A separate `/tmp` scratch audit passed 54 API checks and printed axioms for all 32 public theorems. Every list is exactly `[propext, Classical.choice, Quot.sound]`. Signature checks confirm that the actual-source capstones take only positive time, index, and an evaluation variable where needed. Generic normal-block premises are discharged by the actual source's canonical blocks.

Both theorem-area umbrellas import the finished modules. `scripts/formal_tools.py index` passed, regenerated the three formal index documents, and refreshed the search database. `git diff --check` passed for this work. Owned scratch files and logs were removed after validation.

`scripts/formal_tools.py lint` ran and reported three unrelated RHTower modules unreachable from their umbrella: `CHMDFarFieldEnergy`, `CHMDPrimeWindowTail`, `CHMDStationaryVolumeGraph`. No new HCF module was reported; unrelated concurrent work was preserved. No full or umbrella builds, numerical experiments, new axioms, placeholders, heartbeat increases, web or novelty searches were used.

## Corpus evidence and scope

The initial quadrature and recurrence deep searches reported nonpartial results and complete inventory; the broader structure search reported partial results with complete inventory. Retrieved source-only candidates were not treated as compiled facts. Relevant Lean sources were inspected and the used APIs checked in the installed toolchain. The key leads were `MomentHankelNormalBlocks`, `MomentHankelNormalKernel`, `XiGaussianHeatBlockJacobiCensus`, and the positive-moment constructions in `FiniteOrthoNoCommonRoot`, `SecondKindMomentPolynomials`, and `SecondKindDividedDiff`.

The new structural result is an exact source-normalized polynomial transfer law for the whole cofinal regular-head chain at every positive heat time. It replaces failed scalar-pivot propagation through singular ranks and provides explicit reduced numerator/denominator data. It makes no claim that canonical head indices vary continuously with heat time.

## Remaining global obstacle

An exact nonsingular transfer law does not establish the sign of the complete prime−Gamma source or select the no-transition branch. Its role is to eliminate the singular-pivot obstruction to global canonical polynomial propagation.
