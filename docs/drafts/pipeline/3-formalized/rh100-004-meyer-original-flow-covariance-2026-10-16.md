# Contribution 004: finite causal synthesis follows the original Meyer flow

Status: dependency-closed paper proof and Lean formalization complete, 2026-10-16.
One structural contribution, bringing the goal ledger to **4 / 100**.

## Obstacle and exact result

Generator invariance and matching Xi jets did not establish invariance under
the original dilation flow on literal Meyer cohomology: an orbit discrepancy
could still lie in the invisible sector. Transporting packet dynamics through
a chosen section would not identify that dynamics with the original flow.

Write Q for literal strong-log Poisson cohomology, U(c) for its original
dilation flow, E_S for its full finite Xi-jet map, J_S for its causal section,
P_S = J_S E_S, and F_S(c) for the existing confluent packet flow. For every
finite Xi divisor set S, real c, u in Q, and complex-linear packet operator B,
the new unconditional theorems prove

```
P_S U(c) u = U(c) P_S u,
U(c) J_S a = J_S F_S(c) a,
U(c) Lift_S(B) U(-c) u = Lift_S(F_S(c) B F_S(-c)) u.
```

These are equalities of actual cohomology classes. They remove invisible
dynamical mixing along every finite causal sector and permit arbitrary finite
packet operators to be used with their exact original-flow conjugation law.
No analytic or arithmetic premise is added to these final statements.

## Corpus inputs and conjecture loop

Documented deep searches covered original Meyer covariance, Euler division,
spectral synthesis, and weighted translation differentiation. Search results
were leads; relevant statements and proofs were inspected in Lean and checked
against this toolchain. No web, novelty search, old reports, or numerical
experiments were used.

The first conjecture was original-flow covariance on finite causal chains.
Generator invariance alone left the orbit-uniqueness gap. Equality of observed
jets alone also left an invisible discrepancy. Neither inference was accepted
as a proof. The successful refinement combines:

- `HTGeometry/SchwartzTranslation.lean`: two-sided directional Taylor control
  and translation difference-quotient convergence.
- `DeningerMeyerStrongLogSourceEquivalence`, `DeningerMeyerStrongLogFrechet`,
  and `DeningerMeyerStrongLogOperatorContinuity`: contribution 003's actual
  source equivalence, closed Poisson range, separated natural quotient, and
  continuous finite causal operators.
- `DeningerMeyerXiCausalChains`, `DeningerMeyerFiniteXiCausalSplitting`, and
  `DeningerMeyerFiniteXiJetPacket`: actual causal Jordan chains, synthesis,
  full jet retraction, and the existing packet-flow identity.
- `HTGeometry/RealExponentialPolynomial.lean`: scalar linear ODE uniqueness.

The Schwartz analytic mechanism and literal Meyer algebraic construction meet
through the separated continuous dual; no invisible-kernel vanishing is used.

## Dependency-closed paper proof

1. Extend the corpus two-sided Schwartz Taylor argument to every exponential
   derivative gauge. For shifts of size at most one the weight ratio is at
   most exp(|k|). Each gauge of the difference between the original-flow slope
   and the actual generator tends to zero. Thus the slopes converge in the
   full natural source topology, not just pointwise.
2. Transport local convexity through the continuous source equivalence and
   then through the actual quotient map. Closed Poisson range makes Q
   Hausdorff. Complex Hahn–Banach supplies a separating continuous dual.
3. Compose strong slope convergence with a continuous functional and use the
   original flow law. For every continuous complex functional ell and u in Q,
   the derivative of ell(U(t)u) is ell(U(t)Au), where A is the actual generator.
4. Fix a causal chain u_k at rho in S. It satisfies u_0 = 0 and
   A u_(k+1) = rho u_(k+1) + u_k. For each ell, set
   f_k(t) = ell((P_S-id)U(t)u_k). Induct on k. The preceding residual is zero,
   so f_(k+1)' = rho f_(k+1). Its initial value is zero because P_S fixes the
   causal chain. Scalar ODE uniqueness forces f_(k+1) = 0.
5. Separation by all continuous functionals turns this scalar conclusion
   into (P_S-id)U(t)u_k = 0 in Q. Finite linear synthesis proves invariance
   of the full finite causal range under the original flow.
6. The existing identity E_S U(c) = F_S(c) E_S and E_S P_S = E_S give
   P_S U(c) P_S = P_S U(c). Range invariance gives
   P_S U(c) P_S = U(c) P_S. Hence P_S U(c) = U(c) P_S.
7. Apply this to J_S and use E_S J_S = id to obtain original-flow covariance
   of the section. Substitution into Lift_S(B) = J_S B E_S gives the stated
   conjugation identity for arbitrary B.

## Formalization and audits

New leaves:

- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerStrongLogFlowDerivative.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerWeakFlow.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerOriginalFlowCovariance.lean`

Each passed a foreground direct audit from `formal` using
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<module>.olean GaloisForLFunctions/RHTower/<module>.lean`.
All three are wired individually into `RHTower.lean`; no full or umbrella
build was run. A separate `/tmp` audit checked all 16 public declarations:
only `propext`, `Classical.choice`, and `Quot.sound` occur. Formal lint passed
with existing large-file warnings. No proof holes, new axioms, computations,
or heartbeat increases. Owned scratch files are removed before handoff.

## Exact boundary and next conjectures

This establishes finite causal covariance for the original flow. It does not
establish a continuous global arithmetic complement, infinite-packet
synthesis, vanishing of the full invisible sector, finiteness of the whole
homogeneous kernel, a positive Hodge form, or RH. Polynomial-module injectivity
still must not be mistaken for injectivity of polynomial multiplication.

Next investigations must target a distinct obstruction. Possible corpus-led
questions include extension beyond finite causal sectors, intrinsic source
kernel rigidity, and continuity of a global arithmetic splitting. Routine
conjugation corollaries of this result are not another contribution.
