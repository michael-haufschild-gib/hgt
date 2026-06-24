# Scale-Invariant Source Orientation Cannot Pay A Fixed Budget

- **ID:** scale-invariant-source-orientation-cannot-pay-budget
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Source:** `positive-source-weights-do-not-bound-loewner-budget.md`;
  `loewner-contraction-congruence-normalization.md`;
  `source-selector-repair-obligation-ledger.md`
- **Statement:** A source-orientation predicate that is invariant under positive
  scaling cannot imply a fixed Loewner budget unless every admissible residual is
  already positive semidefinite. Therefore any Euler/Gamma source proof of
  `-R^P<=M_triv` must use exact scale data, not only orientation.

## Setup

Let `E` be a finite-dimensional real or complex vector space. Let `B>=0` be a
fixed Hermitian budget form on `E`.

Let `C` be a class of Hermitian forms on `E` such that

`R in C => t R in C`

for every `t>0`.

Think of `C` as the class selected by a source-orientation condition that sees
the direction, sign convention, or qualitative local-factor orientation of a
residual, but not its absolute scale.

## Theorem

Assume

`B+R>=0`

for every `R in C`.

Then every `R in C` is positive semidefinite.

Equivalently, if `C` contains any form `R` with a negative direction, then the
scale-invariant source condition defining `C` cannot imply the fixed budget
inequality `B+R>=0`.

## Proof

Fix `R in C`. Since `C` is closed under positive scaling, the hypothesis gives

`B+tR>=0`

for every `t>0`.

For any vector `v in E`,

`B[v]+t R[v]>=0`

for every `t>0`.

If `R[v]<0`, then the left side is negative for all sufficiently large `t`,
contradicting the hypothesis. Therefore `R[v]>=0` for every `v`, so `R>=0`.

## Loewner Form

Writing the desired budget as

`-R<=B`

is the same statement, since `B+R>=0`.

Thus a positive-scale-invariant residual class can prove

`-R<=B`

for every admissible `R` only when every admissible residual has no negative
direction at all.

## Application To The Reciprocal Seam Route

The bridge target is the scale-sensitive domination

`-R^P_d <= M_triv,d`,

or, equivalently by congruence,

`K_d=M_triv,d^(-1/2)(-R^P_d)M_triv,d^(-1/2) <= I`.

A source predicate such as "correct Euler orientation" cannot by itself prove
this inequality if it is unchanged under replacing the residual by `t R^P_d`.
The line that fails must use the actual magnitude of the Euler/local-factor
weights, a normalization theorem, multiplicativity at the correct scale,
archimedean cancellation, or a completed explicit-formula identity.

At any degree where the residual class contains a negative direction, a
scale-invariant orientation proof would also certify every amplified residual
`t R^P_d`. For large `t` that amplified residual violates the fixed
archimedean budget. Hence orientation alone is not the missing theorem.

## Consequence For `L_src`

This card generalizes the positive-weight scaling test. The obstruction is not
limited to sums of positive kernels. It applies to any source predicate that is
closed under positive rescaling of the finite-place residual.

Therefore a noncircular `L_src` theorem must state exactly which source datum
fixes scale. Acceptable answers include:

1. a formula for the exact Euler weights and a proof of the resulting budget;
2. a source normalization that bounds the residual in the `M_triv` metric;
3. a completed Euler/Gamma identity whose sign is stronger than orientation;
4. a boundary-Weyl or Schur theorem built before reciprocal zeros are read.

Without such a scale-fixing datum, the proof cannot reach rows A6--A7 of the
source-selector ledger.

## Theatre Test

For any proposed source-orientation proof of `-R^P<=M_triv`, ask:

1. If `R^P` is replaced by `t R^P`, does the source hypothesis still hold?
2. If yes, the hypothesis is scale-invariant and this theorem applies.
3. Which line of the proof uses the actual value of `t=1`?
4. If no line uses it, the argument has proved at most an orientation statement,
   not a fixed-budget domination theorem.

## Source Boundary

This is finite-dimensional cone algebra. It claims no positivity for zeta. Its
role is to prevent the phrase "source orientation" from hiding the scale data
needed by the bridge.

## Gates

- [x] 0 -> 1 in-progress: scale-invariant orientation loophole isolated.
- [x] 1 -> 2 fully-proven: scaling proof completed.
- [ ] 2 -> 3 formalized: optional finite-dimensional Hermitian cone lemma.

## Log

- 2026-06-24 -- Codex: created under the private source-transfer audit. The card
  records that source orientation without scale cannot pay the fixed
  Gamma/trivial-zero budget.

## 2026-06-24 finite-normalization affine version

`finite-source-normalizations-leave-budget-recession.md` gives the affine constraint version. If finitely many source normalizations cut the residual class to `L_j(R)=c_j`, the fixed budget can hold on that class only after every remaining recession direction is nonnegative, or zero in the two-sided case.

Thus finite scale data repair the scale-free orientation objection only if their kernel has no budget-negative direction. Otherwise amplification along the kernel breaks the budget.
