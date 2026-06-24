# Finite Source Normalizations Leave Budget Recession Directions

- **ID:** finite-source-normalizations-leave-budget-recession
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Source:** `scale-invariant-source-orientation-cannot-pay-budget.md`;
  `positive-source-weights-do-not-bound-loewner-budget.md`;
  `finite-codimension-landscape-rh-nonselection.md`;
  `source-selector-repair-obligation-ledger.md`
- **Statement:** A finite list of linear source normalizations cannot imply a
  fixed Loewner budget unless every recession direction left by those
  normalizations is already nonnegative. Thus a finite-scale correction of
  Euler orientation does not reach the bridge unless it controls all
  budget-negative directions.

## Setup

Let `E` be a finite-dimensional real or complex vector space. Let `Herm(E)` be
the real vector space of Hermitian forms on `E`, and let `B>=0` be a fixed
Hermitian budget form.

Let

`L_1,...,L_m: Herm(E) -> R`

be linear source-normalization functionals, and fix constants

`c_1,...,c_m`.

Define the affine residual class

`A={R in Herm(E): L_j(R)=c_j for 1<=j<=m}`.

Its recession space is

`U={D in Herm(E): L_j(D)=0 for 1<=j<=m}`.

Assume `A` is nonempty.

## Theorem

If

`B+R>=0`

for every `R in A`, then every recession direction `D in U` is positive
semidefinite.

Equivalently, if `U` contains a form with a negative direction, then the finite
normalizations `L_j(R)=c_j` cannot imply the fixed budget inequality on the
whole affine class `A`.

## Proof

Choose any `R_0 in A`. If `D in U`, then for every real `t`,

`R_0+tD in A`,

because all `L_j(D)` vanish.

The assumed budget therefore gives

`B+R_0+tD>=0`

for every real `t`.

For any vector `v in E`,

`B[v]+R_0[v]+tD[v]>=0`

for every real `t`.

If `D[v] != 0`, then choosing `t` with the opposite sign and sufficiently large
magnitude makes the left side negative. Hence `D[v]=0` for every `v`.

Thus every unrestricted two-sided recession direction is actually zero as a
quadratic form.

For the one-sided version, if the admissible class contains `R_0+tD` only for
all `t>=0`, the same proof gives `D>=0`: a vector with `D[v]<0` violates the
budget for large positive `t`.

## Practical Form

A finite source-normalization proof must therefore identify which recession
directions remain:

- If both `D` and `-D` remain admissible, budget validity forces `D=0`.
- If only `tD` for `t>=0` remains admissible, budget validity forces `D>=0`.
- If a remaining one-sided direction is indefinite or has a negative vector,
  finite normalizations do not prove the budget.

This is the affine analogue of the scale-invariant orientation test.

## Application To The Reciprocal Seam Route

The desired bridge is

`B+R^P_d>=0`,

with `B=M_triv,d` and `R^P_d` the finite-place residual, or equivalently

`-R^P_d<=M_triv,d`.

A proposed `L_src` proof might try to repair scale-free Euler orientation by
adding finitely many source normalizations: conductor, pole normalization,
first Gamma boundary datum, finitely many Euler coefficients, finitely many
finite-part constraints, or finitely many scalar residues.

This theorem gives the audit:

1. Compute the residual directions left by those finitely many constraints.
2. If any such direction can be added to the finite-place residual and is
   negative on some polynomial square test, the fixed budget can be broken by
   scaling that direction.
3. Therefore the finite normalizations prove the budget only if their recession
   cone is already PSD in the `M_triv` budget problem.

The RH route needs an all-order source identity, an infinite-dimensional
normalization, or a source-built boundary/index theorem that removes the
budget-negative recession directions. Finitely many scale-fixing numbers do not
do this by themselves.

## Consequence For `L_src`

This card separates two uses of source data:

1. **Finite typing.** Conductor, pole, Gamma boundary, and finitely many local
   factors can identify the intended object or a narrow source class.
2. **Budget closure.** The proof of `-R^P<=M_triv` must control every remaining
   direction in the residual space.

Finite typing cannot be promoted to budget closure unless the recession audit
above is passed. Otherwise a fake residual can preserve every finite source
normalization while moving in a budget-negative direction.

## Theatre Test

For a proof using finite source normalizations:

1. List the functionals `L_j`.
2. Describe the recession space `U`.
3. Prove every one-sided recession direction in `U` is PSD, or prove there is
   no nonzero two-sided recession direction.
4. If this is missing, the finite source data have not proved `K<=I` or
   `-R^P<=M_triv`.

## Source Boundary

This is finite-dimensional convex-cone algebra. It claims no positivity for
zeta. Its role is to prevent finite source normalization from being mistaken
for all-order source domination.

## Gates

- [x] 0 -> 1 in-progress: finite-normalization loophole isolated.
- [x] 1 -> 2 fully-proven: recession-direction proof completed.
- [ ] 2 -> 3 formalized: optional finite-dimensional affine-cone theorem.

## Log

- 2026-06-24 -- Codex: created under the private source-scale audit. The card
  records that finite source normalizations can pay the fixed budget only after
  their remaining recession directions are shown nonnegative or absent.
