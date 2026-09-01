# Literal-source admissible rank-gauge obstruction

- **ID:** ULF-LSARGO-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `LiteralSourceReflectionRankGaugeLinearization` +
  `BilateralPrimeAngleModeration`
- **Statement:** The canonical gauge that trivializes actual literal-source rank transport is the
  corpus's bilateral sewing eigenhistory; it is algebraically available for every nonzero
  character but polynomially moderate exactly when the character is unitary.

## Big-picture law and RH closure

Universal formation geometry cannot use ordinary algebraic gauge equivalence.  That quotient is too
coarse: the source reflection cocycle is an exact coboundary for every nonzero character.  The
surviving datum is whether its primitive belongs to the source's admissible class.  Here admissible
means polynomial two-sided growth, equivalently the coefficient growth of a distribution on the
compact prime-angle observer.

Thus the candidate higher law is **relative exactness**: a formation cocycle may be algebraically
exact but non-exact in the admissible gauge category.  The critical line is the boundary where its
canonical primitive first exists on both source directions.

Exact RH closure: let `rho` be any nontrivial zero and `p >= 2`.  If literal pre-divisor formation
proves that the canonical rank primitive for the half-density character
`lambda_p(rho)=p^(1/2-rho)` is source-admissible, then this theorem gives
`|lambda_p(rho)|=1`, hence `Re rho=1/2`.  The missing RH step is therefore not another abstract
selector: it is a pre-divisor theorem forcing admissibility of this already determined primitive.

## Corpus audit

- `rankAnchoredComplexCharacterEdge_eq` proves `(z^-1)^m e_m(z)=1-z` on nonnegative ranks.
- `reflectionBlockMultiplier_rankGaugeConjugation` proves that this gauge removes the raw quadratic
  reflection exponent, leaving the residual character `-z^-1`.
- `bilateral_shift_eigen_eq_zero_of_norm_ne_one` proves that a nonzero moderate bilateral shift
  eigenfamily must have unitary eigencharacter.
- `bilateralEigenFamily lam e=lam^(-e)` and
  `sourceHorizontalBilateralSecondJetHardyDescent_ghost_moderate_iff` already realize and classify
  the same abstract eigenhistory in the second-jet Hardy source organ.
- `norm_bilateralHalfDensityCharacter_eq_one_iff` identifies unitarity of `p^(1/2-s)` with
  `Re s=1/2`.
- `BilateralPrimeAnglePacketSewing` proves the two Hardy halves are separately moderate off the line
  but the sewn bilateral family is moderate only on the line.
- Corpus search found no theorem identifying the **actual marked depth-12 source rank gauge** with
  that bilateral eigenhistory, no cross-organ trivialization square, and no statement that the
  reflection coboundary is algebraically trivial but obstructed in the admissible gauge category.

## Definitions

For `z != 0` and bilateral rank `e in Z`, identify the literal-source rank primitive with the
existing sewing eigenhistory

`g_z(e)=z^(-e)`.

Call the literal-source reflection gauge **admissible** when `g_z` is polynomially moderate:
there exist `C >= 0` and `m in N` such that

`|g_z(e)| <= C(1+|e|)^m`

for every `e in Z`.

For natural `m`, `g_z(m)=(z^-1)^m`, so this is exactly the gauge already forced by rank
normalization of the marked source edge, not a newly chosen selector or a duplicate family.

## Theorem

Let `z != 0`.

1. **Bilateral sewing law:** `g_z(e-1)=z g_z(e)` for every `e in Z`; moreover `g_z` is nonzero.
2. **Agreement with literal rank gauge:** for `m in N`, `g_z(m)=(z^-1)^m`.
3. **Actual-source trivialization:** for every prime `p` and source grade `j`,
   `g_z(12+j) A_(p,j)(z)=1-z`, where `A_(p,j)` is the actual normalized depth-12 marked
   source execution.
4. **Reflection lift:** `g_(z^-1)(e)=g_z(-e)`; functional-equation inversion becomes reversal of
   bilateral source rank.
5. **Admissible obstruction:** `g_z` is polynomially moderate if and only if `|z|=1`.
6. **Half-density specialization:** for `p >= 2`, `g_(lambda_p(s))` is polynomially moderate if
   and only if `Re s=1/2`.

Consequently the source reflection cocycle is algebraically trivial for every nonzero `z`, while
its canonical trivialization exists in the moderate source category exactly on the unitary locus.

## Proof

Integer powers give

`g_z(e-1)=z^(-(e-1))=z^(1-e)=z z^(-e)=z g_z(e)`.

Since `g_z(0)=1`, the family is nonzero.  For natural `m`, the integer-power identity
`z^(-m)=(z^-1)^m` proves item 2.  Substituting item 2 into the already proved actual rank
normalization

`(z^-1)^(12+j) A_(p,j)(z)=1-z`

proves item 3.

For the reflection lift,

`g_(z^-1)(e)=(z^-1)^(-e)=z^e=g_z(-e)`,

using `z != 0`.  Thus character inversion does not create a second primitive; it reverses the
same bilateral history.

Assume `g_z` is moderate.  It is a nonzero solution of the bilateral shift eigen-equation with
eigencharacter `z`.  The bilateral moderation vanishing theorem says that if `|z| != 1`, every
moderate solution is zero, contradiction.  Hence `|z|=1`.

Conversely, if `|z|=1`, then for every integer `e`,

`|g_z(e)|=|z|^(-e)=1`.

The moderation bound holds with `C=1` and degree `m=0`.  This proves item 5.  The half-density norm
identity

`|lambda_p(s)|=p^(1/2-Re s)`

and `p>1` give `|lambda_p(s)|=1` iff `Re s=1/2`, proving item 6. `[PROVED HERE]`

## Hostile assessment

- **Not RH:** admissibility of the primitive at an actual zero has not been derived from literal
  source formation.
- **Killed:** ordinary algebraic cohomology as the invariant; it sees zero class at every nonzero
  character.
- **Positive survivor:** obstruction lives in the mismatch between algebraic and admissible gauge
  categories.  New content is the exact identification of actual marked-source normalization with
  the already classified bilateral sewing history, including reflection as rank reversal.
- **Required producer:** construct source bornology/topology before divisor input and prove that its
  formation law places the canonical primitive `g_z` in the moderate dual.  Defining admissibility
  only after seeing `z` would be circular.

## Gates

- [x] 0 -> 1: big-picture law, corpus audit, and exact RH closure stated
- [x] 1 -> 2: dependency-closed proof; `[PROVED HERE]`
- [ ] 2 -> 3: Lean formalization
- [ ] 3 -> 4: publication-ready extraction

## Log

- 2026-09-01 — algebraic-versus-admissible gauge obstruction isolated and paper proof closed.
