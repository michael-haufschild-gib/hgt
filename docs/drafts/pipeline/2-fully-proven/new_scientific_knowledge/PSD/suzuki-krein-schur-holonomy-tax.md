# Suzuki Krein completion has an exact Schur holonomy tax

- **ID:** `suzuki-krein-schur-holonomy-tax`
- **Stage:** 2 — fully proved on paper
- **Type:** exact finite-negative-block reduction / conjecture repair
- **Status:** `[PROVED] [UNCONDITIONAL] [FRONTIER-SHARPENING]`
- **Parent:** `suzuki-affine-resolvent-krein-defect.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SuzukiAffineResolventKreinDefect.lean`

## 1. Problem

The affine resolvent theorem gives local signed form

```text
Q_K=Q_+-Q_-,
```

with explicit positive debt on every negative restricted-Weil coordinate.  Saying “completion
cancels `Q_-`” is still incomplete if full-frequency Neumann projective holonomy couples positive
and negative channels.  Off-diagonal coupling changes positivity threshold.

## 2. Exact two-channel theorem `[PROVED]`

Let

```text
a>0                positive-channel weight,
n>0                negative Krein debt,
c                   direct completion on negative channel,
b                   projective/holonomy coupling.
```

The complete real two-channel quadratic form is

```text
Q(x,y)=a x^2+2bxy+(c-n)y^2.                             (1)
```

Completing square gives exact identity

```text
Q(x,y)
=a(x+(b/a)y)^2+[c-n-b^2/a]y^2.                         (2)
```

Therefore

```text
Q>=0 on R^2  <=>  c>=n+b^2/a.                          (3)
```

Term `b^2/a` is **Schur holonomy tax**.  If `b!=0`, it is strictly positive.  Direct completion
`c=n` which exactly pays diagonal debt still fails because determinant is `-b^2<0`.

This is not estimate.  It is sharp equality and one-vector falsifier: set `y=1`, `x=-b/a`.

## 3. Finite-negative-block theorem `[PROVED]`

Let local Krein space split `H=H_+ direct_sum H_-`, with

```text
S=diag(P,-N),     P>0, N>0,
C=[[C_++,C_+-],[C_-+,C_--]]
```

a self-adjoint source completion.  Assuming `P+C_++>0`, standard congruence by block Gaussian
elimination gives

```text
S+C>=0
<=>
C_---N-C_-+(P+C_++)^(-1)C_+- >=0.                      (4)
```

### Proof

Put `A=P+C_++`, `B=C_+-`, `D=C_---N`.  Congruence

```text
[[1,-A^(-1)B],[0,1]]^*
[[A,B],[B^*,D]]
[[1,-A^(-1)B],[0,1]]
=diag(A,D-B^*A^(-1)B)
```

is invertible and preserves inertia.  Since `A>0`, positivity is equivalent to second block
being nonnegative, proving `(4)`.  Equation `(3)` is one-dimensional specialization.

For Suzuki's lower-bounded discrete restricted-Weil operator, negative spectral subspace at fixed
aperture is finite-dimensional.  Thus once a common minimal realization of actual jump kernel is
constructed, infinite Pick problem reduces to one finite Schur complement on that negative block.
Positive spectral complement is automatic from signed-resolvent theorem.

## 4. Revised source frontier

`SUZUKI-GLOBAL-LOCAL-KREIN-WELD` must prove stronger exact inequality

```text
C_---N >= C_-+(P+C_++)^(-1)C_+-.                       (5)
```

Interpretation:

- `N`: explicit affine-resolvent negative debt;
- `C_--`: diagonal reflected prime--Gamma/Neumann completion;
- `C_+-`: full-frequency projective holonomy coupling;
- right side of `(5)`: unavoidable cross-channel tax.

Holonomy cannot be declared “compensating” from its presence alone.  If it enters only
off-diagonally, it makes required diagonal completion larger.

**This is formal.**  `suzukiSchurTax_posSemidef` shows the Schur term is a congruence of the inverted
positive block, hence positive semidefinite whatever the coupling is, and
`suzukiKreinDiagonal_dominates_debt` shows that `(5)` therefore forces the diagonal block to dominate
the bare negative debt already: the cross-channel cost is additional, never a discount.  So no
off-diagonal completion can reduce the diagonal requirement.  Successful proof must exhibit a
source square whose diagonal term pays both `N` and Schur tax.

## 5. New conjecture

### `SUZUKI-FINITE-NEGATIVE-BLOCK-WELD` `[CONJECTURE]`

For one curvature-selected aperture and negative shift pair, actual coupled Euler--Gamma/Neumann
jump kernel admits common-gauge Pontryagin realization with negative subspace equal to negative
spectral subspace of restricted-Weil operator, and source blocks satisfy `(5)`.

Because negative block is finite, conjecture is decidable by exact finite Evans determinant.  One
negative principal minor falsifies it.

**The falsification criterion is formal.**  `principalMinor_nonneg`: principal submatrices of a
positive semidefinite matrix are positive semidefinite, so every principal minor is nonnegative.
`not_posSemidef_of_principalMinor_neg` and
`not_schurComplement_posSemidef_of_principalMinor_neg`: hence one negative principal minor of the
Schur complement refutes `(5)`, and so the conjecture, without examining the rest of the source.
That is the decision procedure this section proposes, available as a theorem rather than as a
described method.  If proved, block congruence gives full jump Pick positivity;
existing pole tomography gives RH.

## 6. Scientific gain

- repairs overly weak “pay negative diagonal debt” language;
- identifies exact role of projective holonomy as cross-channel cost;
- converts full-frequency positivity to finite negative-block Schur complement;
- supplies minimal finite determinant target for prime--Gamma source calculation.

No claim is made that `(5)` currently holds for actual source.  That is exact RH-bearing frontier.

## 7. Formal status

Lean proves scalar completed-square identity `(2)`, equivalence `(3)`, strict positivity of
nonzero coupling tax, and specialization to exact negative-node affine-resolvent debt.  General
finite-dimensional block congruence is **also formal** — see the log entry immediately below, which
closes it in `RHTower/SuzukiKreinSchurBlockCongruence.lean`, together with the automatic positive
spectral complement `suzukiPositiveBlock_posDef` of §3.

### Lean progress — general finite block congruence formalized

The §7 gap "general finite-dimensional block congruence remains paper-proved" is now closed
unconditionally in `formal/GaloisForLFunctions/RHTower/SuzukiKreinSchurBlockCongruence.lean`:

- `suzukiSignedKreinMetric P N`, `suzukiKreinCompletion Cpp Cpm Cmm` — the signed Krein metric
  `S = diag(P,−N)` and self-adjoint source completion `C = [[C₊₊,C₊₋],[C₊₋ᴴ,C₋₋]]`.
- `suzukiSignedKreinMetric_add_completion` — the completed weld is the block matrix
  `[[P+C₊₊, C₊₋],[C₊₋ᴴ, C₋₋−N]]`.
- `suzukiKreinWeld_posSemidef_iff_schurComplement` — **equation (4)**: with `A = P+C₊₊` positive
  definite, `(S+C) ⪰ 0 ↔ (C₋₋−N) − C₊₋ᴴ(P+C₊₊)⁻¹C₊₋ ⪰ 0`, the block Gaussian congruence
  (via mathlib `Matrix.PosDef.fromBlocks₁₁`).
- `suzukiKreinScalarSchurComplement_posSemidef_iff` — the `1×1` Schur complement is PSD iff
  `n + b²/a ≤ c` (single entry `c−n−b²/a`).
- `suzukiKreinScalarWeld_posSemidef_iff_twoChannelForm` — **equation (3) as the `Fin 1`
  specialization of (4)**: the scalar two-channel form `Q(x,y) = a x² + 2bxy + (c−n)y²` is
  nonnegative for all `x,y` iff the `1×1` block weld is PSD, both equal to the scalar Schur
  threshold, routed through the general congruence and the existing scalar law
  `suzukiTwoChannelKreinCompletionForm_nonneg_iff_schurDebt`.

Section 3's closing sentence "positive spectral complement is automatic from signed-resolvent
theorem" is formal too, as `suzukiPositiveBlock_posDef`: a positive definite local metric plus a
positive semidefinite completion is positive definite, so the congruence's hypothesis
`P + C_++ > 0` is free for a positive completion.  That is exactly what leaves only the negative
block to analyse, and hence what reduces the infinite Pick problem to one finite Schur complement.
On the diagonal side the same fact is `suzukiDiagonalKreinForm_posPart_nonneg` on the parent card.

All five depend only on `[propext, Classical.choice, Quot.sound]`; `lake build` of the RHTower
umbrella is green; `formal lint passed`.  The RH-bearing inequality (5) and the analytic
Pontryagin-realization conjecture `SUZUKI-FINITE-NEGATIVE-BLOCK-WELD` remain the open frontier.

- 2026-08-01 — section 3's "positive spectral complement is automatic" formalized
  (`suzukiPositiveBlock_posDef`).  The block congruence `(4)` carries `P + C_++ > 0` as a hypothesis;
  for a positive completion that hypothesis is free, since a positive definite matrix plus a positive
  semidefinite one is positive definite.  This is the step that makes the reduction to a *single*
  finite Schur complement legitimate — without it, the positive block would need its own analysis and
  the "one finite Schur complement" claim would not follow.  One new declaration, targeted build
  green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — section 4's interpretation formalized.  `suzukiSchurTax_posSemidef`: the Schur term of
  `(4)` is a congruence of the inverted positive block, hence positive semidefinite for *any*
  coupling.  `suzukiKreinDiagonal_dominates_debt`: consequently `(5)` already forces the diagonal
  completion to dominate the bare negative debt, so the cross-channel tax is paid on top and is never
  a discount.  This is the precise content of "holonomy cannot be declared compensating from its
  presence alone" — its off-diagonal presence strictly cannot help, which is what the card's repair
  of the earlier "pay negative diagonal debt" language asserts.  Two new declarations, targeted build
  green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — section 5's falsification criterion formalized.  `principalMinor_nonneg` (principal
  submatrices of a PSD matrix are PSD, so their determinants are nonnegative) and
  `not_schurComplement_posSemidef_of_principalMinor_neg` make "one negative principal minor falsifies
  it" a theorem rather than a described method: a single exhibited minor refutes `(5)` and hence
  `SUZUKI-FINITE-NEGATIVE-BLOCK-WELD`, with no further examination of the source.  A card that states
  a decision procedure should carry it as a proved implication, since that is what a future
  refutation would be checked against.  Three new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
