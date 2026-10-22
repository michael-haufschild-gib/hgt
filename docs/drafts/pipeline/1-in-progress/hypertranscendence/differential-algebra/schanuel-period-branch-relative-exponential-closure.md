# Relative exponential-closure normal form for multiplicative stage-two Schanuel defects

- **ID:** schanuel-period-branch-relative-exponential-closure
- **Stage:** 3-formalized (card move pending final targeted module audit)
- **Type:** THEOREM (paper and Lean)
- **Source:** stage-two defect character lattices + Hermite--Lindemann + integral isogeny invariance
- **Statement:** Stage-two counterexamples with any nonzero multiplicative algebraic character are
  exactly failures of relative exponential-closure rigidity over `acl(Qbar(alpha))` at a nonzero
  logarithm `alpha` of an algebraic number.

## Goal

Classify the branch complementary to the already formalized nonzero additive-character normal
form.  This is the exact multiplicative dual, not a Kähler or transcendence-degree proxy.

## Gates

- [x] 0 -> 1  in-progress: exact statement and dependency-closed paper proof below
- [x] 1 -> 2  fully-proven: both implications and saturation proof closed below
- [x] 2 -> 3  formalized: exact local equivalence, character saturation, primitive normalization,
  forward normal form, and global iff are source-checked and wired
- [ ] 3 -> 4  publication-ready: independent proof and literature audits pending

## Relative rigidity statement

For `alpha != 0` with `exp(alpha)` algebraic, put

\[
 B_\alpha=\operatorname{acl}_{\mathbb C}
   \bigl(\overline{\mathbb Q}(\alpha)\bigr).
\]

Define `PRER(alpha)` by

\[
 z\in B_\alpha,\quad e^z\in B_\alpha
 \quad\Longrightarrow\quad z\in\mathbb Q\alpha. \tag{PRER}
\]

For a rationally independent pair `x=(x_1,x_2)`, define its multiplicative algebraic-character
lattice

\[
 \Lambda_m(x)=\{m\in\mathbb Z^2:e^{m_1x_1+m_2x_2}\in\overline{\mathbb Q}\}.
\]

Then a stage-two Schanuel counterexample with `Lambda_m(x) != 0` exists if and only if `(PRER)`
fails for some `alpha`.

## Forward implication

Let `x` be a stage-two extraction failure and choose nonzero `m in Lambda_m(x)`.  The lattice is
saturated.  Indeed, if `r m` lies in it for `r != 0`, then

\[
 \exp(rm\cdot x)=\exp(m\cdot x)^r
\]

is algebraic.  A nonzero integral power of a nonzero complex number is algebraic if and only if the
number itself is algebraic: for positive exponent this follows from `X^n-y^n`; for negative
exponent apply the positive case to the inverse.  Hence `m` divides inside the lattice by the gcd
of its coordinates, producing a primitive `p`.

Complete `p` by Bezout to a determinant-one matrix `U` and put

\[
 (\alpha,z)=Ux.
\]

Integral-isogeny invariance preserves extraction failure, and determinant one preserves rational
linear independence.  Thus `alpha != 0`, `z notin Q alpha`, and `exp(alpha)` is algebraic.
Hermite--Lindemann forces `alpha` to be transcendental over `Qbar`.

If `z` were transcendental over `Qbar(alpha)`, the pair `(alpha,z)` would be algebraically
independent over `Qbar`, contradicting extraction failure.  The identical argument with `exp(z)`
would extract `(alpha,exp(z))`.  Therefore both `z` and `exp(z)` are algebraic over
`Qbar(alpha)`, so `(PRER)` fails.

## Reverse implication

Suppose `(PRER)` fails.  Choose `alpha,z` with `alpha != 0`, `exp(alpha)` algebraic,
`z notin Q alpha`, and `z,exp(z)` algebraic over `Qbar(alpha)`.  The pair `(alpha,z)` is rationally
linearly independent.  Hermite--Lindemann makes `alpha` transcendental over `Qbar`, while
`exp(alpha)` is already algebraic over `Qbar`; hence every member of

\[
 \{\alpha,z,e^\alpha,e^z\}
\]

is algebraic over the one-generator field `Qbar(alpha)`.  No two of them can be algebraically
independent over `Qbar`, so this is a stage-two extraction failure.  Its multiplicative character
lattice is nonzero because `(1,0)` belongs to it. **[PROVED HERE]**

## Hostile audit

- This theorem does not prove `(PRER)`.
- It uses concrete fields, elements, extraction data, and character lattices; no proposition
  interface hides the open arithmetic input.
- Existing period-shift Kähler theorems do not imply this classification: they control differential
  rank after adjoining an independent period, whereas this theorem classifies algebraicity inside
  one actual relative algebraic closure.
- Saturation requires the root-of-algebraic-power lemma; treating it as automatic would leave a
  real gap for nonprimitive characters.
- The theorem removes the whole nonzero multiplicative-character branch once `(PRER)` is proved,
  leaving exactly the bi-character-free branch `Lambda_a=Lambda_m=0`.

## Big-picture reinterpretation

Additive and multiplicative character lattices are the two boundary divisors of the exponential
graph.  A stage-two defect meeting either divisor normalizes to a one-edge relative algebraic
closure.  All genuinely interior defects avoid both divisors.  Thus the obstruction is not a bad
choice of coordinates but a three-stratum law:

1. nonzero additive character: relative edge over `Qbar(exp(alpha))`;
2. nonzero multiplicative character: relative edge over `Qbar(alpha)`;
3. no characters of either kind: an interior bi-character-free exponential curve.

The prior failed trace, norm, isogeny, and Kähler attacks are shadows of forgetting this boundary
stratification.

## Formalization status

`RHTower/SchanuelPeriodCharacterNormalForm.lean` defines the actual field `Qbar(alpha)`, proves
that a nonzero logarithm of an algebraic number is transcendental over `Qbar`, proves the exact
local extraction equivalence, proves algebraicity descends from every nonzero integral power,
constructs and saturates the concrete multiplicative character subgroup, divides characters to
primitive ones, applies the explicit determinant-one normalizing matrix, and proves both
directions of the global classification.  The module passes direct `lake env lean` source checking
and is wired into `RHTower.lean`.

## New open core

Prove `(RER)`, prove `(PRER)`, and classify the remaining
bi-character-free stratum by an invariant that uses the selected exponential graph rather than only
its ambient transcendence-degree-one field.

## Log

- 2026-08-14 -- exact multiplicative dual of affine normal form isolated; paper proof closed.
- 2026-08-14 -- full theorem formalized in Lean; whole nonzero multiplicative-character branch
  reduced exactly to `(PRER)`.
