# Relative exponential-closure normal form for affine stage-two Schanuel defects

- **ID:** schanuel-affine-branch-relative-exponential-closure
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** stage-two defect character lattice + Lindemann--Weierstrass
- **Statement:** Affine stage-two counterexamples with any nonzero additive algebraic character
  are exactly failures of relative
  exponential-closure rigidity over `acl(Qbar(exp(alpha)))` for nonzero algebraic `alpha`.

## Goal

Replace the entire nonzero additive-character branch of the defect dichotomy by one exact field-theoretic
obstruction.  This distinguishes actual progress from a differential-Galois restatement and
identifies the smallest known prototype of the remaining arithmetic wall.

## Gates

- [x] 0 -> 1  in-progress: both implications isolated and hostile examples checked
- [x] 1 -> 2  fully-proven: dependency-closed proof below
- [x] 2 -> 3  formalized: saturation, primitive division, explicit Bezout completion, integral-isogeny
  invariance, normalized affine equivalence, and both directions of the global classification are
  source-checked and wired
- [ ] 3 -> 4  publication-ready: independent proof and literature audits pending

## Relative rigidity statement

For `0 != alpha in Qbar`, put

\[
 A_\alpha=\operatorname{acl}_{\mathbb C}
   \bigl(\overline{\mathbb Q}(e^\alpha)\bigr).
\]

Define `RER(alpha)` to be

\[
 z\in A_\alpha,\quad e^z\in A_\alpha
 \quad\Longrightarrow\quad z\in\mathbb Q\alpha. \tag{RER}
\]

Then a stage-two Schanuel counterexample whose additive algebraic-character lattice is nonzero
exists if and only if `(RER)` fails for some nonzero algebraic `alpha`.

## Forward implication

Let `(x_1,x_2)` be a stage-two counterexample and suppose

\[
 \Lambda_a=\{m\in\mathbb Z^2:m_1x_1+m_2x_2\in\overline{\mathbb Q}\}
\]

contains a nonzero vector.  It is saturated: if `r m` lies in `Lambda_a` for a nonzero integer `r`, then
`m dot x=(r m dot x)/r` is algebraic.  Dividing any nonzero vector by the gcd of its coordinates
therefore produces a primitive vector `m` still in `Lambda_a`.
Complete `m` to a matrix `U in GL_2(Z)` with second row `n`, and set

\[
 \alpha=m\mathbin\cdot x,\qquad z=n\mathbin\cdot x.
\]

The first number is algebraic and nonzero; zero would contradict the rational independence of
`x_1,x_2`.  The unimodular change of coordinates preserves the value field:

\[
 K=\overline{\mathbb Q}(x_1,x_2,e^{x_1},e^{x_2})
  =\overline{\mathbb Q}(\alpha,z,e^\alpha,e^z). \tag{1}
\]

Hermite--Lindemann makes `e^alpha` transcendental.  Both
`Qbar(e^alpha)` and `K` therefore have transcendence degree one, and `(1)` makes `K` finitely
generated over the former.  Thus `K/Qbar(e^alpha)` is finite, so

\[
 z,e^z\in A_\alpha.
\]

If `z=q alpha` for `q in Q`, clearing denominators and applying `U^{-1}` would give a nonzero
rational relation between `x_1,x_2`.  Therefore `z notin Q alpha`, and `(RER)` fails.

## Reverse implication

Suppose `(RER)` fails: choose nonzero algebraic `alpha` and `z notin Q alpha` with
`z,e^z in A_alpha`.  Then `alpha,z` are rationally linearly independent.  Moreover

\[
 \overline{\mathbb Q}(\alpha,z,e^\alpha,e^z)
\]

is algebraic over `Qbar(e^alpha)`, hence has transcendence degree one because
Hermite--Lindemann makes `e^alpha` transcendental.  The pair `(alpha,z)` is therefore a stage-two
Schanuel counterexample.

Its additive algebraic-character lattice is nonzero because it contains `(1,0)`.  This proves the
claimed equivalence.  The prior rank-one hypothesis was unnecessary: saturation plus primitive
division normalizes every nonzero character. **[PROVED HERE]**

## Formalization status

`RHTower/SchanuelAffineRelativeExponentialClosure.lean` now proves unconditionally:

1. two complex numbers algebraic over `Qbar(exp(alpha))` cannot be algebraically independent over
   `Qbar`;
2. any nonzero algebraic `alpha` and `z notin Q alpha` for which both `z` and `exp(z)` are algebraic
   over `Qbar(exp(alpha))` produce a literal failure of `SchanuelExtractionAt 2`.

The same module now proves the exact normalized affine equivalence: for nonzero algebraic `alpha`,
the family `alpha,z,exp(alpha),exp(z)` has no two-element algebraically independent extraction if
and only if both `z` and `exp(z)` are algebraic over `Qbar(exp(alpha))`.  This uses actual
intermediate fields and extraction data rather than a new proposition interface.  It also proves
the unconditional algebraic-vertex boundary: if `z` is algebraic and `exp(z)` is algebraic over
`Qbar(exp(alpha))`, finite Lindemann--Weierstrass forces `z in Q alpha`.  Hence every genuine
relative-rigidity obstruction has transcendental `z`.

`RHTower/SchanuelStageTwoIsogenyInvariance.lean` additionally proves that two-element extraction
failure survives every integral isogeny transform.  Its proof selects `x_0` or `exp(x_0)` as an
unconditional transcendental anchor, makes every original generator algebraic over the resulting
one-generator field, and transports algebraicity through integral additive coordinates and torus
monomials.  No determinant hypothesis is needed for failure preservation; nonzero determinant is
used only to preserve rational linear independence.

`RHTower/SchanuelAffineCharacterNormalForm.lean` proves saturation of the concrete additive
character subgroup, primitive division, explicit Bezout completion to a determinant-one integral
matrix, the forward normal form, and the global iff between existence of a nonzero-character
stage-two failure and existence of a relative exponential-edge obstruction.  No rank-one
hypothesis or proposition wrapper remains.

## Failed conjecture and pivot

The first conjecture was that the affine branch might succumb directly to
Lindemann--Weierstrass after an integral coordinate change.  This is false: the transformed second
coordinate is generally transcendental.  At `alpha=1`, choosing `z=e` turns `(RER)` into the open
algebraic independence of `e` and `e^e`.

The exact positive survivor is the equivalence above.  It shows that the obstruction is not a
missing differential calculation: it is the possibility that the algebraically closed
one-variable field `A_alpha` contains a new exponential edge `z -> e^z` not generated by the
rational edge lattice of `alpha -> e^alpha`.

## Big-picture reinterpretation

Earlier coefficient descent, trace/norm, isogeny, and Picard--Vessiot attacks all forgot the same
structure: a selected exponential edge inside an algebraic closure.  Their failures are shadows of
one higher principle:

> **Relative exponential-edge rigidity.**  Algebraic closure of a one-edge exponential field
> should not acquire a second rationally independent exponential edge.

For algebraic starting vertices this principle is exactly `(RER)`.  It is strong enough to kill
the affine branch and weak enough not to disguise full Schanuel as a general-purpose axiom.

## Hostile audit

- This theorem does not prove `(RER)`.
- The prototype `alpha=1,z=e` confirms Schanuel-level hardness rather than giving evidence of a
  shortcut.
- Saturation is essential; a nonzero subgroup vector need not otherwise divide to a primitive
  vector inside the subgroup.
- Equality of transcendence degrees gives algebraicity only because `(1)` is finitely generated.
- Targeted literature search found Kirby's exponential-algebraic-closure pregeometry and generic
  powers results, but no exact relative-closure equivalence for the affine stage-two branch.  Treat
  this as a new internal reduction; external novelty unconfirmed and no priority claimed.

## New open core

The nonzero additive-character branch is now exactly `(RER)`.  The complementary stage-two branch
has zero additive algebraic-character lattice.  Its next exact split is by the multiplicative
algebraic-character lattice; a nonzero multiplicative character should admit the dual normal form
over `acl(Qbar(alpha))`, leaving a bi-character-free core.  Any proof of `(RER)` using only
derivations of `A_alpha` cannot work: both `z` and `e^z` are algebraic over the same transcendence
generator, so their Kähler module is already rank one and reproduces the defect-slope wall.

## Log

- 2026-08-14 -- affine rank-one branch converted into exact relative exponential-closure
  rigidity; direct Lindemann continuation killed by the `e,e^e` prototype.
- 2026-08-14 -- rank-one hypothesis removed: every nonzero additive character divides to a
  primitive character and yields the same exact obstruction; global iff formalized in Lean.
