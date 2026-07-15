# Algebraically independent coefficients force formal hypertranscendence

- **ID:** `algebraically-independent-coefficient-formal-germ`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED IN LEAN] [STRUCTURAL INPUT]`
- **Statement:** A formal power series whose full coefficient family is algebraically independent
  over `ℂ` satisfies no nonzero algebraic differential equation over `ℂ[X]`.

## Theorem

Let `A` be a commutative `ℂ`-algebra and let `a : ℕ → A` be algebraically independent over `ℂ`.
For

\[
  F(X)=\sum_{k\ge0}a_kX^k,
\]

every nonzero `P : MvPolynomial (Fin (r+2)) ℂ` survives the point-and-jet substitution

\[
  P\bigl(X,F,F',\ldots,F^{(r)}\bigr)\ne0
  \quad\text{in }A\llbracket X\rrbracket.
\]

The Lean theorem is
`aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent` in
`AlgebraicallyIndependentCoefficientFormalGerm.lean`.

## Proof

Introduce the universal series

\[
  \mathcal U(X)=\sum_{k\ge0}T_kX^k
  \in \mathbf C[T_0,T_1,\ldots]\llbracket X\rrbracket.
\]

If a nonzero differential polynomial vanished on the jet of `𝒰`, every scalar specialization
`T_k ↦ c_k` would make it vanish on the arbitrary scalar series `Σ c_kX^k`.  This contradicts the
already formalized injectivity of generic jet substitution.  Hence the universal evaluation is a
nonzero power series, so one coefficient is a nonzero polynomial in the `T_k`.  Algebraic
independence of the actual coefficients makes its specialization nonzero.

The module also proves coefficient-map naturality for formal derivatives, complete jet vectors,
and differential-polynomial evaluation.

## Role in the Gamma route

For the regular Gamma factorial tail

\[
  h_n(x)=\Gamma(-n+s_nx)+x^{-1},
  \qquad s_n=(-1)^{n+1}/n!,
\]

the coefficient sequences are triangular transforms of the factorial scale and generalized
harmonic sequences.  Once their algebraic independence is proved, this theorem upgrades it
immediately to all-order differential separation.  It replaces an open-ended generator-by-generator
analysis of the reciprocal differential ideal with one coefficient-freeness criterion.

## Verification

- Direct module compilation passed.
- Individual target build passed; no full build was run.
- The headline theorem and all naturality lemmas use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- The formal lint gate passed after integration.

## Gates

- [x] 0 → 1 in-progress: exact formal statement and specialization proof isolated
- [x] 1 → 2 fully-proven: complete paper proof above, with no open dependency
- [x] 2 → 3 formalized: Lean theorem, direct compile, target build, and axiom audit passed
- [ ] 3 → 4 publication-ready: incorporate as infrastructure in the Gamma-iteration paper

## Log

- 2026-07-15 — proved universal formal-germ separation by scalar specialization and transferred it
  to every algebraically independent coefficient family.

