# Hurwitz nonrational full partition differential-matroid law

- **ID:** `hurwitz-nonrational-full-partition-differential-matroid-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scientific status:** `[CONJECTURE] [90/100 CANDIDATE]`
- **Statement:** For arbitrary finite nonrational exponent families, the differential matroid of
  the analytically continued Hurwitz functions is exactly the partition matroid modulo integer
  translation, without rational independence between distinct classes.

## Goal

Let `s : I → ℂ` be finite and assume every `s i` is irrational.  Then prove

\[
  \bigl(a\mapsto\zeta(s_j,a)\bigr)_{j\in J}
  \text{ is differentially algebraically independent over }\mathbb C(a)
  \quad\Longleftrightarrow\quad
  s_i-s_j\notin\mathbb Z\ \ (i\ne j\text{ in }J).
\]

This would remove the final augmented-rational-independence hypothesis and classify all rational
resonances between nonrational exponent classes.  The already formalized theorem
`continued_hurwitz_integerTranslation_differentialMatroid_law` is the collapse case in which one
representative from each integer class is augmented-rationally independent.

## Gates

- [x] 0 → 1 in-progress: precise claim, boundary identified, proof mechanism candidate
- [ ] 1 → 2 fully-proven: degreewise multi-column separation and polarization proved
- [ ] 2 → 3 formalized: one unconditional Lean theorem, exact build and axiom audit clean
- [ ] 3 → 4 publication-ready: independent novelty audit supports the 90/100 target

## Positive mechanism

The one-column proof required the whole monomial map `α ↦ q^α` to be injective.  A finite-degree
relation contains more structure.  Let `H_d` be its top homogeneous part and choose `d` distinct
branch columns.  After substituting the independently continued branch coefficients, inspect the
component that uses every chosen column nontrivially.  Since its total degree is `d`, each chosen
column occurs exactly once.  Therefore that component sees only the degree-zero character `1` and
the degree-one characters `q_j`; no higher monomial resonance can enter it.

If `q_j ≠ 1` and the `q_j` are pairwise distinct, repeated one-variable Vandermonde extraction in
the loop counts separates the exponent label at every chosen column.  The extracted coefficient is
the polarization of `H_d` evaluated on the branch contribution vectors

\[
  v_{j,n}= (a+n)^{-s_j}\bigl(1,(a+n)^{-1},\ldots,(a+n)^{-N}\bigr)
\]

in the `j`th ladder block.  For fixed `j`, any `N+1` distinct branch points give a Vandermonde basis
of that block.  Infinitely many branch points allow disjoint bases for all `d` polarization slots.
Hence the polarization of `H_d` vanishes on a basis in every slot, so `H_d=0`.  Descending on total
degree proves that the original relation is zero.

Thus full monomial-character separation is replaced by the sharp degree-one condition

\[
  1,q_1,\ldots,q_r\ \text{pairwise distinct},
\]

equivalently: every exponent is nonintegral and distinct exponents are incongruent modulo `ℤ`.

## Verification obligations

1. Define and isolate the top homogeneous part of a multivariable relation after branch-column
   substitution.
2. Prove the degree-support lemma: total degree `d` plus nonzero use of `d` selected columns forces
   degree exactly one in each column.
3. Apply the existing one-variable power-sum Vandermonde theorem to separate `1,q_1,…,q_r` in each
   selected column without assuming separation of higher monomials.
4. Identify the extracted coefficient with the symmetric polarization of the top homogeneous part.
5. Prove the disjoint-branch Vandermonde spanning lemma and descend on total degree.
6. Do not claim the integer-exponent class: nonpositive integer Hurwitz values are Bernoulli
   polynomials, and the present Taylor carrier uses a finite-part convention at zeta poles.

## Honest status

The current formalized partition law still assumes augmented rational independence of class
representatives and is not honestly a 90/100 result.  This conjecture is the identified addition
that could change that verdict because it would give a complete nonrational classification rather
than a generic collapse theorem.

## Log

- 2026-07-12 — isolated after the formalized generic-class law passed build, axiom print, and lint
  but remained below the requested 90/100 significance threshold.
