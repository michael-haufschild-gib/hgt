# Algebraic independence of the normalized inverse-Gamma pole branches

- **ID:** `gamma-inverse-pole-branch-coefficient-freeness`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Scientific status:** `[PROVED ON PAPER] [LEAN IN PROGRESS] [NOVELTY UNVERIFIED]`
- **Statement:** Let

  \[
    s_n=\frac{(-1)^{n+1}}{n!},\qquad
    \Gamma(-n+s_nX)=-\frac{U_n(X)}X,\qquad U_n(0)=1,
  \]

  and let `B_n(T)=T+\sum_{j\ge0}b_{n,j}T^{j+2}` be the unique normalized formal branch
  satisfying

  \[
    \Gamma(-n+s_nB_n(T))=-\frac1T.
  \]

  Then the countable family of pole-index germs `n ↦ b_{n,j}`, `j∈ℕ`, is algebraically
  independent over `ℂ`.

## Goal

Replace the non-injective direct Laurent microscope for outer Gamma composition by an invertible
local coordinate at every pole.  The inverse branches retain every coefficient of the exact Gamma
pole deformation and provide the proposed coordinate system for all-order composition-depth
descent.

## Direct route no-go and positive replacement

The tempting expression `Gamma(Gamma(-n+s_nX))` has no Laurent germ at `X=0`: its inner argument
tends to infinity through a reciprocal pole coordinate, and the outer Gamma encounters an
accumulating singular geometry.  Consequently, the already proved coefficient freeness of
`U_n` cannot be pushed through outer composition by an ordinary Laurent-series substitution.

The positive replacement is to invert the pole coordinate before composing.  Put

\[
  A_n(X)=\frac{X}{U_n(X)}.
\]

Then `A_n` is tangent to the identity and `B_n=A_n^{\langle-1\rangle}`.  Equivalently,

\[
  B_n(T)=T\,U_n(B_n(T)),
\]

which is division-free and uniquely characterizes the branch.  The exact Gamma source identity
then gives the displayed inverse-branch equation.

## Paper proof

The positive Taylor coefficients of `U_n` are the negatives of the already formalized regular
Laurent coefficients of `Gamma(-n+s_nX)`.  Those coefficient germs are countably algebraically
independent.

Two universal coefficient transformations are involutions:

1. `1+Σa_jT^(j+1) ↦ (1+Σa_jT^(j+1))⁻¹`;
2. `T+Σc_jT^(j+2) ↦ (T+Σc_jT^(j+2))^{⟨-1⟩}`.

Each induces an injective endomorphism of the polynomial algebra in countably many universal
coefficients.  Algebraic independence therefore survives both transformations.  Applying first
multiplicative inversion to `U_n`, and then compositional inversion to `X/U_n(X)`, proves the
statement.

## Significance

Published inverse-Gamma work constructs branches, integral representations, numerical methods,
and low-order pole expansions.  This theorem instead identifies the complete family of normalized
branches as a free countable algebraic coordinate system.  If the inverse-coordinate chain rule
makes Gamma composition-depth descent injective at every finite jet order, it supplies the missing
mechanism for joint differential algebraic independence of all positive Gamma iterates.

The theorem is not promoted as novel until a specialist priority audit checks inverse special
functions, differential algebra, iteration theory, and formal-series coefficient automorphisms.

## Gates

- [x] 0 → 1 in-progress: exact source identity, positive theorem, direct-route falsifier, and
  proof mechanism isolated
- [ ] 1 → 2 fully-proven: analytic/formal branch identification written without an open lemma
- [ ] 2 → 3 formalized: production Lean modules, direct checks, lint, and axiom audit pass
- [ ] 3 → 4 publication-ready: specialist priority audit and standalone exposition complete

