# Exact all-order pole-jet law for the Gamma factorial microscope

- **ID:** `gamma-factorial-all-order-pole-jet-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVEN IN LEAN] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every finite polygamma order of the Gamma factorial pole germ splits exactly into
  its reciprocal principal jet, a local polygamma value at `1+sₙx`, and a shifted generalized
  harmonic sum.

## Goal

Replace order-by-order residue calculations by one exact source law.  The theorem identifies the
complete finite-jet input for the harmonic-zeta filtration and makes the parity cancellation
mechanism explicit at every order.

## Theorem

Let `sₙ=(-1)^(n+1)/n!`, let `m,n∈ℕ`, and assume `sₙx` is not an integer.  With

\[
 H_{n,p}(z)=\sum_{j=1}^n(j-z)^{-p},
\]

Lean proves

\[
 \psi^{(m)}(-n+z)=
 \psi^{(m)}(1+z)
 +\frac{(-1)^{m+1}m!}{z^{m+1}}
 +m!H_{n,m+1}(z).
\]

Consequently,

\[
 s_n^{m+1}\psi^{(m)}(-n+s_nx)=
 \frac{(-1)^{m+1}m!}{x^{m+1}}
 +s_n^{m+1}\left(
   \psi^{(m)}(1+s_nx)+m!H_{n,m+1}(s_nx)\right).
\]

The first term is exactly the `(m+1)`-st reciprocal principal jet.

## Meaning

At `z=0`, the local value is
`ψ⁽ᵐ⁾(1)=(-1)^(m+1)m!ζ(m+1)`, while the shifted sum tends `m!ζ(m+1)`.  Therefore:

- odd polygamma orders reinforce and produce `2m!ζ(m+1)`;
- even polygamma orders cancel at the bounded zeta layer and expose the finite Euler-product tail.

This parity law is the exact all-order source of the bifiltration discovered by the third-jet
exponential-envelope escape.

## Lean certificate

Module: `formal/GaloisForLFunctions/HTGeometry/GammaFactorialAllOrderPoleJet.lean`.

Headline declarations:

- `iteratedDeriv_digamma_neg_nat_add_of_ne_int`
- `gammaFactorialScaledPolygamma_eq_principal_add`

Direct compilation and the individual Lake target pass.  Axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.  Formal lint passes.  No full build and no numerical
computation were used.

## Gates

- [x] 0 → 1 in-progress: exact all-order source identity isolated
- [x] 1 → 2 fully-proven: induction on pole depth complete for arbitrary jet order
- [x] 2 → 3 formalized: general Lean theorem, targeted build and axiom audit pass
- [ ] 3 → 4 publication-ready: incorporate into standalone pole-germ paper and priority audit

## Approach

Iterate the differentiated digamma shift law across the negative-integer pole ladder.  Reversing
each denominator `-j+z=-(j-z)` cancels the polygamma sign and leaves the uniform positive
coefficient `m!` on the shifted generalized harmonic sum.  Multiplication by `sₙ^(m+1)` extracts
the reciprocal principal part exactly.

## Log

- 2026-07-15 — proved and formalized after the `ζ(2)` envelope escape revealed the all-order
  parity structure.
