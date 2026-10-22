# Source three-term Hodge purity

- **ID:** `deninger-source-three-term-hodge-purity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Parent:** `deninger-arithmetic-cohomology-construction`
- **Statement:** A positive flow-natural anti-linear Hodge operator on the middle
  cohomology of a source three-term arithmetic complex forces every middle
  Frobenius eigenvalue to have real part \(1/2\); if every nontrivial
  Riemann-zeta zero occurs as such an eigenvalue, RH follows.

## Goal

Separate the formal Hodge-purity implication from every Xi-defined target
cohomology.  The arithmetic complex, cup product, flow, and Hodge operator
below are arbitrary source objects.  The zeta function enters only in the
final one-way spectral comparison.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, attack, falsifiers
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: `DeningerArithmeticThreeTermHodge.eigenvalue_re_eq_half` and the RH
  corollary `riemannHypothesis_of_zetaZero_eigenvector` build unconditionally
- [ ] 3 → 4 publication-ready: standalone theorem and Lean certificate

## Theorem

`[PROVED HERE] [DAC_SOURCE_THREE_TERM_HODGE_PURITY]`

Let
\[
 C^0\xrightarrow{d^0}C^1\xrightarrow{d^1}C^2
\]
be a complex of complex vector spaces.  Let \(\Theta_i\) commute with the
differential and let
\[
 B:H^1(C)\times H^1(C)\longrightarrow\mathbb C
\]
be the cup--trace pairing descended from a chain-level degree-two product.
Assume its flow has weight one:
\[
 B(\Theta x,y)+B(x,\Theta y)=B(x,y).                    \tag{1}
\]
Let
\[
 J:H^1(C)\longrightarrow H^1(C)
\]
be conjugate-linear and satisfy
\[
 J^2=-1,\qquad \Theta J=J\Theta,\qquad
 \operatorname{Re}B(x,Jx)>0\quad(x\ne0).                \tag{2}
\]
Then every nonzero eigenvector
\[
 \Theta x=\lambda x
\]
satisfies
\[
 \operatorname{Re}\lambda=\frac12.                     \tag{3}
\]

Suppose additionally that for every nontrivial zero \(\rho\) of the
completed Riemann zeta function there is a nonzero \(x_\rho\in H^1(C)\) with
\[
 \Theta x_\rho=\rho x_\rho.                             \tag{4}
\]
Then the Riemann hypothesis holds.

The coordinate form used by the existing formal zeta infrastructure is
\[
 \rho=\frac12+i\,z_\rho,\qquad
 z_\rho=(\rho-\tfrac12)(-i).
\]
Thus `(4)` may equivalently be written with eigenvalue
\(\frac12+i z_\rho\).

## Proof

Put \(h(x,y)=B(x,Jy)\).  If \(\Theta x=\lambda x\), conjugate-linearity and
flow-naturality give
\[
 \Theta Jx=J\Theta x=J(\lambda x)=\overline\lambda\,Jx.
\]
Apply `(1)` to \((x,Jx)\):
\[
 \lambda B(x,Jx)+\overline\lambda B(x,Jx)=B(x,Jx).
\]
By `(2)`, \(B(x,Jx)\ne0\), hence
\[
 \lambda+\overline\lambda=1.
\]
Taking real parts proves `(3)`.

For a nontrivial zeta zero \(\rho\), `(4)` and `(3)` give
\(\operatorname{Re}\rho=1/2\).  This is RH.

## Dependency and hostile audit

- The proof uses no divisor-indexed cohomology, Xi quotient, Gamma/CCM
  operator, numerical computation, RH premise, or unproved declaration.
- \(J^2=-1\) and bijectivity are geometric Hodge requirements but are not
  needed for the scalar cancellation itself.  Positivity is used only to
  ensure \(B(x,Jx)\ne0\).
- One-sided inclusion of the nontrivial zeta divisor in the source point
  spectrum is enough for RH.  Equality of spectra, multiplicities,
  regularized determinant identity, and Lefschetz trace formula remain
  separate requirements of Deninger's full program.
- This theorem does not construct \(C^\bullet\), \(B\), \(J\), or the
  spectral comparison.  Those are the open arithmetic-geometric gates.

## Falsifiers

Any of the following breaks the proof:

1. cup--trace has weight other than one;
2. \(J\) intertwines \(\Theta\) with an operator other than \(\Theta\);
3. \(B(x,Jx)=0\) for a nonzero eigenvector;
4. a zeta zero is represented only by generalized spectrum without a
   genuine eigenvector and no approximate-spectrum replacement is proved.

## Log

- 2026-07-26 — dependency-closed paper proof extracted from the generic
  three-term source formalism; Xi-defined quotient removed from hypotheses.

## Unconditional Lean formalization

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticThreeTermHodge.lean`
(namespace `RHTower.DeningerArithmeticThreeTermHodge`), wired into the `RHTower` umbrella.
Axiom audit: `propext, Classical.choice, Quot.sound`.

- `HodgeData H` — the source data of the theorem: a flow `theta`, a cup–trace pairing `cup`, an
  anti-linear `hodge : H →ₗ⋆[ℂ] H`, and the hypotheses `weightOne` `(1)`, `hodgeSq`, `commutes`
  and `positive` `(2)`.  Nothing is constructed; all four are fields.
- `theta_hodge_eigenvector` — conjugate-linearity turns a `λ`-eigenvector into a
  `conj λ`-eigenvector: `Θ (J x) = conj λ • J x`.
- `cup_hodge_ne_zero` — positivity gives `B(x, Jx) ≠ 0`.
- `eigenvalue_re_eq_half` — equation `(3)`: `λ + conj λ = 1`, hence `Re λ = 1/2`.
- `eigenvalue_eq_half_add_I_mul` — the centered coordinate form `λ = 1/2 + i z`.
- `riemannHypothesis_of_zetaZero_eigenvector` — the one-way comparison `(4)`: realizing every
  nontrivial zeta zero as an eigenvalue of `theta` yields mathlib's `RiemannHypothesis`.

`hodgeSq` is carried as a field but, as the card's audit notes, the scalar cancellation does not
use it; only `commutes`, `weightOne` and `positive` enter the proof.
