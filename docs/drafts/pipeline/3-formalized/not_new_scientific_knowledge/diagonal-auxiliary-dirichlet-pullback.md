# Diagonal auxiliary Dirichlet pullback

- **ID:** diagonal-auxiliary-dirichlet-pullback
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `friable-dirichlet-auxiliary.md` §1
- **Statement:** A finite monomial in prime Bohr coordinates `x_p=p^{-s}` pulls back on the diagonal to the Dirichlet frequency `n_m^{-s}`, and a finite auxiliary form pulls back termwise to a finite Dirichlet polynomial.

## Goal
This banks the exact algebraic pullback that identifies finite multi-`q` Bohr-coordinate auxiliaries with finite Dirichlet polynomials. It does not formalize analytic estimates, Siegel lemmas, or obstruction-C lower bounds.

## Paper Proof
For a finite exponent vector `m`, substitute `x_p=p^{-s}` in the monomial `prod_p x_p^{m_p}`. This gives
`prod_p (p^{-s})^{m_p}`. Since only finitely many exponents are nonzero, this is
`(prod_p p^{m_p})^{-s}=n_m^{-s}` by the finite product power law for nonzero prime bases. Linearity then
gives the same identity term by term for any finitely supported auxiliary form.

## Gates
- [x] 0 -> 1  in-progress: exact finite diagonal-pullback statement extracted from the friable auxiliary object.
- [x] 1 -> 2  fully-proven: paper proof above, using finite products and complex-power identities.
- [x] 2 -> 3  formalized: Lean theorems `diagonalMonomial_eq_frequency` and `diagonalAuxiliaryForm_eq_dirichletPolynomial` in `formal/GaloisForLFunctions/RHTower/SmoothNumbers.lean`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the formal diagonal-pullback certificate for the auxiliary-space note.

## Log
- 2026-06-19 — Leaner split this exact diagonal-pullback lemma from `friable-dirichlet-auxiliary`. The parent card remains in `2-fully-proven` because its zero-estimate/PNT bookkeeping and obstruction-C reduction are not fully Lean-formalized.

