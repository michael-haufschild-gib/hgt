# Finite elementary-symmetric algebraic independence

- **ID:** finite-esymm-algebraic-independence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../3-formalized/lean-claim-review-row-058-finite-layers-kappa-esymm.md` Layer 2
- **Statement:** For `n` indeterminate spectral points, the elementary symmetric polynomials
  `e_1, ..., e_n` in `MvPolynomial (Fin n) Q` are algebraically independent over `Q`.

## Goal
This banks the formal finite DSS-face shadow from row #58. It proves algebraic independence of the generic
elementary-symmetric polynomial coordinates only. It does not assert arithmetic algebraic independence of
elementary symmetric functions evaluated at actual zeta zeros, and it does not combine with the carrier
`kappa_-` theorem into an A1/A2 unification theorem.

## Paper Proof
Let `R = Q[X_i : i in Fin n]`. The fundamental theorem of symmetric polynomials gives an injective algebra
map from the polynomial algebra in `n` formal elementary-symmetric coordinates into the symmetric subalgebra
of `R`, sending the `i`-th coordinate to `e_i`. Composing this injective map with the inclusion of the
symmetric subalgebra into `R` is exactly the evaluation homomorphism
`aeval (fun i : Fin n => esymm (Fin n) Q (i+1))`.

Since this evaluation homomorphism is injective, the family `e_1, ..., e_n` is algebraically independent over
`Q`.

## Gates
- [x] 0 -> 1 in-progress: split from row #58 after Professor's audit identified the esymm layer as a separate
  formal finite DSS-face foothold.
- [x] 1 -> 2 fully-proven: paper proof above, using the fundamental theorem of symmetric polynomials.
- [x] 2 -> 3 formalized: Lean theorem `spectrum_esymm_algIndep` in
  `formal/GaloisForLFunctions/SpectrumGenericity.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4 publication-ready: cite as the finite genericity lemma, not as arithmetic DSS.

## Log
- 2026-06-19 — Leaner split this exact theorem from row #58 and certified it against
  `GaloisForLFunctions.spectrum_esymm_algIndep`. Row #58 remains only a split/audit certificate: the
  `kappa_-` layer is separately banked in
  `lean-claim-review-row-032-kappa-minus-offline-pairs.md`, and no combined A1/A2 theorem is asserted.
