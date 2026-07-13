# Finite Bohr-character generator identities

- **ID:** finite-bohr-character-generator-identities
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/archimedean-generator-axis-mode.md`
- **Statement:** For finitely supported integer Bohr characters `e_m(x)=prod_p x_p^{m_p}`, the trivial exponent gives the trivial character, products add exponent vectors, and scaling one coordinate acts diagonally by the corresponding exponent.

## Goal
This banks the finite algebraic skeleton behind the generator-axis-mode card. It does not formalize the analytic `partial_s` operator, infinite torus generator domains, digamma residue, or the C5-localization synthesis.

## Paper Proof
Let `G` be a commutative multiplicative group and let `m : I ->_fin Z`. Define
`e_m(x)=prod_i x_i^{m_i}` over the finite support of `m`.

For `m=0`, the product is empty, so `e_0(x)=1`.

For exponent vectors `m,n`, finite support and commutativity give
`e_{m+n}(x)=prod_i x_i^{m_i+n_i}=prod_i x_i^{m_i} prod_i x_i^{n_i}=e_m(x)e_n(x)`.

For a fixed coordinate `p`, replace `x_p` by `c x_p` and leave all other coordinates unchanged. All factors except the `p`-factor are unchanged, while the `p`-factor becomes
`(c x_p)^{m_p}=c^{m_p} x_p^{m_p}`. Therefore
`e_m(...,c x_p,...)=c^{m_p} e_m(x)`.

## Gates
- [x] 0 -> 1  in-progress: finite Bohr-character identities extracted from the broader generator-axis-mode theorem.
- [x] 1 -> 2  fully-proven: paper proof above, using only finite products in a commutative group.
- [x] 2 -> 3  formalized: Lean theorems `bohrCharacter_zero`, `bohrCharacter_add`, and `bohrCharacter_scaleCoordinate` in `formal/GaloisForLFunctions/HTGeometry/BohrGenerators.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the finite algebraic lemma in the generator-level C5-localization note.

## Log
- 2026-06-19 — Leaner split this exact finite lemma from `archimedean-generator-axis-mode` and created the formalized card. The parent card remains in `2-fully-proven` because the analytic generator and structural C5-localization claims are not fully Lean-formalized.
