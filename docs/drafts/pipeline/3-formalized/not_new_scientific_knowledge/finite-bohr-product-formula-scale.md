# Finite Bohr product-formula scale

- **ID:** finite-bohr-product-formula-scale
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/completed-base-archimedean-coordinate.md` section 4
- **Statement:** For a finitely supported Bohr character, scaling every prime coordinate by `p^-2`
  multiplies the character by the finite product of the corresponding prime-square scale factors.

## Goal
This banks the finite-support algebra behind the completed-base product-formula statement
`sigma_infty|_R = product_p sigma_p^2` on Bohr characters. It does not formalize the Gamma symbol,
the digamma recurrence, the difference-differential ring `R+`, infinite products, or the full completed
base construction.

## Paper Proof
For a finitely supported exponent vector `m`, the Bohr character is

`e_m(x) = product_p x_p^(m_p)`,

where the product is finite over `support(m)`. If every coordinate is scaled by a factor `c_p`, then

`e_m(c*x) = product_p (c_p*x_p)^(m_p)`.

In a commutative group, powers distribute over products, so

`product_p (c_p*x_p)^(m_p) = product_p c_p^(m_p) * product_p x_p^(m_p)`.

Taking `c_p = p^-2` gives the finite Bohr-character form of applying the simultaneous square of all prime
dilations:

`e_m((p^-2 x_p)_p) = (product_p p^(-2 m_p)) e_m(x)`.

## Gates
- [x] 0 -> 1  in-progress: finite product-formula scaling identity extracted from the completed-base card.
- [x] 1 -> 2  fully-proven: paper proof above by finite support and commutativity.
- [x] 2 -> 3  formalized: Lean definitions/theorems `scaleAllCoordinates`,
  `bohrCharacter_scaleAllCoordinates`, `primeComplexUnit`, `archimedeanSquareScale`, and
  `bohrCharacter_archimedeanSquareScale` in `formal/GaloisForLFunctions/HTGeometry/BohrGenerators.lean`; scratch
  `#check`/`#print axioms`, `lake build`, and `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the finite character certificate for the product-formula action on
  the completed base.

## Log
- 2026-06-19 - Leaner split this exact finite-support scaling theorem from
  `completed-base-archimedean-coordinate` section 4. The parent card remains in `2-fully-proven` because
  the Gamma symbol, digamma recurrence, difference-differential ring `R+`, infinite product interpretation,
  and full completed-base construction are not fully Lean-formalized.
