# Finite-adele character self-duality

- **ID:** `field-one-finite-adele-self-duality`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-finite-adele-weyl-character`
- **Statement:** the standard finite-adele additive character is primitive, and its Weyl
  multiplier action on finite Bruhat functions is faithful.

## Proof

For nonzero \(a\in\mathbb A_f\), choose a place \(v\) with \(a_v\ne0\). Let \(c_v\) be the
standard inverse-prime local principal part and choose the one-place adele
\[
  x_v=a_v^{-1}c_v,\qquad x_w=0\quad(w\ne v).
\]
Then \(ax\) is supported at \(v\) with coordinate \(c_v\), so the shifted standard character is
nontrivial. This proves primitivity and injectivity of \(a\mapsto\psi_f(a\,\cdot)\).

To distinguish the corresponding operators inside \(C_c^{\mathrm{lc}}(\mathbb A_f)\), translate
the characteristic function of \(\prod_v\mathbb Z_v\) to any prescribed test point. Its value
there is one, so equality of Weyl operators implies equality of all shifted character values.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleSelfDuality`
- **Core theorems:** `fieldOneFiniteAdeleStandardAddChar_isPrimitive`,
  `fieldOneFiniteAdeleStandardAddChar_mulShift_injective`,
  `fieldOneFiniteAdeleIntegralBruhatTestAt_self`,
  `fieldOneFiniteAdeleStandardWeylMultiplier_injective`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: local inverse-principal-part witness typed
- [x] 1 → 2: dependency-closed primitivity and test-translation proof
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
