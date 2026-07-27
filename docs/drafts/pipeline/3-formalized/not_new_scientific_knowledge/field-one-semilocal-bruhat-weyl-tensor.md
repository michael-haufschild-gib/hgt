# Semilocal Bruhat--Schwartz Weyl tensor

- **ID:** `field-one-semilocal-bruhat-weyl-tensor`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-spherical-weyl-multiplier-bridge`
- **Statement:** the normalized real and standard finite-adele Weyl multipliers combine on
  \(\mathcal S(\mathbb R)\otimes_{\mathbb C}C_c^{\mathrm{lc}}(\mathbb A_f)\) into an
  additive family of algebraic automorphisms, with a canonical rational diagonal
  specialization.

## Theorem

For \(a=(a_\infty,a_f)\in\mathbb R\times\mathbb A_f\), define
\[
  W_a =
  W^{\infty}_{2\pi a_\infty}\otimes W^f_{a_f}.
\]
Then
\[
  W_a(f\otimes g)=W^\infty_{2\pi a_\infty}f\otimes W^f_{a_f}g,\qquad
  W_aW_b=W_{a+b},\qquad W_0=1,\qquad W_a^{-1}=W_{-a}.
\]
The diagonal map \(q\mapsto(q,\Delta_fq)\) is additive and injective, and its multiplier
specialization satisfies the same additive law.

## Boundary

This is an algebraic tensor product. No LF topology, completed tensor product, Haar measure,
Hilbert completion, trace formula, positivity, zero spectrum, or RH premise occurs.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatWeylTensor`
- **Core theorems:** `fieldOneSemilocalBruhatWeylMultiplier_tmul`,
  `fieldOneSemilocalBruhatWeylMultiplier_add`,
  `fieldOneSemilocalBruhatWeylMultiplier_zero`,
  `fieldOneSemilocalBruhatWeylMultiplier_neg_left`,
  `fieldOneSemilocalBruhatWeylLinearEquiv`,
  `fieldOneRationalDiagonalBruhatWeylMultiplier_add`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: algebraic carrier and normalization typed
- [x] 1 → 2: dependency-closed tensor proof
- [x] 2 → 3: unconditional Lean theorem, direct leaf check, and axiom audit
- [ ] 3 → 4: publication-ready integration
