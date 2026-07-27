# Injective tensor product of scalar-valued function spaces

- **ID:** `function-tensor-product`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-semilocal-bruhat-to-l2`
- **Statement:** over a field, the pointwise-product map
  \((X\to K)\otimes_K(Y\to K)\to(X\times Y\to K)\) is injective.

## Proof

Choose a Hamel basis of \(Y\to K\). The standard tensor/basis equivalence writes a tensor uniquely
as a finitely supported family of \(X\to K\) coefficients. If its pointwise product function
vanishes, fixing \(x\in X\) gives a zero finite linear combination of the chosen basis. Basis
uniqueness makes every coefficient vanish at every \(x\), hence the original tensor is zero.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FunctionTensorProduct`
- **Core theorem:** `functionTensorProductHom_injective`
- **Audit:** direct cached `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: pointwise bilinear map typed
- [x] 1 → 2: Hamel-coordinate injectivity proof
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
