# Unit-modulus multipliers on complex L²

- **ID:** `unit-modulus-l2-multiplier`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-spherical-weyl-multiplier-bridge`
- **Statement:** any almost-everywhere strongly measurable complex phase of norm one acts by
  an onto complex-linear isometry on \(L^2\), for any measure.

## Theorem

For a measure \(\mu\) and phase \(\phi\) satisfying
\[
  \phi\ \text{a.e. strongly measurable},\qquad |\phi|=1\quad\mu\text{-a.e.},
\]
pointwise multiplication \(f\mapsto\phi f\) preserves `MemLp`, is linear, preserves the exact
\(L^2\) norm, and is surjective with inverse \(f\mapsto\overline\phi f\).

No invariance, sigma-finiteness, local compactness, or finiteness hypothesis on \(\mu\) is used.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.UnitModulusL2Multiplier`
- **Core definitions/theorems:** `UnitModulusL2Phase`,
  `UnitModulusL2Phase.memLp_mul`, `UnitModulusL2Phase.norm_mulAux`,
  `UnitModulusL2Phase.mulUnitary`, `UnitModulusL2Phase.mulUnitary_ae`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: minimal phase interface typed
- [x] 1 → 2: dependency-closed measure-independent proof
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
